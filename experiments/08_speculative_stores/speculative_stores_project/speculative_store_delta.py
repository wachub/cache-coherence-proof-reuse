#!/usr/bin/env python3
"""Incremental bounded speculative-store verification atop 4-core 2-line MSI+SC.

Speculation is PRIVATE: two optional queue entries per core; staging, confirmation,
abort and queue management do not access caches or memory. After confirmation,
the oldest entry may issue the original ordinary store command. The original
MSI machine subsequently completes that command atomically in program order.

This models a tiny speculative *store queue*, not speculative externally-visible
writes, speculative CAS, or full branch prediction. See README for proof scope.
"""
import os, json, time, argparse
from sc_msi_4core_verifier import System, a, o, neg, eq, ge, le, z3_smt

class SpecStore(System):
    def __init__(self, cores=4, lines=2):
        super().__init__(cores=cores, lines=lines)
        self.old_keys = tuple(self.keys)
        for c in range(cores):
            for field,ty in [('qlen','Int'),('ready','Int'),
                             ('addr0','Int'),('value0','Int'),
                             ('addr1','Int'),('value1','Int')]:
                k=f'sq_{field}_{c}'
                self.keys.append(k)
                self.types[k]=ty

    def q(self,c,field,nxt=False):
        return self.v(f'sq_{field}_{c}',nxt)

    def q_inv(self,nxt=False):
        terms=[]
        for c in range(self.n):
            q=self.q(c,'qlen',nxt);r=self.q(c,'ready',nxt)
            terms += [ge(q,'0'),le(q,'2'),ge(r,'0'),le(r,q)]
            for j in (0,1):
                terms.append(f'(=> (> {q} {j}) (and (<= 0 {self.q(c,f"addr{j}",nxt)}) (< {self.q(c,f"addr{j}",nxt)} {self.k})))')
        return a(*terms)

    def init(self):
        return a(super().init(),*(eq(self.q(c,f), '0') for c in range(self.n)
                                     for f in ('qlen','ready','addr0','addr1','value0','value1')))

    def inherited_steps(self):
        # Original MSI actions still operate identically; old frontend may not
        # issue a new instruction while younger queued speculative stores exist.
        out=[]
        for label,formula in super().steps():
            if label.startswith('core') and ':issue_' in label:
                c=int(label.split(':')[0][4:])
                formula=a(formula,eq(self.q(c,'qlen'),'0'))
            out.append((label,formula))
        return out

    def delta_steps(self,unsafe_second_first=False, unsafe_unresolved=False):
        out=[]
        for c in range(self.n):
            q=self.q(c,'qlen');r=self.q(c,'ready')
            haddr=self.q(c,'addr0');hval=self.q(c,'value0')
            taddr=self.q(c,'addr1');tval=self.q(c,'value1')
            busy=self.cpu(c,'busy')
            # The next TWO stores may be speculatively staged even while an
            # older architectural instruction is still incomplete.
            for l in range(self.k):
                # New write value is a free SMT input (an arbitrary integer).
                inp=self.q(c,'value0',True)
                out.append(self.step(f'core{c}:stage_slot0_line{l}',eq(q,'0'),
                     {f'sq_qlen_{c}':'1',f'sq_addr0_{c}':str(l),
                      f'sq_value0_{c}':inp}))
                inp=self.q(c,'value1',True)
                out.append(self.step(f'core{c}:stage_slot1_line{l}',eq(q,'1'),
                     {f'sq_qlen_{c}':'2',f'sq_addr1_{c}':str(l),
                      f'sq_value1_{c}':inp}))
            # Resolve speculation successfully: a prefix of outstanding writes
            # is now correct-path and eligible for retirement.
            out.append(self.step(f'core{c}:confirm',f'(< {r} {q})',
                     {f'sq_ready_{c}':q}))
            # A branch misprediction discards only the unconfirmed suffix.
            # Confirmed entries must still commit in order.
            out.append(self.step(f'core{c}:squash_unconfirmed',f'(> {q} {r})',
                     {f'sq_qlen_{c}':r}))
            # Start an ordinary MSI store, once the preceding architectural
            # instruction is complete. The store becomes visible only on the
            # OLD complete_store transition, not here.
            for l in range(self.k):
                guard=a(neg(busy),f'(> {r} 0)',eq(haddr,str(l)))
                patch={f'busy_{c}':'true',f'op_{c}':'2',f'target_{c}':str(l),
                       f'newval_{c}':hval,
                       f'sq_qlen_{c}':f'(- {q} 1)',f'sq_ready_{c}':f'(- {r} 1)',
                       f'sq_addr0_{c}':f'(ite (= {q} 2) {taddr} 0)',
                       f'sq_value0_{c}':f'(ite (= {q} 2) {tval} 0)'}
                out.append(self.step(f'core{c}:retire_head_line{l}',guard,patch))
                if unsafe_unresolved:
                    # Wrong-path write is issued even though it is not resolved.
                    guard2=a(neg(busy),f'(> {q} 0)',eq(r,'0'),eq(haddr,str(l)))
                    out.append(self.step(f'core{c}:BUG_retire_unresolved_line{l}',guard2,dict(patch, **{f'sq_ready_{c}':'0'})))
                if unsafe_second_first:
                    # Wrong: younger confirmed store overtakes older store.
                    guard3=a(neg(busy),eq(q,'2'),eq(r,'2'),eq(taddr,str(l)))
                    patch3={f'busy_{c}':'true',f'op_{c}':'2',f'target_{c}':str(l),
                            f'newval_{c}':tval,f'sq_qlen_{c}':'1',f'sq_ready_{c}':'1'}
                    out.append(self.step(f'core{c}:BUG_retire_tail_first_line{l}',guard3,patch3))
        return out

    def old_stutters(self):
        return a(*(eq(self.v(k,True),self.v(k)) for k in self.old_keys))

    def legal_queue_retirement_projection(self):
        """Local memory-ordering contract: only confirmed HEAD can enter MSI.

        Staging/squashing/confirmation must stutter on the OLD state. The
        only other legal new behavior is exactly issuing the confirmed head
        as an OLD store instruction while no older instruction is active.
        """
        out=[self.old_stutters()]
        for c in range(self.n):
            for l in range(self.k):
                haddr=self.q(c,'addr0');hval=self.q(c,'value0')
                original={f'busy_{c}':'true',f'op_{c}':'2',
                          f'target_{c}':str(l),f'newval_{c}':hval}
                out.append(a(neg(self.cpu(c,'busy')),
                             f'(> {self.q(c,"ready")} 0)',eq(haddr,str(l)),
                             *(eq(self.v(k,True),original.get(k,self.v(k)))
                               for k in self.old_keys)))
        return o(*out)

    def steps(self):
        return self.inherited_steps()+self.delta_steps()

    def proof(self,out_dir):
        os.makedirs(out_dir,exist_ok=True)
        oldinv=super().inv(); oldnext=super().inv(True)
        qinv=self.q_inv(); qnext=self.q_inv(True)
        delta=o(*(f for _,f in self.delta_steps()))
        projected=self.legal_queue_retirement_projection()
        goals={
            'initial_queues': a(self.init(),neg(qinv)),
            'new_transitions_preserve_queue_invariants':a(oldinv,qinv,delta,neg(qnext)),
            'new_transitions_obey_program_order':a(oldinv,qinv,delta,neg(projected)),
            'new_transitions_preserve_old_invariant':a(oldinv,qinv,delta,neg(oldnext)),
        }
        ans={}
        for name,body in goals.items():
            script=self.declarations()+'\n(assert '+body+')\n(check-sat)\n'
            path=os.path.join(out_dir,name+'.smt2')
            with open(path,'w') as f:f.write(script)
            t=time.monotonic(); out=z3_smt(script)
            val=out.strip().splitlines()[0] if out.strip() else 'error'
            ans[name]={'result':val,'seconds':round(time.monotonic()-t,3),'file':os.path.basename(path), 'bytes':len(script)}
            if val!='unsat':ans[name]['detail']=out[:1000]
        report={'cores':self.n,'lines':self.k,'max_speculative_stores_per_core':2,
                'old_MSI_SC_lemma':'reused: baseline inductive MSI invariants; SC follows from atomic completions in program order (trace theorem not separately mechanized)',
                'new_transitions':len(self.delta_steps()),
                'results':ans,'success':all(x['result']=='unsat' for x in ans.values())}
        with open(os.path.join(out_dir,'results.json'),'w') as f:json.dump(report,f,indent=2)
        return report

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--cores',type=int,default=4)
    ap.add_argument('--lines',type=int,default=2)
    ap.add_argument('--out-dir',default='/mnt/data/speculative_stores_project/smt')
    ar=ap.parse_args();print(json.dumps(SpecStore(ar.cores,ar.lines).proof(ar.out_dir),indent=2))
