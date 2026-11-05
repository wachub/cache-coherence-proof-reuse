#!/usr/bin/env python3
"""Incrementally verified four-core MSI + speculative STORE and LOAD interaction.

Fixed abstract model: up to 2 private speculative writes and one younger
speculative read per core. One older architectural instruction may be in flight.
The cache/network transitions are inherited unchanged from the MSI model.

This verifier checks the NEW transition cases and an explicit interface contract;
it is conditional on a previously checked inductive MSI invariant.
Requires libz3.so.4 via the baseline ctypes SMT-LIB adapter.
"""
import argparse, json, os, time
from sc_msi_4core_verifier import System, a, o, neg, eq, imp, ge, le, z3_smt

class CombinedSpec(System):
    def __init__(self, cores=4, lines=2):
        super().__init__(cores=cores, lines=lines)
        self.old_keys=tuple(self.keys)
        fields=[('qlen','Int'),('ready','Int'),('addr0','Int'),('value0','Int'),
                ('addr1','Int'),('value1','Int'),
                ('load_active','Bool'),('load_confirmed','Bool'),
                ('load_addr','Int'),('load_kind','Int'),
                ('load_version','Int'),('load_value','Int')]
        for c in range(cores):
            for field, typ in fields:
                key=f'spec_{field}_{c}'
                self.keys.append(key)
                self.types[key]=typ
        self.new_keys=tuple(k for k in self.keys if k not in self.old_keys)

    def x(self,c,k,nxt=False): return self.v(f'spec_{k}_{c}',nxt)

    def new_inv(self,nxt=False):
        t=[]
        for c in range(self.n):
            q=self.x(c,'qlen',nxt);r=self.x(c,'ready',nxt)
            act=self.x(c,'load_active',nxt);conf=self.x(c,'load_confirmed',nxt)
            ka=self.x(c,'load_kind',nxt);addr=self.x(c,'load_addr',nxt)
            t.extend([ge(q,'0'),le(q,'2'),ge(r,'0'),le(r,q),
                      ge(addr,'0'),le(addr,str(self.k-1)),
                      o(eq(ka,'0'),eq(ka,'1')),
                      ge(self.x(c,'load_version',nxt),'0'),
                      imp(conf,act)])
            # A cached speculative load preserves its captured data payload.
            # This relational ghost invariant is essential: validity of a
            # version token alone says nothing about an unconstrained result.
            for l in range(self.k):
                t.append(imp(a(act,eq(ka,'0'),eq(addr,str(l))),
                    eq(self.x(c,'load_value',nxt),
                       f'(select payload_{l} {self.x(c,"load_version",nxt)})')))
            for j in (0,1):
                t.append(imp(f'(> {q} {j})',a(ge(self.x(c,f'addr{j}',nxt),'0'),
                                               le(self.x(c,f'addr{j}',nxt),str(self.k-1)))))
        return a(*t)

    def init(self):
        t=[super().init()]
        for c in range(self.n):
            for f in ('qlen','ready','addr0','value0','addr1','value1',
                      'load_addr','load_kind','load_version','load_value'):
                t.append(eq(self.x(c,f),'0'))
            for f in ('load_active','load_confirmed'):
                t.append(eq(self.x(c,f),'false'))
        return a(*t)

    def inherited_steps(self):
        out=[]
        for label,formula in super().steps():
            if label.startswith('core') and ':issue_' in label:
                c=int(label.split(':')[0][4:])
                formula=a(formula,eq(self.x(c,'qlen'),'0'),neg(self.x(c,'load_active')))
            out.append((label,formula))
        return out

    def delta_steps(self, mutant=None):
        steps=[]
        for c in range(self.n):
            q=self.x(c,'qlen');r=self.x(c,'ready')
            act=self.x(c,'load_active');conf=self.x(c,'load_confirmed')
            busy=self.cpu(c,'busy');la=self.x(c,'load_addr')
            kind=self.x(c,'load_kind');vers=self.x(c,'load_version')
            sval=self.x(c,'load_value');ha=self.x(c,'addr0');hv=self.x(c,'value0')
            ta=self.x(c,'addr1');tv=self.x(c,'value1')
            # Store staging is never allowed after the younger speculative read:
            # that would reverse the program's known instruction sequence.
            for l in range(self.k):
                steps.append(self.step(f'core{c}:stage0_line{l}',a(eq(q,'0'),neg(act)),{
                    f'spec_qlen_{c}':'1',f'spec_addr0_{c}':str(l),
                    f'spec_value0_{c}':self.x(c,'value0',True)}))
                steps.append(self.step(f'core{c}:stage1_line{l}',a(eq(q,'1'),neg(act)),{
                    f'spec_qlen_{c}':'2',f'spec_addr1_{c}':str(l),
                    f'spec_value1_{c}':self.x(c,'value1',True)}))
            # Confirm the entire outstanding write prefix and the younger read.
            steps.append(self.step(f'core{c}:confirm',o(f'(< {r} {q})',a(act,neg(conf))),{
                f'spec_ready_{c}':q,f'spec_load_confirmed_{c}':act}))
            # Wrong-path resolution discards the unconfirmed suffix and its
            # younger speculative read; confirmed writes are not rolled back.
            steps.append(self.step(f'core{c}:squash_suffix',f'(> {q} {r})',{
                f'spec_qlen_{c}':r,
                f'spec_load_active_{c}':'false',f'spec_load_confirmed_{c}':'false'}))
            steps.append(self.step(f'core{c}:squash_read',a(act,neg(conf)),{
                f'spec_load_active_{c}':'false',f'spec_load_confirmed_{c}':'false'}))
            # The oldest confirmed store is the only one allowed into MSI.
            for l in range(self.k):
                steps.append(self.step(f'core{c}:issue_confirmed_store_line{l}',
                    a(neg(busy),f'(> {r} 0)',eq(ha,str(l))),{
                    f'busy_{c}':'true',f'op_{c}':'2',f'target_{c}':str(l),f'newval_{c}':hv,
                    f'spec_qlen_{c}':f'(- {q} 1)',f'spec_ready_{c}':f'(- {r} 1)',
                    f'spec_addr0_{c}':f'(ite (= {q} 2) {ta} 0)',
                    f'spec_value0_{c}':f'(ite (= {q} 2) {tv} 0)'}))
            # Speculative read of the YOUNGEST earlier buffered store if present.
            # When no earlier same-line store exists, speculate from L1 only.
            can_spec=a(neg(act),o(f'(> {q} 0)',busy))
            for l in range(self.k):
                same0=a(f'(>= {q} 1)',eq(ha,str(l)))
                same1=a(eq(q,'2'),eq(ta,str(l)))
                for j,val,guard in [(0,hv,a(same0,neg(same1))),
                                    (1,tv,same1)]:
                    steps.append(self.step(f'core{c}:spec_forward_slot{j}_line{l}',
                        a(can_spec,guard),{
                        f'spec_load_active_{c}':'true',
                        f'spec_load_confirmed_{c}':'false',
                        f'spec_load_addr_{c}':str(l),f'spec_load_kind_{c}':'1',
                        f'spec_load_value_{c}':val,f'spec_load_version_{c}':'0'}))
                mode=self.pl(l,'mode',c);pending=self.pl(l,'pending',c)
                valid=a(o(eq(mode,'1'),eq(mode,'2')),neg(pending))
                cv=self.pl(l,'val',c)
                steps.append(self.step(f'core{c}:spec_cache_line{l}',
                    a(can_spec,neg(same0),neg(same1),valid),{
                    f'spec_load_active_{c}':'true',
                    f'spec_load_confirmed_{c}':'false',
                    f'spec_load_addr_{c}':str(l),f'spec_load_kind_{c}':'0',
                    f'spec_load_version_{c}':cv,
                    f'spec_load_value_{c}':f'(select payload_{l} {cv})'}))
                # Safe retirement: all earlier stores have LEFT queue, AND the
                # older in-flight MSI instruction has FINISHED. Cache must be
                # still coherent. Read originally from cache requires same
                # version; forwarded read requires same current data value.
                valid_now=a(valid,eq(la,str(l)))
                fresh_cache=a(eq(kind,'0'),eq(cv,vers))
                fresh_forward=a(eq(kind,'1'),eq(f'(select payload_{l} {cv})',sval))
                fresh=a(valid_now,o(fresh_cache,fresh_forward))
                head_done=a(act,conf,eq(q,'0'),neg(busy),eq(la,str(l)))
                fast_guard=a(head_done,fresh)
                if mutant=='unvalidated_read':
                    fast_guard=head_done
                if mutant=='premature_read':
                    fast_guard=a(act,conf,eq(la,str(l)),fresh)
                steps.append(self.step(f'core{c}:spec_retire_fast_line{l}',fast_guard,{
                    f'spec_load_active_{c}':'false',
                    f'spec_load_confirmed_{c}':'false',
                    f'observed_{c}':sval}))
                if mutant is None:
                    # On stale/inaccessible line, issue the original MSI read
                    # instead of returning an unvalidated speculative value.
                    steps.append(self.step(f'core{c}:spec_replay_line{l}',
                        a(head_done,neg(fresh)),{
                        f'spec_load_active_{c}':'false',
                        f'spec_load_confirmed_{c}':'false',
                        f'busy_{c}':'true',f'op_{c}':'1',f'target_{c}':str(l)}))
        return steps

    def steps(self):
        return self.inherited_steps()+self.delta_steps()

    def _old_stutter(self):
        return a(*(eq(self.v(k,True),self.v(k)) for k in self.old_keys))

    def _old_patch(self,changes):
        return a(*(eq(self.v(k,True),changes.get(k,self.v(k))) for k in self.old_keys))

    def interface_contract(self):
        """Every new transition must project to a legal architectural event.
        Fast speculative loads are linearized as correct-value abstract reads.
        """
        allowed=[self._old_stutter()]
        for c in range(self.n):
            busy=self.cpu(c,'busy');q=self.x(c,'qlen');r=self.x(c,'ready')
            act=self.x(c,'load_active');conf=self.x(c,'load_confirmed')
            for l in range(self.k):
                allowed.append(a(neg(busy),f'(> {r} 0)',eq(self.x(c,'addr0'),str(l)),
                    self._old_patch({f'busy_{c}':'true',f'op_{c}':'2',
                        f'target_{c}':str(l),f'newval_{c}':self.x(c,'value0')})))
                allowed.append(a(neg(busy),eq(q,'0'),act,conf,eq(self.x(c,'load_addr'),str(l)),
                    self._old_patch({f'observed_{c}':self.x(c,'load_value')}),
                    eq(self.x(c,'load_value'),f'(select payload_{l} {self.v(f"ref_{l}")})')))
                allowed.append(a(neg(busy),eq(q,'0'),act,conf,eq(self.x(c,'load_addr'),str(l)),
                    self._old_patch({f'busy_{c}':'true',f'op_{c}':'1',f'target_{c}':str(l)})))
        return o(*allowed)

    def _retire_steps(self,mutant=None):
        return [(lab,st) for lab,st in self.delta_steps(mutant=mutant)
                if ':spec_retire_fast_' in lab]

    def _forward_steps(self):
        return [(lab,st) for lab,st in self.delta_steps()
                if ':spec_forward_slot' in lab]

    def _expected_read_value(self,c,l):
        return f'(select payload_{l} {self.v(f"ref_{l}")})'

    def proof_goals(self):
        """Pure named delta obligations: no solver calls or output side effects.

        Keeping generation separate lets the fast harness share declarations,
        cache exact formulas, and localize failing transition schemas.
        """
        oldinv=super().inv();qinv=self.new_inv()
        deltasteps=self.delta_steps()
        delta=o(*(s for _,s in deltasteps))
        fast_events={(c,l):s for c in range(self.n) for l in range(self.k)
            for lab,s in self._retire_steps()
            if lab==f'core{c}:spec_retire_fast_line{l}'}
        forwarding_events=[]
        for lab,st in self._forward_steps():
            c=int(lab.split(':')[0][4:]);j=int(lab.split('slot',1)[1][0]);l=int(lab.rsplit('line',1)[1])
            expected=self.x(c,f'value{j}')
            bug=neg(eq(self.x(c,'load_value',True),expected))
            if j==0:  # an earlier slot cannot overtake a newer matching write
                bug=o(bug,a(eq(self.x(c,'qlen'),'2'),eq(self.x(c,'addr1'),str(l))))
            forwarding_events.append(a(st,bug))
        goals={
            'new_invariant_initial':a(self.init(),neg(qinv)),
            'new_transition_preserves_new_invariant':a(oldinv,qinv,delta,neg(self.new_inv(True))),
            'new_transition_preserves_MSI_invariant':a(oldinv,qinv,delta,neg(super().inv(True))),
            'new_transition_obeys_interface':a(oldinv,qinv,delta,neg(self.interface_contract())),
            'fast_read_returns_current_value':a(oldinv,qinv,
                o(*(a(st,neg(eq(self.cpu(c,'observed',True),
                                  self._expected_read_value(c,l))))
                    for (c,l),st in fast_events.items()))),
            'forwarding_uses_youngest_prior_store':a(oldinv,qinv,o(*forwarding_events)),
            'fast_read_not_before_prior_memory_ops':a(oldinv,qinv,
                o(*(a(st,o(self.cpu(c,'busy'),neg(eq(self.x(c,'qlen'),'0')),
                             neg(self.x(c,'load_confirmed'))))
                    for (c,l),st in fast_events.items())))
        }
        return goals

    def proof(self,out_dir,include_init=True):
        os.makedirs(out_dir,exist_ok=True)
        goals=self.proof_goals()
        deltasteps=self.delta_steps()
        results={}
        for label,goal in goals.items():
            text=self.declarations()+ '\n(assert '+goal+')\n(check-sat)\n'
            with open(os.path.join(out_dir,label+'.smt2'),'w') as f:f.write(text)
            start=time.monotonic();answer=z3_smt(text)
            r=answer.strip().splitlines()[0] if answer.strip() else 'ERROR'
            results[label]={'result':r,'seconds':round(time.monotonic()-start,3),
                            'smt_bytes':len(text),'smt_file':label+'.smt2'}
            if r!='unsat':results[label]['detail']=answer[:1000]
        summary={'cores':self.n,'cache_lines':self.k,'max_spec_stores_per_core':2,
                 'max_spec_reads_per_core':1,
                 'new_transition_schemas':len(deltasteps),
                 'inherited_proof':'requires old four-core MSI invariant and its induction result',
                 'checks':results,
                 'passed':all(d['result']=='unsat' for d in results.values())}
        with open(os.path.join(out_dir,'results.json'),'w') as f:json.dump(summary,f,indent=2)
        return summary

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--cores',type=int,default=4)
    ap.add_argument('--lines',type=int,default=2)
    ap.add_argument('--output-dir',default='/mnt/data/combined_speculative_smt')
    x=ap.parse_args()
    print(json.dumps(CombinedSpec(x.cores,x.lines).proof(x.output_dir),indent=2))
