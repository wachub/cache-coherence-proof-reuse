#!/usr/bin/env python3
"""Incremental, SMT-checked extension of the existing four-core MSI/SC model.

Only one speculative load is permitted per core, and only while an older
memory command is outstanding. A speculative read captures a data version from
an *already valid* cache line, but it has no architectural effect.

After the older command completes, speculative data may retire only if the
line is still valid and contains the *same version* at retirement. Otherwise,
the speculative result is discarded and the load is reissued through the
original nonspeculative interface.

Proof reuse:
  (1) all old transitions (possibly with an added issue guard) preserve the
      original invariant by the OLD proof, which we do not regenerate;
  (2) all old transitions frame the new speculative registers, so they
      preserve their simple domain invariant;
  (3) Z3 checks ONLY the new transition schemas preserve the original and
      new invariant, including the read-vs-reference comparison at retirement.

This is a one-step inductive extension, not a full CPU/speculation model.
"""
import argparse, json, os, time
from sc_msi_4core_verifier import System, a, o, neg, eq, imp, ge, le, z3_smt

class SpeculativeSystem(System):
    def __init__(self, cores=4, lines=2):
        super().__init__(cores=cores, lines=lines)
        self.oldkeys=set(self.keys)
        for c in range(cores):
            for field,typ in [('spec_active','Bool'),('spec_addr','Int'),('spec_version','Int')]:
                key=f'{field}_{c}'
                self.keys.append(key)
                self.types[key]=typ

    def sp(self,c,k,nxt=False):
        return self.v(f'spec_{k}_{c}',nxt)

    def init(self):
        return a(super().init(),*(a(neg(self.sp(c,'active')),
                                  eq(self.sp(c,'addr'),'0'),
                                  eq(self.sp(c,'version'),'0'))
                                 for c in range(self.n)))

    def spec_inv(self,nxt=False):
        return a(*(a(ge(self.sp(c,'addr',nxt),'0'),
                    le(self.sp(c,'addr',nxt),str(self.k-1)),
                    ge(self.sp(c,'version',nxt),'0')) for c in range(self.n)))

    def inv(self,nxt=False):
        return a(super().inv(nxt),self.spec_inv(nxt))

    def inherited_steps(self):
        # Existing proof covers these actions. The only change to old actions
        # is to prevent issuing a NEW architectural instruction while a
        # speculative load (which is next in program order) awaits retirement.
        out=[]
        for label,formula in super().steps():
            if label.startswith('core') and ':issue_' in label:
                c=int(label.split(':')[0][4:])
                formula=a(formula,neg(self.sp(c,'active')))
            out.append((label,formula))
        return out

    def delta_steps(self,unsafe=False):
        steps=[]
        for c in range(self.n):
            busy=self.cpu(c,'busy');active=self.sp(c,'active')
            addr=self.sp(c,'addr');token=self.sp(c,'version')
            for l in range(self.k):
                mode=self.pl(l,'mode',c);pending=self.pl(l,'pending',c)
                valid=a(o(eq(mode,'1'),eq(mode,'2')),neg(pending))
                # This is a speculative LOAD following an older uncompleted
                # instruction; fetch its value from a valid L1 hit.
                steps.append(self.step(
                    f'core{c}:spec_execute_line{l}',
                    a(busy,neg(active),valid),
                    {f'spec_active_{c}':'true',f'spec_addr_{c}':str(l),
                     f'spec_version_{c}':self.pl(l,'val',c)}))

                matched=a(valid,eq(token,self.pl(l,'val',c)))
                bad_or=o(self.v('bad'),neg(eq(token,self.v(f'ref_{l}'))))
                steps.append(self.step(
                    f'core{c}:spec_retire_line{l}'+('_unsafe' if unsafe else ''),
                    a(active,neg(busy),eq(addr,str(l)), 'true' if unsafe else matched),
                    {f'spec_active_{c}':'false',
                     f'observed_{c}':f'(select payload_{l} {token})',
                     'bad':bad_or}))

                if not unsafe:
                    # A stale/inaccessible speculative value must not retire.
                    # Reissue the same read through original MSI frontend.
                    steps.append(self.step(
                        f'core{c}:spec_replay_line{l}',
                        a(active,neg(busy),eq(addr,str(l)),neg(matched)),
                        {f'spec_active_{c}':'false',f'busy_{c}':'true',
                         f'op_{c}':'1',f'target_{c}':str(l)}))
        return steps

    def steps(self):
        return self.inherited_steps()+self.delta_steps()

    def check_delta(self,output_dir):
        os.makedirs(output_dir,exist_ok=True)
        oldinv=super().inv();newinv=self.spec_inv()
        allinv=a(oldinv,newinv)
        # Old actions: their projection to original vars is a subset of OLD
        # transition relation. Original proof says OLD_INV & OLD_T => OLD_INV'.
        # New variables stutter on old transitions. Hence no full recheck.
        goals={
            'delta_init':a(self.init(),neg(allinv)),
            'delta_induction':a(allinv, o(*(s for _,s in self.delta_steps())),
                                 neg(a(super().inv(True),self.spec_inv(True)))),
            'delta_bad':a(allinv,self.v('bad')),
            'retire_stale_impossible':a(allinv,
                o(*(s for lab,s in self.delta_steps() if ':spec_retire' in lab)),
                self.v('bad',True)),
        }
        answers=[]
        for name,assertion in goals.items():
            q=self.declarations()+'\n(assert '+assertion+')\n(check-sat)\n'
            path=os.path.join(output_dir,name+'.smt2')
            open(path,'w').write(q)
            t=time.monotonic();response=z3_smt(q).strip().splitlines()[0]
            answers.append({'obligation':name,'result':response,'seconds':round(time.monotonic()-t,3),
                            'smt_bytes':len(q),'file':name+'.smt2'})
        results={'n_cores':self.n,'n_lines':self.k,
                 'baseline_lemma':'reuse the previous OLD_INV & OLD_T => OLD_INV_next SMT proof',
                 'delta_actions':len(self.delta_steps()),
                 'new_actions':'early speculative L1 load, validated retirement, replay through MSI',
                 'results':answers,
                 'success':all(x['result']=='unsat' for x in answers)}
        open(os.path.join(output_dir,'results.json'),'w').write(json.dumps(results,indent=2))
        return results

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--cores',type=int,default=4)
    p.add_argument('--lines',type=int,default=2)
    p.add_argument('--output-dir',default='/mnt/data/spec_delta_proof')
    x=p.parse_args();s=SpeculativeSystem(x.cores,x.lines)
    print(json.dumps(s.check_delta(x.output_dir),indent=2))
