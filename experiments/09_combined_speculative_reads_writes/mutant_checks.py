#!/usr/bin/env python3
"""One-step SAT mutants illustrating why interaction guards are necessary."""
import json,os,time
from combined_speculative_model import CombinedSpec,a,o,neg,eq,z3_smt

def main(out_dir=None):
    out_dir=out_dir or os.path.join(os.path.dirname(__file__),'mutants_smt')
    os.makedirs(out_dir,exist_ok=True)
    s=CombinedSpec(4,2)
    common=a(super(CombinedSpec,s).inv(),s.new_inv())
    results={}
    for kind in ('unvalidated_read','premature_read'):
        f=[]
        for lab,trans in s.delta_steps(mutant=kind):
            if ':spec_retire_fast_' not in lab:continue
            c=int(lab.split(':')[0][4:]);l=int(lab.rsplit('line',1)[1])
            if kind=='unvalidated_read':
                fails=neg(eq(s.cpu(c,'observed',True),
                           f'(select payload_{l} {s.v(f"ref_{l}")})'))
            else:
                fails=o(s.cpu(c,'busy'),neg(eq(s.x(c,'qlen'),'0')),
                        neg(s.x(c,'load_confirmed')))
            f.append(a(trans,fails))
        assertion=a(common,o(*f))
        query=s.declarations()+'\n(assert '+assertion+')\n(check-sat)\n'
        path=os.path.join(out_dir,kind+'.smt2')
        with open(path,'w') as h:h.write(query)
        t=time.monotonic();raw=z3_smt(query)
        results[kind]={'result':raw.strip().splitlines()[0],
                       'seconds':round(time.monotonic()-t,3),
                       'interpretation':('stale value can be retired' if kind=='unvalidated_read'
                          else 'younger read can retire before older memory operations'),
                       'file':os.path.basename(path)}
    with open(os.path.join(out_dir,'results.json'),'w') as f:json.dump(results,f,indent=2)
    print(json.dumps(results,indent=2))
    assert all(v['result']=='sat' for v in results.values())
if __name__=='__main__':main()
