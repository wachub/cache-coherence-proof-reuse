#!/usr/bin/env python3
"""Optional full-system induction cross-check, not needed for delta proof reuse."""
import json,os,time,sys
from combined_speculative_model import CombinedSpec,a,neg,z3_smt
from sc_msi_4core_verifier import System

def run(n=4,lines=2,outdir=None):
    s=CombinedSpec(n,lines);outdir=outdir or f'full_regression_{n}_{lines}'
    os.makedirs(outdir,exist_ok=True)
    inv=a(System.inv(s),s.new_inv());invnext=a(System.inv(s,True),s.new_inv(True))
    goals={'init':a(s.init(),neg(inv)),
           'induction':a(inv,s.T(),neg(invnext)),
           'safety':a(inv,s.v('bad'))}
    ans={}
    for label,body in goals.items():
        q=s.declarations()+'\n(assert '+body+')\n(check-sat)\n'
        path=os.path.join(outdir,label+'.smt2')
        with open(path,'w') as f:f.write(q)
        t=time.monotonic();r=z3_smt(q)
        ans[label]={'result':r.strip().splitlines()[0],
                    'seconds':round(time.monotonic()-t,3),'bytes':len(q)}
    with open(os.path.join(outdir,'results.json'),'w') as f:json.dump(ans,f,indent=2)
    print(json.dumps({'cores':n,'lines':lines,'checks':ans},indent=2))
    assert all(x['result']=='unsat' for x in ans.values())
if __name__=='__main__':
    run(int(sys.argv[1]) if len(sys.argv)>1 else 4,
        int(sys.argv[2]) if len(sys.argv)>2 else 2,
        sys.argv[3] if len(sys.argv)>3 else None)
