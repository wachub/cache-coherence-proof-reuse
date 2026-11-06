#!/usr/bin/env python3
"""Replay v1.7 concrete temporal premises with v1.8 minimized directory I.

No new temporal theorem is claimed: the old 290 transition-level premises are
rechecked with a proven-equivalent smaller invariant. Unknown and SAT are FAIL.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
from directory_invariant_minimize import MinimizedDirectorySpec
from temporal_v17_verify import lemmas
from cache_smt_verifier import z3_smt

ROOT=Path(__file__).resolve().parents[1]
def run(cores=4,lines=(2,3),output=ROOT/'artifacts/directory_minimization_v1_8'):
    summary={'check_type':'v1.7 concrete fairness/progress premises with minimized invariant',
             'warning':'Not a native global temporal liveness theorem',
             'configurations':{}}
    for k in lines:
        m=MinimizedDirectorySpec(cores,k)
        goals=lemmas(m);declarations=m.declarations()
        records={}
        for label,formula in goals.items():
            q=declarations+'\n(assert '+formula+')\n(check-sat)\n'
            tic=time.monotonic();raw=z3_smt(q).strip().splitlines()[0]
            records[label]={'status':raw,'seconds':round(time.monotonic()-tic,4),
                            'sha256':hashlib.sha256(q.encode()).hexdigest()}
            if raw!='unsat':
                print('FAIL',cores,k,label,raw,flush=True)
                break
        key=f'{cores}cores_{k}lines'
        summary['configurations'][key]={'passed':len(records)==len(goals) and all(x['status']=='unsat' for x in records.values()),
                                        'checked':len(records),'expected':len(goals),'details':records}
        print(key,summary['configurations'][key]['passed'],len(records),len(goals),flush=True)
    summary['passed']=all(x['passed'] for x in summary['configurations'].values())
    output.mkdir(parents=True,exist_ok=True)
    (output/'v17_premises_rechecked_v18.json').write_text(json.dumps(summary,indent=2)+'\n')
    if not summary['passed']:raise RuntimeError('Minimized invariant fails original temporal premises')
    return summary

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cores',type=int,default=4)
    p.add_argument('--lines',type=int,nargs='+',default=[2,3])
    p.add_argument('--output',type=Path,default=ROOT/'artifacts/directory_minimization_v1_8')
    args=p.parse_args()
    run(args.cores,args.lines,args.output)
