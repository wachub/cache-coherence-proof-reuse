#!/usr/bin/env python3
"""Re-run four-core SC safety, non-vacuity and ordering-violation checks."""
import json,os
from sc_msi_4core_verifier import System
from sc_msi_trace_witness import witness
from sc_msi_ordering_mutant import check

def main():
    root=os.path.join(os.path.dirname(__file__),'proof_results')
    os.makedirs(root,exist_ok=True)
    results={}
    for n,k in ((2,2),(4,2),(4,3)):
        out=os.path.join(root,f'{n}cores_{k}lines')
        results[f'{n}cores_{k}lines']=System(n,k).check(out)
    out=os.path.join(root,'4cores_2lines')
    results['witnesses']=witness(out)
    results['ordering_mutant']=check(out)
    assert all(v['proof']=='UNBOUNDED_INDUCTION_PASS' for k,v in results.items() if k.endswith('lines'))
    assert all(v['result']=='sat' for v in results['witnesses'].values())
    assert results['ordering_mutant']=={'strict_writer_order':'unsat','broken_writer_order':'sat'}
    outfile=os.path.join(root,'summary.json');open(outfile,'w').write(json.dumps(results,indent=2))
    print('PASS: 2x2, 4x2, 4x3 inductive proofs, two SAT witnesses, and ordering mutant')
    print(outfile)
if __name__=='__main__':main()
