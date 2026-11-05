#!/usr/bin/env python3
"""Compare exact-query isolated Z3, shared-context Z3, and unchanged-cache reuse."""
from pathlib import Path
import argparse
import json
import statistics
import sys
import tempfile

sys.path.insert(0,str(Path(__file__).parent))
from fast_verify import load_combined, solve_goals

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cores',type=int,default=4)
    p.add_argument('--lines',type=int,default=2)
    p.add_argument('--repeats',type=int,default=3)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    if args.repeats<1: p.error('--repeats must be positive')
    model=load_combined(args.cores,args.lines)
    decl=model.declarations();goals=model.proof_goals()
    samples={'isolated':[],'batch':[],'cache_hit':[]}
    with tempfile.TemporaryDirectory() as tmp:
        for _ in range(args.repeats):
            for kind in ('isolated','batch'):
                ans=solve_goals(decl,goals,cache_dir=None,mode=kind)
                if not ans['passed']:raise SystemExit('Verification failed')
                samples[kind].append(ans['seconds'])
            # Prime cache with exact formulas and immediately recheck.
            prime=solve_goals(decl,goals,cache_dir=Path(tmp),mode='batch')
            if not prime['passed']:raise SystemExit('Verification failed')
            cached=solve_goals(decl,goals,cache_dir=Path(tmp),mode='batch')
            if cached['cache_hits']!=len(goals):raise SystemExit('Incomplete cache')
            samples['cache_hit'].append(cached['seconds'])
    med={k:round(statistics.median(v),4) for k,v in samples.items()}
    output={'cores':args.cores,'lines':args.lines,'repeats':args.repeats,
         'solver_version':prime['solver_version'],'goal_count':len(goals),
         'samples_seconds':samples,'medians_seconds':med,
         'isolated_over_batch_speedup':round(med['isolated']/med['batch'],2) if med['batch'] else None,
         'batch_over_cache_hit_speedup':round(med['batch']/med['cache_hit'],2) if med['cache_hit'] else None,
         'disclaimer':'Machine, workload and cache dependent; cached check not a new solver execution'}
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))
if __name__=='__main__':main()
