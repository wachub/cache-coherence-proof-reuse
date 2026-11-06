#!/usr/bin/env python3
"""Machine-checked premises for fair completion in the ATOMIC hierarchy model.

Asynchronous v2.0 delivery/deadlock is NOT covered. In this abstraction, every
issued command is one continuously enabled, atomic service transition (or
partition of two CAS outcome transitions). Weak fairness of Service(core)
suffices for eventual completion; the derivation is explained in the report.
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/13_hierarchy'))
from hierarchy import Hierarchy,AND,OR,NOT,EQ
from verify_hierarchy_v21 import run_one
from verify_hierarchy_equivalence_v21 import guard

def verify(fanouts,variant,output,timeout=15000):
    m=Hierarchy(fanouts,variant);I=m.invariant();steps=dict(m.steps())
    output.mkdir(parents=True,exist_ok=True)
    results=[]
    def check(name,goal):
        r=run_one(m,output,name,goal,timeout_ms=timeout)
        results.append(r)
        if not r['passed']:raise AssertionError(r)
    for c in range(m.n):
        pending=m.c(c,'pending');pending_p=m.c(c,'pending',True)
        service_labels=[n for n in steps if n.startswith(f'core{c}:serve_')]
        enable=OR(*(guard(m,n) for n in service_labels))
        check(f'c{c}_service_enabled_if_pending',AND(I,pending,NOT(enable)))
        for label,t in steps.items():
            name=label.replace(':','_')
            if label in service_labels:
                # Pending is always cleared by a service transition.
                check(f'c{c}_service_clears_{name}',AND(I,pending,t,pending_p))
            else:
                # No other processor or issue step can silently drop the
                # outstanding request.
                check(f'c{c}_persists_across_{name}',AND(I,pending,t,NOT(pending_p)))
    summary={'variant':variant,'topology':m.top.summary(),'checks':len(results),
             'passed':all(r['passed'] for r in results),'results':results,
             'temporal_claim':'Under WF(Service(c)) for each core, every issued request eventually completes.',
             'proof_scope':'Atomic service transitions; asynchronous packet/channel progress not modeled.'}
    (output/'summary.json').write_text(json.dumps(summary,indent=2))
    return summary

def main():
    p=argparse.ArgumentParser();p.add_argument('--fanouts',nargs='+',type=int,default=[2,2])
    p.add_argument('--variant',choices=['MSI','MESI','MOESI','all'],default='all')
    p.add_argument('--output-dir',type=Path,default=ROOT/'artifacts/hierarchy_v21_progress')
    args=p.parse_args();vs=('MSI','MESI','MOESI') if args.variant=='all' else (args.variant,)
    xs=[verify(tuple(args.fanouts),v,args.output_dir/(v.lower()+'_'+'_'.join(map(str,args.fanouts)))) for v in vs]
    print(json.dumps({'passed':all(x['passed'] for x in xs),'checks':sum(x['checks'] for x in xs)},indent=2))
if __name__=='__main__':main()
