#!/usr/bin/env python3
"""Recheck representative induction queries without modifying archived artifacts.

Requires Linux libz3.so.4; works with standard-library Python only.
This does not review the soundness of model abstraction, and it does not claim
all earlier experiments have been rerun.
"""
from pathlib import Path
import json, tempfile, sys

ROOT=Path(__file__).resolve().parents[1]

def main():
    sys.path.insert(0,str(ROOT/'experiments/08_speculative_stores/speculative_stores_project'))
    from speculative_store_delta import SpecStore
    checks=[]
    with tempfile.TemporaryDirectory(prefix='cache_verif_') as folder:
        spec=SpecStore(4,2).proof(folder)
        checks.extend([(name,v['result']) for name,v in spec['results'].items()])
    print('Fresh Z3 rerun: speculative-store delta, 4 cores / 2 lines')
    for name, res in checks: print(f'  {name}: {res}')
    if any(res!='unsat' for _,res in checks):
        raise SystemExit('PROOF CHECK FAILED: expected every formula to be UNSAT')
    print('PASS: all four rechecked delta queries UNSAT')
    print('Note: archived predecessor proof, witnesses, and other stages not rerun here.')

if __name__=='__main__': main()
