#!/usr/bin/env python3
"""Small SMT witness: per-line coherence alone does not prevent cross-line W/W reorder.

Time variables enumerate four per-line atomic completions:
  W(data,42), W(flag,1), R(flag)->1, R(data)->0.
Program order for the reader is preserved. If writer W(data)<W(flag), the
litmus outcome is impossible. Without that ordering it becomes possible.
"""
import json,os
from cache_smt_verifier import z3_smt

DECL='''(set-logic QF_LIA)
(declare-const t_data Int)
(declare-const t_flag Int)
(declare-const t_readflag Int)
(declare-const t_readdata Int)
(assert (distinct t_data t_flag t_readflag t_readdata))
'''
for v in ('t_data','t_flag','t_readflag','t_readdata'):
    DECL+=f'(assert (and (<= 0 {v}) (< {v} 4)))\n'
# Results encoded using per-location coherent and atomic memory:
# readflag=1 if W(flag,1) before R(flag), and read(data)=0 if R(data) before W(data).
CONSTRAINTS='''(assert (< t_flag t_readflag))
(assert (< t_readflag t_readdata))
(assert (< t_readdata t_data))
'''

def check(out='/mnt/data/sc_msi_smt4'):
    os.makedirs(out,exist_ok=True)
    results={}
    for strict in (True,False):
        name='strict_writer_order' if strict else 'broken_writer_order'
        smt=DECL+CONSTRAINTS+ ('(assert (< t_data t_flag))\n' if strict else '')+'(check-sat)\n'
        open(os.path.join(out,name+'.smt2'),'w').write(smt)
        results[name]=z3_smt(smt).strip().splitlines()[0]
    open(os.path.join(out,'ordering_mutant_results.json'),'w').write(json.dumps(results,indent=2))
    return results
if __name__=='__main__':print(json.dumps(check(),indent=2))
