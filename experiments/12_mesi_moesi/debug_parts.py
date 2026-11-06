import sys
from extended_system import ExtendedFairSpec
from cache_smt_verifier import z3_smt,neg,a
variant=sys.argv[1]; label=sys.argv[2] if len(sys.argv)>2 else None
m=ExtendedFairSpec(2,1,variant)
base='(set-option :timeout 2000)\n'+m.declarations()+'\n(assert '+m.inv()+')\n'
steps=m.steps();lab,st=next(((lab,st) for lab,st in steps if lab==label), (None,None)) if label else next(((lab,st) for lab,st in steps if z3_smt(base+'(assert '+st+')\n(assert '+neg(m.inv(True))+')\n(check-sat)\n').strip().splitlines()[0]=='sat'),(None,None))
print('step',lab)
base+='(assert '+st+')\n'
terms=m.p.invariant_terms(True)
for ix,ex in enumerate(terms):
 q=base+'(assert '+neg(m.map_line(ex,0))+')\n(check-sat)\n'
 res=z3_smt(q).strip().splitlines()[0]
 if res!='unsat': print('invariant fail',ix,res,ex[:240],flush=True)
for ix,ex in enumerate([m.new_inv(True),m.inv(True)]):
 q=base+'(assert '+neg(ex)+')\n(check-sat)\n'
 print('new/full',ix,z3_smt(q).strip().splitlines()[0])
