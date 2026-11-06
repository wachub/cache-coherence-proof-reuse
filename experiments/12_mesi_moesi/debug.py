import sys,time
from extended_system import ExtendedFairSpec
from cache_smt_verifier import z3_smt,neg
m=ExtendedFairSpec(int(sys.argv[2]) if len(sys.argv)>2 else 2,int(sys.argv[3]) if len(sys.argv)>3 else 1,sys.argv[1] if len(sys.argv)>1 else 'MESI')
hdr='(set-option :timeout 4000)\n'+m.declarations()+'\n(assert '+m.inv()+')\n'
for lab,formula in m.steps():
  q=hdr+'(assert '+formula+')\n(assert '+neg(m.inv(True))+')\n(check-sat)\n';t=time.monotonic();r=z3_smt(q);stat=r.strip().splitlines()[0] if r.strip() else 'empty'
  if stat!='unsat':
    print('FAIL',lab,stat,'sec',time.monotonic()-t,flush=True)
    with open('/mnt/data/mesi_moesi_work/fail.smt2','w') as f:f.write(q)
    break
else: print('ALL ACTIONS inductive',len(m.steps()),flush=True)
