"""Deliberately invalid coherence optimizations must trigger SAT induction failures."""
from __future__ import annotations
import hashlib,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent))
from extended_system import ExtendedFairSpec
from cache_smt_verifier import a,eq,neg,z3_smt

def line_step(m,label,guard,patch,line=0):
    raw=m.p.step(guard,patch,label)[1]
    frames=[eq(m.v(key,True),m.v(key)) for key in m.keys if not key.startswith(f'l{line}__')]
    frames.append(eq(m.v(f'l{line}__rr_turn',True),m.v(f'l{line}__rr_turn')))
    return a(m.map_line(raw,line),*frames)

def run(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    records={}
    m=ExtendedFairSpec(2,1,'MESI')
    p=m.p; V=p.v;L=p.L
    unsafe_E=line_step(m,'mutant:grant_E_even_with_sharer',
        a(eq(V('tx'),'0'),eq(V('phase'),'0'),eq(V('kind'),'1'),
          *(neg(L('wait',j)) for j in range(p.n))),
        {'phase':'1','kind':'3','grS_0':'true','grv_0':V('latest'),'owner':'0'})
    records['mesi_unsafe_exclusive_grant']=query(m,unsafe_E,out/'mesi_unsafe_exclusive_grant.smt2')
    m=ExtendedFairSpec(2,1,'MOESI');p=m.p;V=p.v;L=p.L
    bad_drop=line_step(m,'mutant:drop_dirty_O_owner_without_writeback',
        a(L('wb',0),L('wait',0),eq(L('mode',0),'4'),eq(V('kind'),'1')),
        {'wb_0':'false','wait_0':'false','owner':'(- 1)'})
    records['moesi_drop_dirty_owner']=query(m,bad_drop,out/'moesi_drop_dirty_owner.smt2')
    (out/'negative_controls_summary.json').write_text(json.dumps(records,indent=2))
    for k,x in records.items():print(k,x['result'])
    return all(x['passed'] for x in records.values())

def query(m,step,out):
    text='(set-option :timeout 20000)\n'+m.declarations()+'\n'
    for part in (m.inv(),step,neg(m.inv(True))):text+='(assert '+part+')\n'
    text+='(check-sat)\n';out.write_text(text)
    raw=z3_smt(text).strip();status=raw.splitlines()[0] if raw else 'error'
    return {'result':status,'passed':status=='sat','query_hash':hashlib.sha256(text.encode()).hexdigest()}
if __name__=='__main__':sys.exit(0 if run(Path(sys.argv[1]) if len(sys.argv)>1 else Path('artifacts/mesi_moesi_v20/mutants')) else 1)
