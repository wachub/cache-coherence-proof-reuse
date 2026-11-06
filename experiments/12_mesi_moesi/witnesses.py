"""Concrete symbolic traces demonstrating that E and O are reachable.
All traces begin in the actual model initial state and use actual step formulas.
"""
from __future__ import annotations
import argparse,hashlib,json,re,sys,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent))
from extended_system import ExtendedFairSpec
from cache_smt_verifier import z3_smt

START=[
 'core0:issue_1_line0','core0:ask_read_line0',
 'l0::dir:start_rqR_c0','l0::dir:grant_E_c0',
 'l0::net:deliver_grS_c0','l0::dir:accept_gack_c0',
 'core0:complete_read_line0','core0:issue_2_line0','core0:complete_store_line0']
MESI_DOWNGRADE=['core1:issue_1_line0','core1:ask_read_line0',
  'l0::dir:start_rqR_c1','l0::net:deliver_recall_to_I_from_2_read_c0',
  'l0::dir:accept_wb_drop_c0','l0::dir:grant_S_c1',
  'l0::net:deliver_grS_c1','l0::dir:accept_gack_c1','core1:complete_read_line0']
MOESI_DIRTY_OWNER=['core1:issue_1_line0','core1:ask_read_line0',
  'l0::dir:start_rqR_c1','l0::net:deliver_recall_to_O_from_2_c0',
  'l0::dir:accept_wb_O_read_c0','l0::dir:grant_S_c1',
  'l0::net:deliver_grS_c1','l0::dir:accept_gack_c1','core1:complete_read_line0']
MOESI_UPGRADE=['core0:issue_2_line0','core0:ask_write_line0',
  'l0::dir:start_rqW_c0','l0::net:deliver_inv_c1','l0::dir:accept_ack_c1',
  'l0::dir:grant_M_c0','l0::net:deliver_grM_c0','l0::dir:accept_gack_c0',
  'core0:complete_store_line0']
MESI_CLEAN_SHARE=['core1:issue_1_line0','core1:ask_read_line0',
  'l0::dir:start_rqR_c1','l0::net:deliver_recall_E_read_c0',
  'l0::dir:accept_wb_E_read_c0','l0::dir:grant_S_c1',
  'l0::net:deliver_grS_c1','l0::dir:accept_gack_c1','core1:complete_read_line0']

def lift(model,formula,t):
    if not hasattr(model,'_lift_re'):
        keys=sorted((key+suffix for key in model.keys for suffix in ('_next','')),key=len,reverse=True)
        model._lift_re=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,keys))+r')(?![A-Za-z0-9_])')
    def repl(match):
        token=match.group(1)
        if token.endswith('_next'):return token[:-5]+f'_s{t+1}'
        return token+f'_s{t}'
    return model._lift_re.sub(repl,formula)

def witness(m,path,goal,output):
    steps=dict(m.steps())
    assert all(label in steps for label in path),set(path)-set(steps)
    n=len(path);decl='\n'.join(f'(declare-const {key}_s{i} {typ})'
                    for i in range(n+1) for key,typ in m.types.items())
    lines=['(set-option :timeout 30000)',decl,'(assert '+lift(m,m.init(),0)+')']
    for i,step in enumerate(path):
        lines.append('(assert '+lift(m,steps[step],i)+')')
        # Intermediates must remain in the same verified state invariant.
        lines.append('(assert '+lift(m,m.inv(True),i)+')')
    lines.append('(assert '+lift(m,goal,n)+')')
    lines.append('(check-sat)')
    query='\n'.join(lines)+'\n'
    output.write_text(query);raw=z3_smt(query).strip();result=raw.splitlines()[0] if raw else 'error'
    return {'result':result,'passed':result=='sat','steps':len(path),
            'trace':path,'sha256':hashlib.sha256(query.encode()).hexdigest()}

def run(output,ncores=2,nlines=1):
    output=Path(output);output.mkdir(exist_ok=True,parents=True)
    results={}
    m=ExtendedFairSpec(ncores,nlines,'MESI')
    results['mesi_E_to_M']=witness(m,START,
        f'(and (= {m.pl(0,"mode",0)} 2) (= {m.pl(0,"latest")} 1) (= {m.pl(0,"mem")} 0) (= {m.pl(0,"owner")} 0))',
        output/'mesi_E_to_M.smt2')
    clean=START[:6]+['core0:complete_read_line0']
    results['mesi_E_to_S_downgrade']=witness(m,clean+MESI_CLEAN_SHARE,
        f'(and (= {m.pl(0,"mode",0)} 1) (= {m.pl(0,"mode",1)} 1) (= {m.pl(0,"owner")} (- 1)))',
        output/'mesi_E_to_S_downgrade.smt2')
    m=ExtendedFairSpec(ncores,nlines,'MOESI')
    results['moesi_dirty_O_supplies_S']=witness(m,START+MOESI_DIRTY_OWNER,
        f'(and (= {m.pl(0,"mode",0)} 4) (= {m.pl(0,"mode",1)} 1) (= {m.pl(0,"owner")} 0) '
        f'(= {m.pl(0,"mem")} 0) (= {m.pl(0,"latest")} 1) '
        f'(= {m.pl(0,"val",1)} {m.pl(0,"latest")}))',
        output/'moesi_dirty_O_supplies_S.smt2')
    results['moesi_O_upgrade_to_M']=witness(m,START+MOESI_DIRTY_OWNER+MOESI_UPGRADE,
        f'(and (= {m.pl(0,"mode",0)} 2) (= {m.pl(0,"mode",1)} 0) (= {m.pl(0,"owner")} 0) '
        f'(= {m.pl(0,"latest")} 2) (= {m.pl(0,"mem")} 0))',
        output/'moesi_O_upgrade_to_M.smt2')
    for name,val in results.items():print(name,val['result'],val['steps'],flush=True)
    (output/'witness_summary.json').write_text(json.dumps(results,indent=2))
    return all(r['passed'] for r in results.values())
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',default='artifacts/mesi_moesi_v20/witnesses')
    ap.add_argument('--cores',type=int,default=2);ap.add_argument('--lines',type=int,default=1);args=ap.parse_args()
    sys.exit(0 if run(args.out,args.cores,args.lines) else 1)
