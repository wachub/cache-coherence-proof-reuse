#!/usr/bin/env python3
"""Z3 satisfiable execution witnesses for asynchronous MSI with four cores."""
import os, re, json, time
from sc_msi_4core_verifier import System, z3_smt

def run_trace(system, labels, assertions, destination):
    dictionary=dict(system.steps()); assert all(l in dictionary for l in labels)
    keys=sorted(system.keys,key=len,reverse=True)
    rx=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,keys))+r')(_next)?(?![A-Za-z0-9_])')
    def subs(expr,j):return rx.sub(lambda m:f's{j+int(bool(m.group(2)))}__{m.group(1)}',expr)
    parts=['(set-logic ALL)']+[f'(declare-const payload_{l} (Array Int Int))' for l in range(system.k)]
    for i in range(len(labels)+1):
        for k,typ in system.types.items():parts.append(f'(declare-const s{i}__{k} {typ})')
    parts.append('(assert '+subs(system.init(),0)+')')
    for i,label in enumerate(labels):parts.append('(assert '+subs(dictionary[label],i)+')')
    for constraint in assertions:parts.append('(assert '+constraint+')')
    parts.append('(check-sat)')
    q='\n'.join(parts)+'\n'
    os.makedirs(os.path.dirname(destination),exist_ok=True)
    open(destination,'w').write(q)
    start=time.monotonic();answer=z3_smt(q).strip().splitlines()[0]
    return {'result':answer,'seconds':round(time.monotonic()-start,3),'events':labels,'smt_file':os.path.basename(destination)}

def witness(out_dir='/mnt/data/sc_msi_smt4'):
    s=System(4,2)
    read_labels=[
      'core0:issue_2_line0','core0:ask_write_line0',
      'l0::dir:start_rqW_c0','l0::dir:grant_M_c0','l0::net:deliver_grM_c0',
      'core0:complete_store_line0','l0::dir:accept_gack_c0',
      'core1:issue_1_line0','core1:ask_read_line0',
      'l0::dir:start_rqR_c1','l0::net:deliver_recall_c0','l0::dir:accept_wb_c0',
      'l0::dir:grant_S_c1','l0::net:deliver_grS_c1','core1:complete_read_line0']
    r=run_trace(s,read_labels,
                ['(= s1__newval_0 42)','(= s15__observed_1 42)','(not s15__busy_1)'],
                os.path.join(out_dir,'ownership_handoff_witness.smt2'))
    cas_labels=[
      'core0:issue_3_line0','core1:issue_3_line0',
      'core0:ask_write_line0','core1:ask_write_line0',
      'l0::dir:start_rqW_c0','l0::dir:grant_M_c0','l0::net:deliver_grM_c0',
      'core0:complete_cas_line0','l0::dir:accept_gack_c0',
      'l0::dir:start_rqW_c1','l0::net:deliver_recall_c0','l0::dir:accept_wb_c0',
      'l0::dir:grant_M_c1','l0::net:deliver_grM_c1','core1:complete_cas_line0']
    r2=run_trace(s,cas_labels,
                 ['(= (select payload_0 0) 0)',
                  '(= s1__expected_0 0)','(= s1__newval_0 42)',
                  '(= s2__expected_1 0)','(= s2__newval_1 99)',
                  's15__cas_success_0','(not s15__cas_success_1)',
                  '(= s15__observed_1 42)'],
                 os.path.join(out_dir,'competing_cas_witness.smt2'))
    results={'handoff':r,'competing_cas':r2}
    open(os.path.join(out_dir,'witness_results.json'),'w').write(json.dumps(results,indent=2))
    return results
if __name__=='__main__':print(json.dumps(witness(),indent=2))
