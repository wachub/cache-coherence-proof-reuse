#!/usr/bin/env python3
"""v1.9: Audit safety, deadlock enabledness and progress premises of REDUCED MSI.

This is NOT an end-to-end native temporal (LTL/TLA+/CTL) theorem over the
infinite-state model. It is a reproducible collection of concrete transition-
level Z3 obligations, a logical-equivalence audit and an independently executed
fair-lasso check of the *separate finite abstraction*.

No protocol transition or environment assumption is changed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from directory_invariant_minimize import (MinimizedDirectorySpec,TemporalFairSpec,
    REMOVED_SCHEMAS,clauses_by_schema,invariant_without)
from progress_v16_verify import (a,neg,z3_smt,invariant_queries,local_progress_queries,
    frontend_progress_queries,unconditional_no_terminal_stall_queries,
    generic_rr_arithmetic,generic_transaction_rank_arithmetic)
from temporal_v17_verify import lemmas
from fair_lasso_v17 import run_case
from progress_v16_witnesses import repaired_arbitrary_write, starving_queued_core_lasso


def query(declarations, formula, path, timeout_ms=60000, prior=None):
    # A SAT or UNKNOWN response is NEVER a successful proof.
    content=f'(set-option :timeout {timeout_ms})\n'+declarations+'\n(assert '+formula+')\n(check-sat)\n'
    path.parent.mkdir(exist_ok=True,parents=True)
    path.write_text(content)
    base_query=declarations+'\n(assert '+formula+')\n(check-sat)\n'
    base_hash=hashlib.sha256(base_query.encode()).hexdigest()
    if prior and prior.get('status')=='unsat' and prior.get('sha256')==base_hash:
        return {'status':'unsat','passed':True,'seconds':0,'verified_by':'v1.8 exact-query SHA256 match to prior Z3 UNSAT result',
                'sha256':hashlib.sha256(content.encode()).hexdigest(), 'original_sha256':base_hash,
                'file':str(path.resolve().relative_to(ROOT))}
    t0=time.monotonic();res=z3_smt(content).strip();status=res.splitlines()[0] if res else 'error'
    return {'status':status,'passed':status=='unsat','seconds':round(time.monotonic()-t0,5),'verified_by':'fresh Z3 execution',
            'sha256':hashlib.sha256(content.encode()).hexdigest(),
            'file':str(path.resolve().relative_to(ROOT))}


def check_group(declarations,goals,directory,timeout_ms,verbose,prior=None):
    out={}
    for key,formula in goals.items():
        out[key]=query(declarations,formula,directory/(key+'.smt2'),timeout_ms,prior=(prior or {}).get(key))
        if verbose or not out[key]['passed']:
            print(' ',directory.name,key,out[key]['status'],flush=True)
    return out


def run(cores=(4,),lines=(2,3),out=ROOT/'artifacts'/'minimized_temporal_progress_v1_9',
        timeout_ms=60000,max_abstract_cores=4,verbose=False):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    summary={'version':'v1.9','branch':'proof/minimized-invariant-progress-v1.9',
        'model':'exactly v1.8 MinimizedDirectorySpec; protocol transitions unchanged',
        'proof_scope':{
         'induction':'concrete full-step SMT safety invariant proof for listed fixed configurations',
         'deadlock':'no terminal stall when outstanding work; enabledness only',
         'local_progress':'ranking and fairness premises for individual transactions and CPU/speculative operations',
         'temporal':'finite fair-lasso model checking of a separate abstraction; composition is still a paper mathematical argument, NOT a concrete LTL certificate',
         'parameterization':'symbolic-N arithmetic lemmas; NOT all-N concrete-system induction',
         'reuse':'v1.8 temporal UNSAT results reused only when exact-query SHA256 matches the prior successful manifest'},
        'fairness_assumptions':{
            'weak':['SomeService(line)','SomeStart(line)','ResolveUnconfirmedWrites(core)',
                    'ResolveUnconfirmedRead(core)','IssueConfirmedStore(core)','SettleConfirmedRead(core)'],
            'strong':['CPUAsk(core,kind,line)','CPUComplete(core,kind,line)'],
            'excluded':['fairness of initiating new architectural commands',
                        'committing squashed speculation']},
        'removed_directory_schemas':sorted(REMOVED_SCHEMAS),
        'configurations':{},'symbolic_arithmetic':{},'finite_abstraction':{},'concrete_trace_witnesses':{}}
    for name,builder in [('round_robin',generic_rr_arithmetic),
                          ('transaction_rank',generic_transaction_rank_arithmetic)]:
        decls,goals=builder()
        summary['symbolic_arithmetic'][name]=check_group(decls,goals,out/'symbolic_arithmetic'/name,timeout_ms,verbose)
        print('Symbolic arithmetic',name,len(goals),'checks',flush=True)

    old_manifest=ROOT/'artifacts/directory_minimization_v1_8/v17_premises_rechecked_v18.json'
    if old_manifest.exists():
        old_manifest=json.loads(old_manifest.read_text())
        if not old_manifest.get('passed'):old_manifest=None
    else:old_manifest=None
    for n in cores:
      if n < 1:raise ValueError('cores must be positive')
      for k in lines:
        if k < 1:raise ValueError('lines must be positive')
        name=f'{n}cores_{k}lines'
        print('CONFIG',name,flush=True)
        m=MinimizedDirectorySpec(n,k)
        # All the lemmas below refer to the very same concrete transition relation.
        old=TemporalFairSpec(n,k)
        name_dir=out/name
        identical=(m.T()==old.T() and m.init()==old.init() and m.declarations()==old.declarations())
        if not identical:raise AssertionError('Concrete transition schema was modified in '+name)
        equivalence={
          'minimized_implies_full':a(m.inv(),neg(old.inv())),
          'full_implies_minimized':a(old.inv(),neg(m.inv())),
          'all_deleted_directory_schemas_follow_from_minimized':a(
                 m.inv(),neg(clauses_by_schema(m,REMOVED_SCHEMAS))),
          'minimized_next_implies_full_next':a(m.inv(True),neg(old.inv(True))),
        }
        groups={
            'logical_equivalence':equivalence,
            'safety_and_speculation':invariant_queries(m),
            'directory_and_arbitration_progress':local_progress_queries(m),
            'frontend_progress':frontend_progress_queries(m),
            'deadlock_enabledness':unconditional_no_terminal_stall_queries(m),
            'temporal_fairness_premises':lemmas(m),
        }
        result={'groups':{},'passed':True,'exact_same_init_transition_declarations':identical}
        decls=m.declarations()
        for group,goals in groups.items():
            prior=(old_manifest or {}).get('configurations',{}).get(name,{}).get('details',{}) if group=='temporal_fairness_premises' else None
            entries=check_group(decls,goals,name_dir/group,timeout_ms,verbose,prior)
            group_ok=all(q['passed'] for q in entries.values())
            result['groups'][group]={'passed':group_ok,'count':len(entries),'details':entries}
            print(f'  {group}: {sum(q["passed"] for q in entries.values())}/{len(entries)}',flush=True)
            if not group_ok:result['passed']=False
        summary['configurations'][name]=result
        (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    for label,payload,expected in [
       ('arbitrary_integer_write_can_complete',repaired_arbitrary_write()[0],'sat'),
       ('starvation_cycle_blocked_by_round_robin',starving_queued_core_lasso(False)[0],'unsat'),
       ('starvation_cycle_allowed_by_unfair_mutant',starving_queued_core_lasso(True)[0],'sat')]:
        path=out/'concrete_trace_witnesses'/(label+'.smt2')
        path.parent.mkdir(exist_ok=True,parents=True)
        path.write_text(payload)
        start=time.monotonic()
        raw=z3_smt('(set-option :timeout '+str(timeout_ms)+')\n'+payload).strip()
        status=raw.splitlines()[0] if raw else 'error'
        summary['concrete_trace_witnesses'][label]={'status':status,'expected':expected,
            'passed':status==expected,'time_s':round(time.monotonic()-start,5),
            'sha256':hashlib.sha256(payload.encode()).hexdigest()}
        print('CONCRETE TRACE',label,status,flush=True)
    # This abstraction is *not* claimed to be a formally proved simulation of
    # MinimizedDirectorySpec. A fair-lasso result on it is supplemental evidence.
    finite=[]
    for n in range(2,max_abstract_cores+1):
        tests=[('fair_round_robin',{},False),
               ('unfair_arbiter',{'unfair':True},True),
               ('weak_cpu_completion',{'strong_completion':False},True),
               ('unfair_service',{'service_fair':False},True),
               ('unfair_start',{'start_fair':False},True)]
        for label,options,expected in tests:
            case=run_case(n,**options)
            case.update({'test':label,'expected_fair_incomplete_lasso':expected})
            case['passed']=case['fair_incomplete_lasso_exists']==expected
            print('ABSTRACTION',n,label,'PASS' if case['passed'] else 'FAIL',flush=True)
            finite.append(case)
    summary['finite_abstraction']={'scope':'independent finite progress abstraction, NOT the concrete MSI state machine',
        'cases':finite,'passed':all(item['passed'] for item in finite)}
    summary['passed']=bool(summary['configurations']) and all(
        x['passed'] for x in summary['configurations'].values()) and all(
        y['passed'] for group in summary['symbolic_arithmetic'].values() for y in group.values()) and summary['finite_abstraction']['passed'] and all(x['passed'] for x in summary['concrete_trace_witnesses'].values())
    summary['total_concrete_unsat']=sum(sum(group['count'] for group in c['groups'].values())
                                      for c in summary['configurations'].values())
    summary['total_symbolic_unsat']=sum(len(group) for group in summary['symbolic_arithmetic'].values())
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    (out/'fair_lasso.json').write_text(json.dumps(summary['finite_abstraction'],indent=2)+'\n')
    print('TOTAL',summary['total_concrete_unsat'],'concrete obligations,',
          summary['total_symbolic_unsat'],'symbolic-N arithmetic,',len(finite),'fair-lasso cases, 3 concrete trace witnesses:',
          'PASS' if summary['passed'] else 'FAIL',flush=True)
    return summary

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cores',nargs='+',type=int,default=[4])
    p.add_argument('--lines',nargs='+',type=int,default=[2,3])
    p.add_argument('--output-dir',type=Path,default=ROOT/'artifacts/minimized_temporal_progress_v1_9')
    p.add_argument('--timeout-ms',type=int,default=60000)
    p.add_argument('--max-abstract-cores',type=int,default=4)
    p.add_argument('--verbose',action='store_true')
    args=p.parse_args()
    try:r=run(args.cores,args.lines,args.output_dir,args.timeout_ms,args.max_abstract_cores,args.verbose)
    except Exception as exc:
        print('VERIFICATION FAILED:',repr(exc),file=sys.stderr)
        raise
    raise SystemExit(0 if r['passed'] else 1)
