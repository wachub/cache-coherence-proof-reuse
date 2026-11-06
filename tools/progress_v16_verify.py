#!/usr/bin/env python3
"""Proof obligations for the distinct v1.6 fair-round-robin, mutable-data model.

'unsat' means the listed one-step invariant/ranking lemma holds in the
fixed-size transition system. No claim of an automated LTL model check.
"""
from __future__ import annotations
import argparse, hashlib, json, re, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments'/'10_fair_progress'))
sys.path.insert(0,str(ROOT/'tools'))
from fair_progress_model import FairProgressSpec
from liveness_verify import transaction_rank,capture_protocol_guards, is_service
from cache_smt_verifier import a,o,neg,eq,z3_smt


def rr_distance(turn,c,n):
    return f'(ite (>= {c} {turn}) (- {c} {turn}) (+ (- {c} {turn}) {n}))'


def nextify_formula(m,formula):
    rx=re.compile(r'(?<![A-Za-z0-9_])('+('|'.join(map(re.escape,sorted(m.keys,key=len,reverse=True))))+r')(?![A-Za-z0-9_])')
    return rx.sub(lambda g: g.group(1)+'_next',formula)


def generic_rr_arithmetic():
    """For symbolic positive N, modular RR always moves toward a waiting c."""
    n='N';t='T';c='C';d='D';t1='(ite (= D (- N 1)) 0 (+ D 1))'
    dc=rr_distance(t,c,n);dd=rr_distance(t,d,n);next_dc=rr_distance(t1,c,n)
    dec='\n'.join(f'(declare-const {v} Int)' for v in (n,t,c,d))
    pre=a('(>= N 1)', '(<= 0 T)','(< T N)', '(<= 0 C)','(< C N)',
          '(<= 0 D)','(< D N)')
    return dec,{
        'RR_distance_is_bounded_for_all_positive_N':a(pre,neg(a(f'(<= 0 {dc})',f'(< {dc} N)'))),
        'earlier_competitor_strictly_decreases_distance_for_all_N':a(pre,f'(< {dd} {dc})',
                                                             neg(f'(< {next_dc} {dc})')),
        'RR_next_pointer_stays_in_range_for_all_N':a(pre,neg(a('(<= 0 '+t1+')','(< '+t1+' N)'))),
    }


def generic_transaction_rank_arithmetic():
    """Symbolic N proof of descent of each service-kind's abstract counter update.

    A concrete transition's correspondence to these counter updates is
    checked separately by the composed per-configuration SMT obligations.
    """
    dec='\n'.join(f'(declare-const {k} Int)' for k in ('N','W','D','G'))
    pre=a('(>= N 1)','(<= 0 W)','(<= W N)','(<= 0 D)','(<= D N)',
          '(<= 0 G)','(<= G 1)')
    r0='(+ 8 (* 3 W) D)';r1='(+ 2 G)'
    obligations={
      'active_phase0_rank_bounded_all_N':a(pre,neg(a(f'(>= {r0} 1)',f'(<= {r0} (+ 8 (* 4 N)))'))),
      'active_phase1_rank_bounded_all_N':a(pre,neg(a(f'(>= {r1} 1)',f'(<= {r1} (+ 8 (* 4 N)))'))),
      'network_inv_or_recall_delivery_descends_all_N':a(pre,'(>= D 1)',
                                                  neg(f'(< (+ 8 (* 3 W) (- D 1)) {r0})')),
      'directory_ack_or_writeback_descends_all_N':a(pre,'(>= W 1)',
                                                  neg(f'(< (+ 8 (* 3 (- W 1)) D) {r0})')),
      'directory_grant_descends_all_N':a(pre,'(= W 0)','(= D 0)',
                                                  neg(f'(< 3 {r0})')),
      'network_grant_delivery_descends_all_N':a(pre,'(= G 1)',
                                                  neg(f'(< 2 {r1})')),
      'directory_grant_ack_descends_all_N':a(pre,'(= G 0)',
                                                  neg(f'(< 0 {r1})')),
    }
    return dec,obligations


def invariant_queries(m):
    return {
        'initial_establishes_inductive_invariant':a(m.init(),neg(m.inv())),
        'all_transitions_preserve_inductive_invariant':a(m.inv(),m.T(),neg(m.inv(True))),
        'bad_state_unreachable_under_invariant':a(m.inv(),m.v('bad')),
        'speculative_delta_preserves_architectural_effect_contract':a(
            m.inv(),o(*(step for _,step in m.delta_steps())),neg(m.interface_contract())),
    }


def local_progress_queries(m):
    """All service and RR fairness obligations at each concrete core/line."""
    goals={}; I=m.inv(); steps=dict(m.steps()); T=o(*steps.values()); p_guards,_=capture_protocol_guards(m.p)
    for l in range(m.k):
        pref=f'l{l}::'; active=neg(eq(m.pl(l,'tx'),'(- 1)'))
        idle=eq(m.pl(l,'tx'),'(- 1)')
        rank=m.map_line(transaction_rank(m.p),l)
        rank_next=m.map_line(transaction_rank(m.p,True),l)
        service=o(*(step for label,step in steps.items() if label.startswith(pref)
                    and is_service(label[len(pref):])))
        nonservice=o(*(step for label,step in steps.items() if label.startswith(pref)
                       and not is_service(label[len(pref):])))
        unrelated=o(*(step for label,step in steps.items() if not label.startswith(pref)))
        goals[f'line{l}_service_decreases_rank']=a(I,active,service,neg(f'(< {rank_next} {rank})'))
        goals[f'line{l}_nonservice_does_not_increase_rank']=a(I,active,nonservice,
                                                  neg(f'(<= {rank_next} {rank})'))
        goals[f'line{l}_unrelated_actions_frame_rank']=a(I,unrelated,neg(eq(rank,rank_next)))
        # Symbolic guard enabling is easier on the component Protocol's guards,
        # with RR selection checked in the concrete composed state below.
        service_guards=o(*(m.map_line(g,l) for label,g in p_guards.items() if is_service(label)))
        goals[f'line{l}_active_has_service_enabled']=a(I,active,neg(service_guards))
        # Weak fairness of internal servicing suffices only if an individually
        # enabled service guard persists while other *nonservicing* actions run.
        service_ones=[m.map_line(g,l) for label,g in p_guards.items() if is_service(label)]
        local_service_steps=o(*(step for label,step in steps.items()
                if label.startswith(pref) and is_service(label[len(pref):])))
        disabled=o(*(a(g,neg(nextify_formula(m,g))) for g in service_ones))
        goals[f'line{l}_service_guard_stable_without_service']=a(
            I,active,T,neg(local_service_steps),disabled)
        pending_any=o(*(m.pl(l,kind,c) for c in range(m.n) for kind in ('rqR','rqW')))
        start_guards=[]
        for c in range(m.n):
            for kind in ('rqR','rqW'):
                start_guards.append(a(idle,m.pl(l,kind,c),m._rr_selected(l,c)))
        goals[f'line{l}_idle_pending_has_start_enabled']=a(I,idle,pending_any,
                                                            neg(o(*start_guards)))
        rr=m.v(f'l{l}__rr_turn');rrnext=m.v(f'l{l}__rr_turn',True)
        any_start=o(*(step for label,step in steps.items()
                        if label.startswith(pref+'dir:start_')))
        goals[f'line{l}_RR_pointer_changes_only_on_directory_start']=a(
            I,T,neg(any_start),neg(eq(rrnext,rr)))
        for c in range(m.n):
            queued=o(m.pl(l,'rqR',c),m.pl(l,'rqW',c))
            dist=rr_distance(rr,str(c),m.n);distnext=rr_distance(rrnext,str(c),m.n)
            starts_other=o(*(step for label,step in steps.items()
                if label.startswith(pref+'dir:start_') and not label.endswith(f'_c{c}')))
            start_this=o(*(step for label,step in steps.items()
                if label.startswith(pref+'dir:start_') and label.endswith(f'_c{c}')))
            queued_next=o(m.pl(l,'rqR',c,nxt=True),m.pl(l,'rqW',c,nxt=True))
            goals[f'line{l}_core{c}_request_persists_until_selected']=a(
                I,queued,T,neg(start_this),neg(queued_next))
            goals[f'line{l}_core{c}_bypass_reduces_RR_distance']=a(I,queued,starts_other,
                neg(f'(< {distnext} {dist})'))
            goals[f'line{l}_core{c}_queued_core_cannot_be_bypassed_at_turn']=a(
                I,queued,eq(rr,str(c)),starts_other)
    return goals


def frontend_progress_queries(m):
    """The repaired data abstraction removes representability preconditions."""
    I=m.inv(); goals={}
    guards={}
    original=m.step
    def intercepted(label,guard,patch):
        # Capture *effective* guard after the old payload guard is removed.
        fixed=guard
        mo=re.fullmatch(r'core(\d+):complete_(store|cas)_line(\d+)',label)
        if mo:
            c,l=int(mo[1]),int(mo[3])
            fresh=f'(+ {m.pl(l,"latest")} 1)'
            must_equal=eq(f'(select payload_{l} {fresh})',m.cpu(c,'newval'))
            if must_equal not in fixed: raise AssertionError(label)
            fixed=fixed.replace(must_equal,'true')
        guards[label]=fixed
        return original(label,guard,patch)
    m.step=intercepted
    try:
        m.inherited_steps();m.delta_steps()
    finally:
        m.step=original
    for c in range(m.n):
        busy=m.cpu(c,'busy');op=m.cpu(c,'op');target=m.cpu(c,'target')
        pending=o(*(a(eq(target,str(l)),m.pl(l,'pending',c)) for l in range(m.k)))
        local_progress=o(*(guard for label,guard in guards.items()
                           if label.startswith(f'core{c}:ask_') or
                           label.startswith(f'core{c}:complete_')))
        goals[f'core{c}_busy_without_pending_has_unconditional_action']=a(I,busy,
                                                           neg(pending),neg(local_progress))
        good_queue=o(*(a(eq(target,str(l)),o(m.pl(l,'rqR',c),
                         m.pl(l,'rqW',c),eq(m.pl(l,'tx'),str(c))))
                         for l in range(m.k)))
        goals[f'core{c}_pending_has_directory_work']=a(I,pending,neg(good_queue))
        # Must hold for all integer newval, independently of ghost array data.
        for l in range(m.k):
            pre=a(I,busy,eq(target,str(l)),eq(m.pl(l,'mode',c),'2'),
                  neg(m.pl(l,'pending',c)),eq(op,'2'))
            goals[f'core{c}_line{l}_store_can_complete_with_arbitrary_value']=a(
                pre,neg(guards[f'core{c}:complete_store_line{l}']))
            pre_cas=a(I,busy,eq(target,str(l)),eq(m.pl(l,'mode',c),'2'),
                  neg(m.pl(l,'pending',c)),eq(op,'3'))
            goals[f'core{c}_line{l}_cas_can_complete_with_arbitrary_value']=a(
                pre_cas,neg(guards[f'core{c}:complete_cas_line{l}']))
    return goals


def unconditional_no_terminal_stall_queries(m):
    """No busy/queued/speculative configuration lacks a progress-enabled action.

    Progress enabledness is not a temporal/fair-scheduling guarantee. Fresh
    architectural issues and speculative staging are excluded intentionally.
    """
    goals={}; I=m.inv(); p_guards,_=capture_protocol_guards(m.p)
    guards={}; old=m.step
    def instrument(label, guard, patch):
        fixed=guard
        mo=re.fullmatch(r'core(\d+):complete_(store|cas)_line(\d+)',label)
        if mo:
            c,l=int(mo[1]),int(mo[3]);fresh=f'(+ {m.pl(l,"latest")} 1)'
            fixed=fixed.replace(eq(f'(select payload_{l} {fresh})',m.cpu(c,'newval')),'true')
        guards[label]=fixed
        return old(label,guard,patch)
    m.step=instrument
    try:
        m.inherited_steps();m.delta_steps()
    finally:
        m.step=old
    service=o(*(m.map_line(g,l) for l in range(m.k)
        for label,g in p_guards.items() if is_service(label)))
    start=o(*(a(m.map_line(g,l),m._rr_selected(l,c))
         for l in range(m.k)
         for c in range(m.n)
         for label,g in p_guards.items() if label.startswith('dir:start_') and label.endswith(f'_c{c}')))
    def useful(label):
        return (':ask_' in label or ':complete_' in label
            or ':issue_confirmed_store_' in label
            or ':spec_retire_fast_' in label or ':spec_replay_' in label
            or label.endswith((':confirm',':squash_suffix',':squash_read')))
    frontend=o(*(g for label,g in guards.items() if useful(label)))
    work=o(*(m.cpu(c,'busy') for c in range(m.n)),
       *(f'(> {m.x(c,"qlen")} 0)' for c in range(m.n)),
       *(m.x(c,'load_active') for c in range(m.n)),
       *(neg(eq(m.pl(l,'tx'),'(- 1)')) for l in range(m.k)),
       *(m.pl(l,kind,c) for l in range(m.k) for c in range(m.n) for kind in ('rqR','rqW')))
    goals['outstanding_work_has_a_progress_action_without_payload_assumptions']=a(
        I,work,neg(o(service,start,frontend)))
    return goals



def solve(decls,goals,dest):
    dest.mkdir(parents=True,exist_ok=True);ans={}
    for name,g in goals.items():
        query=decls+'\n(assert '+g+')\n(check-sat)\n'
        (dest/(name+'.smt2')).write_text(query)
        t=time.monotonic();raw=z3_smt(query).strip();out=raw.splitlines()[0] if raw else 'error'
        ans[name]={'result':out,'expected':'unsat','passed':out=='unsat',
                    'seconds':round(time.monotonic()-t,4),
                    'sha256':hashlib.sha256(query.encode()).hexdigest()}
        print(name, out, ans[name]['seconds'],flush=True)
    return ans


def run(ns=(2,3,4),lines=(2,3),out=ROOT/'artifacts'/'fair_progress_v1_6'):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    results={'version':'v1.6 experimental revised semantics', 'matrix':{},
             'assumptions':['Weak fairness of directory servicing actions',
             'Weak fairness of per-line directory start EVENT (not individual start alternatives)',
             'Strong fairness of each busy CPU ask/complete action',
             'Fair scheduling of confirmed-store issue and confirmed-load settle',
             'Eventual confirm-or-squash for unresolved speculation',
             'No fairness claimed for arbitrary fresh command issuance'],
             'limits':['Finite configurations are SMT-checked, not all-N inductive invariance',
             'Fair-path LTL/CTL model checking not implemented; liveness composition is a conditional mathematical argument',
             'Stateful payload maps are specification ghost variables, not an RTL memory implementation']}
    d,qs=generic_rr_arithmetic()
    results['symbolic_n_rr_arithmetic']=solve(d,qs,out/'symbolic_n_rr_arithmetic')
    d,qs=generic_transaction_rank_arithmetic()
    results['symbolic_n_transaction_rank']=solve(d,qs,out/'symbolic_n_transaction_rank')
    for n in ns:
        for k in lines:
            print('CONFIG',n,k,flush=True)
            m=FairProgressSpec(n,k);key=f'{n}cores_{k}lines'
            results['matrix'][key]={
                'invariants':solve(m.declarations(),invariant_queries(m),out/key/'invariants'),
                'protocol_and_arbitration':solve(m.declarations(),local_progress_queries(m),out/key/'protocol_and_arbitration'),
                'frontend':solve(m.declarations(),frontend_progress_queries(m),out/key/'frontend'),
                'global_deadlock_enabledness':solve(m.declarations(),unconditional_no_terminal_stall_queries(m),out/key/'global_deadlock_enabledness')}
    from progress_v16_witnesses import repaired_arbitrary_write,starving_queued_core_lasso
    results['witnesses']={}
    for label,(query,expected) in {
        'new_store_with_arbitrary_value_finishes':(repaired_arbitrary_write()[0],'sat'),
        'old_starvation_cycle_rejected_by_rr':(starving_queued_core_lasso(False)[0],'unsat'),
        'starvation_cycle_returns_with_unfair_arbiter_mutant':(starving_queued_core_lasso(True)[0],'sat'),
    }.items():
        f=out/'witnesses'/f'{label}.smt2';f.parent.mkdir(parents=True,exist_ok=True);f.write_text(query)
        start=time.monotonic();r=z3_smt(query).strip().splitlines()[0]
        results['witnesses'][label]={'result':r,'expected':expected,'passed':r==expected,
                                     'seconds':round(time.monotonic()-start,4)}
        print(label,r,flush=True)
    results['passed']=all(v['passed'] for v in results['witnesses'].values()) and all(v['passed'] for v in results['symbolic_n_rr_arithmetic'].values()) and all(v['passed'] for v in results['symbolic_n_transaction_rank'].values()) and all(
        r['passed'] for case in results['matrix'].values() for group in case.values() for r in group.values())
    (out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
    return results

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--cores',type=int,nargs='+',default=[2,3,4]);p.add_argument('--lines',type=int,nargs='+',default=[2,3]);p.add_argument('--output-dir',type=Path,default=ROOT/'artifacts'/'fair_progress_v1_6')
    x=p.parse_args();rs=run(x.cores,x.lines,x.output_dir)
    print('ALL CHECKS', 'PASS' if rs['passed'] else 'FAIL')
    sys.exit(0 if rs['passed'] else 1)
