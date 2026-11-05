#!/usr/bin/env python3
"""Incremental liveness/progress analysis for the *unchanged* v1.4 cache model.

This proves local service enabling and a well-founded phase ranking for one
arbitrary MSI line at fixed core count, checks speculative frontend enabling,
and produces a reachable symbolic-data stall witness. It does *not* claim a
full fair-path liveness theorem or unconditional starvation freedom.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / 'experiments' / '09_combined_speculative_reads_writes'
sys.path.insert(0, str(MODEL))
from cache_smt_verifier import Protocol, a, o, neg, eq, imp, z3_smt
from sc_msi_4core_verifier import System
from combined_speculative_model import CombinedSpec


def capture_protocol_guards(p: Protocol):
    captured = {}
    original = p.step
    def intercepted(guard, patch, label):
        assert label not in captured, label
        captured[label] = guard
        return original(guard, patch, label)
    p.step = intercepted
    try:
        transitions = p.transitions()
    finally:
        p.step = original
    assert set(captured) == {label for label, _ in transitions}
    return captured, dict(transitions)


def capture_spec_guards(model: CombinedSpec):
    captured = {}
    original = model.step
    def intercepted(label, guard, patch):
        assert label not in captured, label
        captured[label] = guard
        return original(label, guard, patch)
    model.step = intercepted
    try:
        transitions = model.delta_steps()
    finally:
        model.step = original
    assert set(captured) == {label for label, _ in transitions}
    return captured, dict(transitions)


def is_service(label):
    return label.startswith(('net:deliver_', 'dir:accept_', 'dir:grant_'))


def count_bools(*terms):
    return '(+ 0 ' + ' '.join(f'(ite {t} 1 0)' for t in terms) + ')' if terms else '0'


def transaction_rank(p, nxt=False):
    """Strict descent for servicing steps of an already-active transaction.

    Phase 0: 8 + 3*pending victim acknowledgments + undelivered recall/inv.
    Phase 1: 2 + outstanding grant messages.
    Idle: 0. Never claimed to decrease across START of a new transaction.
    """
    w = count_bools(*(p.L('wait', c, nxt) for c in range(p.n)))
    early = count_bools(*(o(p.L('inv',c,nxt),p.L('recall',c,nxt)) for c in range(p.n)))
    grants = count_bools(*(o(p.L('grS',c,nxt),p.L('grM',c,nxt)) for c in range(p.n)))
    return (f'(ite (= {p.v("tx",nxt)} (- 1)) 0 '
            f'(ite (= {p.v("phase",nxt)} 0) (+ 8 (* 3 {w}) {early}) '
            f'(+ 2 {grants})))')


def nextify_protocol_guard(p,guard):
    """Replace every unprimed Protocol symbol by its next-state counterpart."""
    rx=re.compile(r'(?<![a-zA-Z0-9_])('+
         '|'.join(map(re.escape,sorted(p.keys,key=len,reverse=True)))+
         r')(?![a-zA-Z0-9_])')
    return rx.sub(lambda m:m.group(1)+'_next',guard)


def protocol_obligations(n):
    p = Protocol(n=n, max_version=None)
    guards, steps = capture_protocol_guards(p)
    servicing = [(label, steps[label]) for label in steps if is_service(label)]
    request_start = [g for label,g in guards.items() if label.startswith('dir:start_')]
    service_en = o(*(guards[label] for label,_ in servicing))
    nonservice=o(*(step for label,step in steps.items() if not is_service(label)))
    # Weak fairness of *individual* servicing actions is sufficient only if
    # an enabled servicing guard cannot be disabled by arbitrary nonservicing
    # steps. Check precisely that stability condition (not just their union).
    disabled_without_service=o(*(a(guards[label],neg(nextify_protocol_guard(p,guards[label])))
                          for label,_ in servicing))
    any_request = o(*(p.L(k,c) for c in range(n) for k in ('rqR','rqW')))
    active = neg(eq(p.v('tx'),'(- 1)'))
    idle = eq(p.v('tx'),'(- 1)')
    rank = transaction_rank(p)
    rank_next = transaction_rank(p, True)
    # Shared natural-number rank is strictly reduced by every servicing step.
    # A concurrent local write is allowed to stutter on this rank.
    goals = {
        'active_transaction_has_service_step': a(p.inv(),active,neg(service_en)),
        'idle_queued_request_can_start': a(p.inv(),idle,any_request,neg(o(*request_start))),
        'service_strictly_decreases_rank': a(p.inv(),active,o(*(step for _,step in servicing)),
                                             neg(f'(< {rank_next} {rank})')),
        'active_transaction_rank_never_increases': a(p.inv(),active,p.T(),
                                                        neg(f'(<= {rank_next} {rank})')),
        'active_transaction_rank_is_positive': a(p.inv(),active,neg(f'(> {rank} 0)')),
        'active_transaction_rank_bounded': a(p.inv(),active,f'(> {rank} {8+4*n})'),
        'enabled_service_guard_persists_without_service':a(p.inv(),active,nonservice,disabled_without_service),
    }
    return p.declarations(), goals, {
        'per_line_protocol_transition_schemas':len(steps),
        'service_transition_schemas':len(servicing),
        'rank':'idle=0; phase0=8+3*wait_count+undelivered_inval_or_recall; phase1=2+undelivered_grant_count',
        'assumption':'All servicing actions are scheduled weakly fairly; request arbitration needs stronger fairness for starvation freedom.',
    }


def frontend_obligations(n, lines):
    m = CombinedSpec(n,lines)
    guards,_ = capture_spec_guards(m)
    oldinv = System.inv(m)
    inv = a(oldinv, m.new_inv())
    goals={}
    for c in range(n):
        q=m.x(c,'qlen'); ready=m.x(c,'ready'); active=m.x(c,'load_active')
        confirmed=m.x(c,'load_confirmed'); busy=m.cpu(c,'busy')
        confirm=guards[f'core{c}:confirm']
        squash_suffix=guards[f'core{c}:squash_suffix']
        squash_read=guards[f'core{c}:squash_read']
        issue=o(*(guards[f'core{c}:issue_confirmed_store_line{l}'] for l in range(lines)))
        settle=o(*(guards[f'core{c}:spec_retire_fast_line{l}'] for l in range(lines)),
                 *(guards[f'core{c}:spec_replay_line{l}'] for l in range(lines)))
        goals[f'core{c}_unresolved_speculation_has_resolution'] = a(
            inv,o(f'(> {q} {ready})',a(active,neg(confirmed))),
            neg(o(confirm,squash_suffix,squash_read)))
        goals[f'core{c}_confirmed_store_head_can_issue_when_idle'] = a(
            inv,f'(> {ready} 0)',neg(busy),neg(issue))
        goals[f'core{c}_confirmed_load_can_retire_or_replay_when_idle'] = a(
            inv,active,confirmed,eq(q,'0'),neg(busy),neg(settle))
    return m.declarations(),goals,{'cores':n,'lines':lines,'speculative_obligations':len(goals)}




def protocol_negative_controls(n):
    """Intentionally remove critical service types; expect SAT witnesses."""
    p=Protocol(n=n,max_version=None)
    guards,steps=capture_protocol_guards(p)
    active=neg(eq(p.v('tx'),'(- 1)'))
    without_grant=o(*(g for label,g in guards.items()
                      if is_service(label) and not label.startswith('dir:grant_')))
    # Wrong progress ranking: count only victim waits, omitting message-delivery
    # phases. A delivered invalidation does not lower this incorrect rank.
    rank=lambda nxt:count_bools(*(p.L('wait',c,nxt) for c in range(p.n)))
    phase0_service=o(*(step for label,step in steps.items()
                        if label.startswith('net:deliver_inv_') or label.startswith('net:deliver_recall_')))
    return p.declarations(), {
        'mutant_drop_grants_can_block_active_transaction':a(p.inv(),active,neg(without_grant)),
        'mutant_wait_only_rank_fails_strict_descent':a(p.inv(),active,phase0_service,
                                neg(f'(< {rank(True)} {rank(False)})')),
    }


def architectural_frontend_obligations(n,lines):
    """CPU local-progress proof conditional on representable symbolic payloads.

    An outstanding instruction either has a queued/in-flight coherence request
    or has an enabled ask/complete action. It is *not* a fair completion proof.
    """
    m=System(n,lines)
    guards={}
    original=m.step
    def intercepted(label,guard,patch):
        assert label not in guards
        guards[label]=guard
        return original(label,guard,patch)
    m.step=intercepted
    try:
        m.steps()
    finally:
        m.step=original
    goals={}
    for c in range(n):
        busy=m.cpu(c,'busy');op=m.cpu(c,'op');target=m.cpu(c,'target')
        pending=o(*(a(eq(target,str(l)),m.pl(l,'pending',c)) for l in range(lines)))
        service=o(*(guard for label,guard in guards.items()
                  if label.startswith(f'core{c}:ask_') or label.startswith(f'core{c}:complete_')))
        representability=[]
        for l in range(lines):
            mode=m.pl(l,'mode',c);version=m.pl(l,'latest')
            current=f'(select payload_{l} {m.pl(l,"val",c)})'
            next_value=f'(select payload_{l} (+ {version} 1))'
            cas_success=eq(current,m.cpu(c,'expected'))
            lhs=a(busy,eq(target,str(l)),eq(mode,'2'),neg(m.pl(l,'pending',c)))
            representability.extend([
                imp(a(lhs,eq(op,'2')),eq(next_value,m.cpu(c,'newval'))),
                imp(a(lhs,eq(op,'3'),cas_success),eq(next_value,m.cpu(c,'newval'))),
            ])
        rep=a(*representability)
        goals[f'core{c}_busy_not_pending_has_ask_or_completion_if_payload_available']=a(
             m.inv(),busy,neg(pending),rep,neg(service))
        # Pending always corresponds to a real queued request or directory tx.
        goals[f'core{c}_pending_has_protocol_work']=a(
             m.inv(),pending,
             neg(o(*(a(eq(target,str(l)),
                     o(m.pl(l,'rqR',c),m.pl(l,'rqW',c),
                       eq(m.pl(l,'tx'),str(c)))) for l in range(lines)))))
    return m.declarations(),goals,{'cores':n,'lines':lines,
        'assumption':'The immutable payload at the next version equals the requested write value for any locally executable store or successful CAS.'}




def rank_frame_obligations(n,lines):
    """Machine-check that non-line-service actions frame this line's rank.

    Includes other cache lines, normal CPU reads/writes/CAS, and *all* existing
    speculative transitions. This validates the compositional transfer from
    the standalone Protocol rank lemma to the combined model.
    """
    m=CombinedSpec(n,lines)
    actions=m.steps()
    goals={}
    oldinv=System.inv(m)
    bothinv=a(oldinv,m.new_inv())
    for l in range(lines):
        rank=m.map_line(transaction_rank(m.p),l)
        rank_next=m.map_line(transaction_rank(m.p,True),l)
        unrelated=o(*(step for label,step in actions if not label.startswith(f'l{l}::')))
        goals[f'line{l}_all_foreign_and_frontend_steps_frame_transaction_rank']=a(
            bothinv,unrelated,neg(eq(rank,rank_next)))
    return m.declarations(),goals,{'cores':n,'lines':lines,
        'step_schemas':len(actions),
        'assumption':'Both inherited inductive invariants; all active model transitions enumerated.'}


def combined_no_terminal_stall_obligation(n,lines):
    """Whole-system enabledness under explicitly stated input fairness.

    Only *progress* actions count: starting or servicing protocol requests,
    asking/completing an existing CPU command, resolving speculation,
    issuing committed stores, or retiring/replaying loads. Issuing fresh
    commands or staging new speculative work does not count.
    """
    m=CombinedSpec(n,lines)
    p_guards,_=capture_protocol_guards(m.p)
    captured={}
    original=m.step
    def intercepted(label, guard, patch):
        assert label not in captured,label
        captured[label]=guard
        return original(label,guard,patch)
    m.step=intercepted
    try:
        m.inherited_steps()
        m.delta_steps()
    finally:
        m.step=original
    protocol_progress=o(*(m.map_line(g,l) for l in range(lines)
                       for label,g in p_guards.items() if label.startswith(('net:','dir:'))))
    def is_frontend_progress(label):
        return (':ask_' in label or ':complete_' in label or
                ':issue_confirmed_store_' in label or
                ':spec_retire_fast_' in label or ':spec_replay_' in label or
                label.endswith((':confirm',':squash_suffix',':squash_read')))
    frontend_progress=o(*(g for label,g in captured.items() if is_frontend_progress(label)))
    work=o(*(m.cpu(c,'busy') for c in range(n)),
           *(f'(> {m.x(c,"qlen")} 0)' for c in range(n)),
           *(m.x(c,'load_active') for c in range(n)),
           *(neg(eq(m.pl(l,'tx'),'(- 1)')) for l in range(lines)),
           *(m.pl(l,kind,c) for l in range(lines) for c in range(n) for kind in ('rqR','rqW')))
    # The solver's immutable payload array encoding cannot realize every
    # possible next write value at a fixed next version. Make availability
    # explicit, rather than falsely claiming unconditional progress.
    representability=[]
    for c in range(n):
        busy=m.cpu(c,'busy');op=m.cpu(c,'op');target=m.cpu(c,'target')
        for l in range(lines):
            lhs=a(busy,eq(target,str(l)),eq(m.pl(l,'mode',c),'2'),neg(m.pl(l,'pending',c)))
            version=m.pl(l,'latest')
            current=f'(select payload_{l} {m.pl(l,"val",c)})'
            next_value=f'(select payload_{l} (+ {version} 1))'
            representability.extend([
                imp(a(lhs,eq(op,'2')),eq(next_value,m.cpu(c,'newval'))),
                imp(a(lhs,eq(op,'3'),eq(current,m.cpu(c,'expected'))),
                    eq(next_value,m.cpu(c,'newval'))),
            ])
    goal=a(System.inv(m),m.new_inv(),a(*representability),work,
           neg(o(protocol_progress,frontend_progress)))
    return (m.declarations(),{'combined_busy_system_has_some_progress_action_if_payload_available':goal},
        {'cores':n,'lines':lines,'protocol_guards':len(p_guards),
         'captured_frontend_guards':len(captured),
         'assumptions':'inherited invariants; compatible next-version data representation; external speculation resolution allowed',
         'qualification':'Existence of an enabled action, NOT eventual completion under all schedules.'})


def bmc_reachable_data_stall(n=4,lines=2):
    """A reachable pending store blocked solely by symbolic payload lookup.

    This is a modeling-artifact counterexample to unconditional completion
    claims; it should not be misreported as a real MSI protocol deadlock.
    """
    m=System(n,lines)
    steps=dict(m.steps())
    path=[f'core0:issue_2_line0',f'core0:ask_write_line0',
          'l0::dir:start_rqW_c0','l0::dir:grant_M_c0',
          'l0::net:deliver_grM_c0','l0::dir:accept_gack_c0']
    assert all(x in steps for x in path)
    # Convert current/next variable names to time-indexed instances, never
    # touching the immutable symbolic payload arrays.
    names=sorted(m.keys,key=len,reverse=True)
    matcher=re.compile(r'(?<![a-zA-Z0-9_])('+'|'.join(map(re.escape,names))+r')(_next)?(?![a-zA-Z0-9_])')
    def at(formula,t):
        return matcher.sub(lambda match: f'{match.group(1)}_t{t+int(bool(match.group(2)))}', formula)
    declarations='\n'.join(f'(declare-const {key}_t{t} {typ})'
             for t in range(len(path)+1) for key,typ in m.types.items())
    declarations+='\n'+'\n'.join(f'(declare-const payload_{l} (Array Int Int))' for l in range(lines))
    final=len(path)
    bad=a(eq(f'busy_0_t{final}','true'),eq(f'op_0_t{final}','2'),
          eq(f'l0__mode_0_t{final}','2'),eq(f'l0__pending_0_t{final}','false'),
          neg(eq('(select payload_0 (+ l0__latest_t%d 1))'%final,f'newval_0_t{final}')))
    # Stronger than a one-state stall: choose a payload array whose *every*
    # version maps to zero while this pending store requests one. No future
    # coherence activity can create a version matching the requested value.
    const_payload='(= payload_0 ((as const (Array Int Int)) 0))'
    requested_value=eq(f'newval_0_t{final}','1')
    statements=[at(m.init(),0)] + [at(steps[name],i) for i,name in enumerate(path)] + [bad,const_payload,requested_value]
    text = declarations+'\n'+'\n'.join(f'(assert {st})' for st in statements)+'\n(check-sat)\n'
    return text,path



def starvation_lasso_weak_fairness(n=4):
    """Reachable 4-core single-line lasso: c0 read remains queued forever.

    Cores 1 and 2 alternately transfer exclusive ownership, each time the
    directory skips c0 when briefly idle. This is compatible with WEAK
    fairness of individual actions, because c0's start action is only
    intermittently enabled (never continuously from some point onward).
    """
    assert n>=3
    p=Protocol(n=n,max_version=None)
    steps=dict(p.transitions())
    prefix=['c0:issue_read','c1:issue_write','dir:start_rqW_c1',
            'dir:grant_M_c1','net:deliver_grM_c1','dir:accept_gack_c1',
            'c2:issue_write','dir:start_rqW_c2',
            'net:deliver_recall_c1','dir:accept_wb_c1',
            'dir:grant_M_c2','net:deliver_grM_c2','dir:accept_gack_c2']
    cycle=['c1:issue_write','dir:start_rqW_c1','net:deliver_recall_c2',
           'dir:accept_wb_c2','dir:grant_M_c1',
           'net:deliver_grM_c1','dir:accept_gack_c1',
           'c2:issue_write','dir:start_rqW_c2','net:deliver_recall_c1',
           'dir:accept_wb_c1','dir:grant_M_c2',
           'net:deliver_grM_c2','dir:accept_gack_c2']
    path=prefix+cycle
    assert all(x in steps for x in path)
    matcher=re.compile(r'(?<![a-zA-Z0-9_])('+'|'.join(map(re.escape,sorted(p.keys,key=len,reverse=True)))+r')(_next)?(?![a-zA-Z0-9_])')
    def at(formula,t):
        return matcher.sub(lambda match: f'{match.group(1)}_t{t+int(bool(match.group(2)))}', formula)
    decl='\n'.join(f'(declare-const {key}_t{t} {typ})'
        for t in range(len(path)+1) for key,typ in p.types.items())
    start=len(prefix);end=len(path)
    assertions=[at(p.init(),0)]+[at(steps[label],i) for i,label in enumerate(path)]
    # The queue remains pending and no transaction starts for its request.
    assertions.extend([eq(f'rqR_0_t{start}','true'),
                       eq(f'pending_0_t{start}','true'),
                       eq(f'tx_t{start}','(- 1)'),
                       eq(f'owner_t{start}','2')])
    assertions.extend(eq(f'{key}_t{start}',f'{key}_t{end}') for key in p.keys)
    text=decl+'\n'+'\n'.join(f'(assert {line})' for line in assertions)+'\n(check-sat)\n'
    return text,prefix,cycle



def combined_starvation_lasso(n=4,lines=2):
    """Reachable concrete starvation cycle in the *full combined* 4-core model.

    Core 0 issues a read and remains pending while cores 1 and 2 repeatedly
    perform failing CAS operations to acquire M ownership. This uses the
    original CPU frontend, full two-/three-line MSI, and speculative fields.
    The unused cores/lines are framed; no existing transition is modified.
    """
    assert n>=3 and lines>=1
    m=CombinedSpec(n,lines)
    steps=dict(m.steps())
    def acquire_by_cas(c,previous_owner):
        return [f'core{c}:issue_3_line0',f'core{c}:ask_write_line0',
                f'l0::dir:start_rqW_c{c}'] + (
                [f'l0::net:deliver_recall_c{previous_owner}',
                 f'l0::dir:accept_wb_c{previous_owner}']
                if previous_owner is not None else []) + [
                f'l0::dir:grant_M_c{c}',f'l0::net:deliver_grM_c{c}',
                f'l0::dir:accept_gack_c{c}',f'core{c}:complete_cas_line0']
    prefix=['core0:issue_1_line0','core0:ask_read_line0'] + \
           acquire_by_cas(1,None) + acquire_by_cas(2,1)
    cycle=acquire_by_cas(1,2) + acquire_by_cas(2,1)
    path=prefix+cycle
    assert all(x in steps for x in path)
    matcher=re.compile(r'(?<![a-zA-Z0-9_])('+
            '|'.join(map(re.escape,sorted(m.keys,key=len,reverse=True)))+
            r')(_next)?(?![a-zA-Z0-9_])')
    def at(formula,t):
        return matcher.sub(lambda match:f'{match.group(1)}_t{t+int(bool(match.group(2)))}',formula)
    decl='\n'.join(f'(declare-const {key}_t{t} {typ})'
         for t in range(len(path)+1) for key,typ in m.types.items())
    decl+='\n'+'\n'.join(f'(declare-const payload_{l} (Array Int Int))' for l in range(lines))
    start=len(prefix);end=len(path)
    assertions=[at(m.init(),0)]+[at(steps[label],i) for i,label in enumerate(path)]
    assertions.extend([
        eq(f'l0__rqR_0_t{start}','true'),
        eq(f'l0__pending_0_t{start}','true'),
        eq(f'busy_0_t{start}','true'),
        eq(f'l0__tx_t{start}','(- 1)'),
        eq(f'l0__owner_t{start}','2'),
        eq(f'l0__latest_t{start}','0'),
        eq(f'expected_1_t{start}','1'),
        eq(f'expected_2_t{start}','1'),
        '(= payload_0 ((as const (Array Int Int)) 0))',
    ])
    assertions.extend(eq(f'{key}_t{start}',f'{key}_t{end}') for key in m.keys)
    query=decl+'\n'+'\n'.join(f'(assert {g})' for g in assertions)+'\n(check-sat)\n'
    return query,prefix,cycle


def solve_group(declarations,goals,out,expected='unsat'):
    out.mkdir(parents=True,exist_ok=True)
    results={}
    for label,goal in goals.items():
        query=declarations+'\n(assert '+goal+')\n(check-sat)\n'
        filename=out/(label+'.smt2')
        filename.write_text(query)
        started=time.perf_counter()
        raw=z3_smt(query).strip()
        result=raw.splitlines()[0] if raw else 'error'
        results[label]={ 'result':result, 'expected':expected,
            'pass':result==expected, 'seconds':round(time.perf_counter()-started,4),
            'sha256':hashlib.sha256(query.encode()).hexdigest(),
            'query_bytes':len(query.encode()) }
        print(f'{label}: {result} ({results[label]["seconds"]:.3f}s)',flush=True)
    return results


def run(n=4,lines=(2,3),out=Path('/mnt/data/liveness_results')):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    pdecl,pgoals,meta=protocol_obligations(n)
    results={'model_version':'v1.4 cache transitions unchanged',
             'cores':n,'configurations':list(lines),
             'scope':'local transaction progress and speculative enabling only, NOT global starvation freedom',
             'protocol_meta':meta}
    results['local_protocol']=solve_group(pdecl,pgoals,out/'protocol')
    negdecl,neggoals=protocol_negative_controls(n)
    results['negative_controls']=solve_group(negdecl,neggoals,out/'negative_controls',expected='sat')
    results['frontends']={}
    results['architectural_frontends']={}
    results['combined_deadlock_checks']={}
    results['rank_frame_checks']={}
    for k in lines:
        decl,goals,notes=frontend_obligations(n,k)
        results['frontends'][str(k)]={'notes':notes,
            'checks':solve_group(decl,goals,out/f'frontend_{k}lines')}
        adecl,agoals,anotes=architectural_frontend_obligations(n,k)
        results['architectural_frontends'][str(k)]={'notes':anotes,
            'checks':solve_group(adecl,agoals,out/f'arch_frontend_{k}lines')}
        gdecl,ggoals,gnotes=combined_no_terminal_stall_obligation(n,k)
        results['combined_deadlock_checks'][str(k)]={'notes':gnotes,
            'checks':solve_group(gdecl,ggoals,out/f'combined_deadlock_{k}lines')}
        fdecl,fgoals,fnotes=rank_frame_obligations(n,k)
        results['rank_frame_checks'][str(k)]={'notes':fnotes,
            'checks':solve_group(fdecl,fgoals,out/f'rank_frames_{k}lines')}
    witness,path=bmc_reachable_data_stall(n,min(lines))
    witness_path=out/'reachable_symbolic_payload_stall.smt2'
    witness_path.write_text(witness)
    t=time.perf_counter()
    raw=z3_smt(witness).strip();res=raw.splitlines()[0] if raw else 'error'
    print('reachable symbolic payload stall:',res, flush=True)
    results['reachable_payload_stall']={
        'result':res,'expected':'sat','pass':res=='sat',
        'steps':path,'seconds':round(time.perf_counter()-t,4),
        'explanation':'Reachable state: the immutable payload array is constantly zero at every version while the pending store requests one. The completion guard can never become true, regardless of subsequent version increments. This is a representation artifact, not a real cache protocol failure.',
        'smt_file':witness_path.name}
    starvation_query,prefix,cycle=starvation_lasso_weak_fairness(n)
    starvation_file=out/'reachable_weak_fair_starvation_lasso.smt2'
    starvation_file.write_text(starvation_query)
    t=time.perf_counter()
    starvation_raw=z3_smt(starvation_query).strip()
    starvation_result=starvation_raw.splitlines()[0] if starvation_raw else 'error'
    print('reachable weak-fair starvation lasso:',starvation_result,flush=True)
    results['weak_fair_request_starvation']={
        'result':starvation_result,'expected':'sat','pass':starvation_result=='sat',
        'prefix_steps':prefix,'cycle_steps':cycle,
        'seconds':round(time.perf_counter()-t,4),
        'explanation':'One queued read is bypassed indefinitely by two other cores alternating ownership. A weak-fair scheduler can repeat this cycle because the skipped directory start is only intermittently enabled; strong fairness or fair arbitration is needed for starvation freedom.',
        'smt_file':starvation_file.name}
    results['combined_weak_fair_starvation']={}
    for k in lines:
        combined_lasso,cl_prefix,cl_cycle=combined_starvation_lasso(n,k)
        filename=out/f'reachable_combined_{n}core_{k}line_starvation_lasso.smt2'
        filename.write_text(combined_lasso)
        t=time.perf_counter()
        answer=z3_smt(combined_lasso).strip()
        outcome=answer.splitlines()[0] if answer else 'error'
        print(f'combined {n}-core {k}-line starvation lasso:',outcome,flush=True)
        results['combined_weak_fair_starvation'][str(k)]={
            'result':outcome,'expected':'sat','pass':outcome=='sat',
            'prefix_length':len(cl_prefix),'cycle_length':len(cl_cycle),
            'prefix_steps':cl_prefix,'cycle_steps':cl_cycle,
            'seconds':round(time.perf_counter()-t,4),
            'qualification':'Weak fairness of INTERNAL protocol scheduling only; fresh CPU issues are environmental actions.',
            'smt_file':filename.name}
    checks=(list(results['local_protocol'].values())+list(results['negative_controls'].values())
        + [v for z in results['frontends'].values() for v in z['checks'].values()]
        + [v for z in results['architectural_frontends'].values() for v in z['checks'].values()]
        + [v for z in results['combined_deadlock_checks'].values() for v in z['checks'].values()]
        + [v for z in results['rank_frame_checks'].values() for v in z['checks'].values()])
    results['passed']=all(r['pass'] for r in checks) and results['reachable_payload_stall']['pass'] and results['weak_fair_request_starvation']['pass'] and all(x['pass'] for x in results['combined_weak_fair_starvation'].values())
    (out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
    print('passed:',results['passed'], 'results in', out,flush=True)
    return results


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--cores',type=int,default=4)
    p.add_argument('--lines',type=int,nargs='+',default=[2,3])
    p.add_argument('--output-dir',type=Path,default=Path('/mnt/data/liveness_results'))
    args=p.parse_args()
    r=run(args.cores,tuple(args.lines),args.output_dir)
    sys.exit(0 if r['passed'] else 1)
