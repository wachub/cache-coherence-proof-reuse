#!/usr/bin/env python3
"""Reachability SAT (good write) and lasso SAT/UNSAT (RR fairness mutant)."""
from __future__ import annotations
import re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments'/'10_fair_progress'))
from fair_progress_model import FairProgressSpec
from cache_smt_verifier import a,eq


def timeslice(m,expr,t):
    matcher=re.compile(r'(?<![A-Za-z0-9_])('+
      '|'.join(map(re.escape,sorted(m.keys,key=len,reverse=True)))+
      r')(_next)?(?![A-Za-z0-9_])')
    return matcher.sub(lambda g:f'{g.group(1)}_t{t+int(bool(g.group(2)))}',expr)


def query_for_trace(m,path,extras=(),loop_from=None):
    steps=dict(m.steps())
    if set(path)-set(steps):raise ValueError(set(path)-set(steps))
    dec='\n'.join(f'(declare-const {key}_t{t} {typ})'
      for t in range(len(path)+1) for key,typ in m.types.items())
    clauses=[timeslice(m,m.init(),0)]+[
        timeslice(m,steps[label],i) for i,label in enumerate(path)] + list(extras)
    if loop_from is not None:
        clauses += [eq(f'{key}_t{loop_from}',f'{key}_t{len(path)}')
                       for key in m.keys]
    return dec+'\n'+'\n'.join(f'(assert {clause})' for clause in clauses)+'\n(check-sat)\n'


def repaired_arbitrary_write():
    m=FairProgressSpec(4,2)
    path=['core0:issue_2_line0','core0:ask_write_line0',
          'l0::dir:start_rqW_c0','l0::dir:grant_M_c0',
          'l0::net:deliver_grM_c0','l0::dir:accept_gack_c0',
          'core0:complete_store_line0']
    end=len(path)
    additions=[ '(= payload_0_t0 ((as const (Array Int Int)) 0))',
               '(= newval_0_t1 1)',
               eq(f'l0__latest_t{end}','1'),
               eq(f'(select payload_0_t{end} 1)','1'),
               eq(f'busy_0_t{end}','false')]
    return query_for_trace(m,path,additions),path


def starving_queued_core_lasso(unfair=False):
    m=FairProgressSpec(4,2,unfair_arbiter=unfair)
    def cas(c,previous=None,split_core0=False):
        acc=[f'core{c}:issue_3_line0',f'core{c}:ask_write_line0',
             f'l0::dir:start_rqW_c{c}']
        if split_core0:acc += ['core0:issue_1_line0','core0:ask_read_line0']
        if previous is not None:
            acc += [f'l0::net:deliver_recall_c{previous}',
                    f'l0::dir:accept_wb_c{previous}']
        acc += [f'l0::dir:grant_M_c{c}',f'l0::net:deliver_grM_c{c}',
                f'l0::dir:accept_gack_c{c}',f'core{c}:complete_cas_line0']
        return acc
    prefix=cas(1,split_core0=True)+cas(2,previous=1)
    cycle=cas(1,previous=2)+cas(2,previous=1)
    k=len(prefix)
    additions=['(= payload_0_t0 ((as const (Array Int Int)) 0))',
              eq(f'expected_1_t{k}','1'),eq(f'expected_2_t{k}','1'),
              eq(f'l0__rqR_0_t{k}','true'),eq(f'l0__pending_0_t{k}','true'),
              eq(f'l0__tx_t{k}','(- 1)'),eq(f'l0__rr_turn_t{k}','3')]
    return query_for_trace(m,prefix+cycle,additions,loop_from=k),prefix,cycle
