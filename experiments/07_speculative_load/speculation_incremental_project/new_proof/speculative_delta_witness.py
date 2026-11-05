#!/usr/bin/env python3
"""Concrete legal MSI execution witnessing why speculative load validation matters."""
import json, os
from speculative_load_delta_proof import SpeculativeSystem
from sc_msi_trace_witness import run_trace

class UnsafeSpeculativeSystem(SpeculativeSystem):
    def steps(self):
        return self.inherited_steps()+self.delta_steps(unsafe=True)

def test(out='/mnt/data/spec_delta_4'):
    os.makedirs(out,exist_ok=True)
    labels=[
      # C0 makes a cache line Shared and readable.
      'core0:issue_1_line1',
      'core0:ask_read_line1',
      'l1::dir:start_rqR_c0',
      'l1::dir:grant_S_c0',
      'l1::net:deliver_grS_c0',
      'core0:complete_read_line1',
      'l1::dir:accept_gack_c0',
      # C0 begins an older read of line0.
      'core0:issue_1_line0',
      'core0:ask_read_line0',
      # C0 speculates on line1 (currently version 0).
      'core0:spec_execute_line1',
      # C1 writes line1, invalidating C0's copy.
      'core1:issue_2_line1',
      'core1:ask_write_line1',
      'l1::dir:start_rqW_c1',
      'l1::net:deliver_inv_c0',
      'l1::dir:accept_ack_c0',
      'l1::dir:grant_M_c1',
      'l1::net:deliver_grM_c1',
      'core1:complete_store_line1',
      # C0's earlier read of line0 finally completes.
      'l0::dir:start_rqR_c0',
      'l0::dir:grant_S_c0',
      'l0::net:deliver_grS_c0',
      'core0:complete_read_line0',
      # BUG: retire without checking if line1 was invalidated.
      'core0:spec_retire_line1_unsafe',
    ]
    bad=UnsafeSpeculativeSystem(4,2)
    conditions=[
      '(= (select payload_1 0) 0)',
      '(= (select payload_1 1) 99)',
      '(= s11__newval_1 99)',
      '(= s10__spec_version_0 0)',
      '(= s18__l1__latest 1)',
      '(not s22__busy_0)',
      '(= s23__observed_0 0)',
      '(= s23__l1__latest 1)',
      's23__bad',
    ]
    result=run_trace(bad,labels,conditions,os.path.join(out,'unsafe_speculation_counterexample.smt2'))
    # A corrected version of the *same* sequence is forced to replay.
    good=SpeculativeSystem(4,2)
    assert 'core0:spec_replay_line1' in dict(good.steps())
    goodlabels=labels[:-1]+['core0:spec_replay_line1']
    conditionsgood=[
      '(= (select payload_1 0) 0)',
      '(= (select payload_1 1) 99)',
      '(= s11__newval_1 99)',
      '(not s23__bad)',
      's23__busy_0',
      '(= s23__op_0 1)',
      '(= s23__target_0 1)',
    ]
    goodresult=run_trace(good,goodlabels,conditionsgood,
                         os.path.join(out,'safe_speculation_replay.smt2'))
    # Replay actually completes through MSI and reads the newer value.
    complete=goodlabels+[
      'l1::dir:accept_gack_c1',
      'core0:ask_read_line1',
      'l1::dir:start_rqR_c0',
      'l1::net:deliver_recall_c1',
      'l1::dir:accept_wb_c1',
      'l1::dir:grant_S_c0',
      'l1::net:deliver_grS_c0',
      'core0:complete_read_line1',
    ]
    end=len(complete)
    complete_result=run_trace(good,complete,[
      '(= (select payload_1 0) 0)',
      '(= (select payload_1 1) 99)',
      '(= s11__newval_1 99)',
      f'(= s{end}__observed_0 99)',
      f'(not s{end}__bad)',
      f'(not s{end}__busy_0)',
    ], os.path.join(out,'safe_replay_completion.smt2'))
    # No interfering write: the speculative hit retires successfully.
    fast_labels=[
      'core0:issue_1_line1', 'core0:ask_read_line1',
      'l1::dir:start_rqR_c0', 'l1::dir:grant_S_c0',
      'l1::net:deliver_grS_c0', 'core0:complete_read_line1',
      'l1::dir:accept_gack_c0',
      'core0:issue_1_line0', 'core0:ask_read_line0',
      'core0:spec_execute_line1',
      'l0::dir:start_rqR_c0', 'l0::dir:grant_S_c0',
      'l0::net:deliver_grS_c0', 'core0:complete_read_line0',
      'core0:spec_retire_line1',
    ]
    rfast=run_trace(good,fast_labels,[
      '(= (select payload_1 0) 13)',
      '(= s15__observed_0 13)',
      '(not s15__bad)',
      '(not s15__spec_active_0)'
    ],os.path.join(out,'safe_speculation_fast_retire.smt2'))
    results={'unsafe_validation_removed':result,'safe_replay':goodresult,
             'safe_speculative_retire':rfast,
             'safe_replay_completion':complete_result,
             'conclusion':'The same concurrent history is satisfiable, but the corrected design replays instead of retiring stale data.'}
    open(os.path.join(out,'witness_results.json'),'w').write(json.dumps(results,indent=2))
    return results

if __name__=='__main__':
    print(json.dumps(test(),indent=2))
