#!/usr/bin/env python3
"""Executable concrete-path witnesses, including two deliberately broken mutants."""
import json, os
from combined_speculative_model import CombinedSpec
from sc_msi_trace_witness import run_trace

class Mutant(CombinedSpec):
    def __init__(self, cores=4, lines=2, mutant=None):
        self.mutant=mutant
        super().__init__(cores=cores,lines=lines)
    def steps(self):return self.inherited_steps()+self.delta_steps(mutant=self.mutant)

def check(s, name, labels, constraints, out):
    last=len(labels)
    assertions=[]
    for expr in constraints:
        assertions.append(expr.replace('__LAST__',f's{last}__'))
    return run_trace(s,labels,assertions,os.path.join(out,name+'.smt2'))

def main(out_dir=None):
    out_dir=out_dir or os.path.join(os.path.dirname(__file__),'witness_smt')
    os.makedirs(out_dir,exist_ok=True)
    s=CombinedSpec(4,2)
    # Most recent same-line store wins: A=11; A=22; speculative R(A)->22.
    forward_twice=[
        'core0:stage0_line0','core0:stage1_line0',
        'core0:spec_forward_slot1_line0', 'core0:confirm',
        'core0:issue_confirmed_store_line0','core0:ask_write_line0',
        'l0::dir:start_rqW_c0','l0::dir:grant_M_c0','l0::net:deliver_grM_c0',
        'core0:complete_store_line0','l0::dir:accept_gack_c0',
        'core0:issue_confirmed_store_line0', 'core0:complete_store_line0',
        'core0:spec_retire_fast_line0'
    ]
    results={}
    results['two_same_line_stores_forward_youngest']=check(s,'two_same_line_stores_forward_youngest',forward_twice,[
        '(= s1__spec_value0_0 11)','(= s2__spec_value1_0 22)',
        '(= s3__spec_load_value_0 22)', '(= __LAST__observed_0 22)',
        '(= __LAST__ref_0 2)','(not __LAST__spec_load_active_0)'
    ],out_dir)
    # A then B, followed by read A; read does not skip the A store.
    forward_cross=[
        'core0:stage0_line0','core0:stage1_line1',
        'core0:spec_forward_slot0_line0','core0:confirm',
        'core0:issue_confirmed_store_line0','core0:ask_write_line0',
        'l0::dir:start_rqW_c0','l0::dir:grant_M_c0','l0::net:deliver_grM_c0',
        'core0:complete_store_line0','l0::dir:accept_gack_c0',
        'core0:issue_confirmed_store_line1','core0:ask_write_line1',
        'l1::dir:start_rqW_c0','l1::dir:grant_M_c0','l1::net:deliver_grM_c0',
        'core0:complete_store_line1','l1::dir:accept_gack_c0',
        'core0:spec_retire_fast_line0'
    ]
    results['two_different_line_stores_forward_oldest_matching']=check(s,'two_different_line_stores_forward_oldest_matching',forward_cross,[
        '(= s1__spec_value0_0 11)','(= s2__spec_value1_0 22)',
        '(= s3__spec_load_value_0 11)', '(= __LAST__observed_0 11)',
        '(= __LAST__ref_0 1)','(= __LAST__ref_1 1)'
    ],out_dir)
    # On a wrong branch, neither the unconfirmed store nor the younger read leaks.
    squash=[
        'core0:stage0_line0','core0:spec_forward_slot0_line0',
        'core0:squash_suffix', 'core1:issue_1_line0','core1:ask_read_line0',
        'l0::dir:start_rqR_c1','l0::dir:grant_S_c1','l0::net:deliver_grS_c1',
        'core1:complete_read_line0'
    ]
    results['squash_store_and_younger_read']=check(s,'squash_store_and_younger_read',squash,[
        '(= s1__spec_value0_0 77)', '(= __LAST__observed_1 0)',
        '(= __LAST__ref_0 0)','(not __LAST__spec_load_active_0)'
    ],out_dir)
    # Core 1 overwrites the line before Core 0 retires the forwarded read.
    stale=[
        'core0:stage0_line0','core0:spec_forward_slot0_line0','core0:confirm',
        'core0:issue_confirmed_store_line0','core0:ask_write_line0',
        'l0::dir:start_rqW_c0','l0::dir:grant_M_c0','l0::net:deliver_grM_c0',
        'core0:complete_store_line0','l0::dir:accept_gack_c0',
        'core1:issue_2_line0','core1:ask_write_line0',
        'l0::dir:start_rqW_c1','l0::net:deliver_recall_c0',
        'l0::dir:accept_wb_c0','l0::dir:grant_M_c1',
        'l0::net:deliver_grM_c1','core1:complete_store_line0',
        'l0::dir:accept_gack_c1'
    ]
    good_replay=stale+[
        'core0:spec_replay_line0','core0:ask_read_line0',
        'l0::dir:start_rqR_c0','l0::net:deliver_recall_c1',
        'l0::dir:accept_wb_c1','l0::dir:grant_S_c0',
        'l0::net:deliver_grS_c0','core0:complete_read_line0'
    ]
    results['stale_forward_replayed_to_current_value']=check(s,'stale_forward_replayed_to_current_value',good_replay,[
        '(= s1__spec_value0_0 11)','(= s11__newval_1 77)',
        '(= __LAST__observed_0 77)','(= __LAST__ref_0 2)'
    ],out_dir)
    bad=Mutant(4,2,mutant='unvalidated_read')
    stale_bad=stale+['core0:spec_retire_fast_line0']
    results['BUG_stale_forward_without_validation']=check(bad,'BUG_stale_forward_without_validation',stale_bad,[
        '(= s1__spec_value0_0 11)','(= s11__newval_1 77)',
        '(= __LAST__observed_0 11)','(= (select payload_0 __LAST__ref_0) 77)'
    ],out_dir)
    # Spec read from an already cached line B while an older write to A is
    # still queued. Mutant may retire the read too early.
    prem=[
        'core0:issue_1_line1','core0:ask_read_line1',
        'l1::dir:start_rqR_c0','l1::dir:grant_S_c0',
        'l1::net:deliver_grS_c0','core0:complete_read_line1',
        'l1::dir:accept_gack_c0',
        'core0:stage0_line0','core0:spec_cache_line1',
        'core0:confirm','core0:spec_retire_fast_line1'
    ]
    badprem=Mutant(4,2,mutant='premature_read')
    results['BUG_read_retires_with_older_store_queued']=check(badprem,'BUG_read_retires_with_older_store_queued',prem,[
        '(= s8__spec_value0_0 77)','(= __LAST__observed_0 0)',
        '(= __LAST__spec_qlen_0 1)'
    ],out_dir)
    with open(os.path.join(out_dir,'results.json'),'w') as f:json.dump(results,f,indent=2)
    print(json.dumps({name:{'result':v['result'],'events':len(v['events']),'seconds':v['seconds']}
                      for name,v in results.items()},indent=2))
    return results
if __name__=='__main__':main()
