#!/usr/bin/env python3
"""Bounded executions demonstrating legal speculation and bad mutations."""
import json, os, sys
from speculative_store_delta import SpecStore, a, o, neg, z3_smt
from sc_msi_trace_witness import run_trace

class Mutant(SpecStore):
    def __init__(self,*args,kind=None,**kwargs):
        self.kind=kind
        super().__init__(*args,**kwargs)
    def steps(self):
        return self.inherited_steps()+self.delta_steps(
          unsafe_second_first=self.kind=='out_of_order',
          unsafe_unresolved=self.kind=='unresolved')

def main():
    path=os.path.join(os.path.dirname(__file__),'witness_smt')
    os.makedirs(path,exist_ok=True)
    s=SpecStore(2,2)
    good=[
     'core0:stage_slot0_line0',
     'core0:stage_slot1_line1',
     'core0:confirm',
     'core0:retire_head_line0',
     'core0:ask_write_line0',
     'l0::dir:start_rqW_c0','l0::dir:grant_M_c0','l0::net:deliver_grM_c0',
     'core0:complete_store_line0','l0::dir:accept_gack_c0',
     'core0:retire_head_line1',
     'core0:ask_write_line1',
     'l1::dir:start_rqW_c0','l1::dir:grant_M_c0','l1::net:deliver_grM_c0',
     'core0:complete_store_line1','l1::dir:accept_gack_c0',
     'core1:issue_1_line0','core1:ask_read_line0',
     'l0::dir:start_rqR_c1','l0::net:deliver_recall_c0','l0::dir:accept_wb_c0',
     'l0::dir:grant_S_c1','l0::net:deliver_grS_c1','core1:complete_read_line0',
     'l0::dir:accept_gack_c1',
     'core1:issue_1_line1','core1:ask_read_line1',
     'l1::dir:start_rqR_c1','l1::net:deliver_recall_c0','l1::dir:accept_wb_c0',
     'l1::dir:grant_S_c1','l1::net:deliver_grS_c1','core1:complete_read_line1',
    ]
    r1=run_trace(s,good,[
      '(= s1__sq_value0_0 11)','(= s2__sq_value1_0 22)',
      '(= s25__observed_1 11)',
      '(= s34__observed_1 22)',
      '(= s34__ref_0 1)','(= s34__ref_1 1)',
    ],os.path.join(path,'good_two_speculative_stores.smt2'))

    s0=SpecStore(2,2)
    squashed=[
       'core0:stage_slot0_line0',
       'core0:squash_unconfirmed',
       'core1:issue_1_line0','core1:ask_read_line0',
       'l0::dir:start_rqR_c1','l0::dir:grant_S_c1','l0::net:deliver_grS_c1',
       'core1:complete_read_line0'
    ]
    r2=run_trace(s0,squashed,[
      '(= s1__sq_value0_0 77)',
      '(= s8__observed_1 0)',
      '(= s8__ref_0 0)',
    ],os.path.join(path,'good_squash_no_memory_effect.smt2'))

    b=Mutant(2,2,kind='out_of_order')
    bad=[
       'core0:stage_slot0_line0',
       'core0:stage_slot1_line1',
       'core0:confirm',
       'core0:BUG_retire_tail_first_line1',
       'core0:ask_write_line1',
       'l1::dir:start_rqW_c0','l1::dir:grant_M_c0','l1::net:deliver_grM_c0',
       'core0:complete_store_line1','l1::dir:accept_gack_c0',
       'core1:issue_1_line1','core1:ask_read_line1',
       'l1::dir:start_rqR_c1','l1::net:deliver_recall_c0','l1::dir:accept_wb_c0',
       'l1::dir:grant_S_c1','l1::net:deliver_grS_c1','core1:complete_read_line1',
       'l1::dir:accept_gack_c1',
       'core1:issue_1_line0','core1:ask_read_line0',
       'l0::dir:start_rqR_c1','l0::dir:grant_S_c1','l0::net:deliver_grS_c1',
       'core1:complete_read_line0'
    ]
    r3=run_trace(b,bad,[
      '(= s1__sq_value0_0 11)','(= s2__sq_value1_0 22)',
      '(= s18__observed_1 22)',
      '(= s25__observed_1 0)',
      '(= s25__ref_0 0)','(= s25__ref_1 1)',
    ],os.path.join(path,'BUG_out_of_order_observed.smt2'))

    # Also verify the unsound branch-store issue can happen in a reachable run.
    u=Mutant(2,2,kind='unresolved')
    leak=[
        'core0:stage_slot0_line0','core0:BUG_retire_unresolved_line0',
        'core0:ask_write_line0','l0::dir:start_rqW_c0','l0::dir:grant_M_c0',
        'l0::net:deliver_grM_c0','core0:complete_store_line0','l0::dir:accept_gack_c0',
        'core1:issue_1_line0','core1:ask_read_line0',
        'l0::dir:start_rqR_c1','l0::net:deliver_recall_c0',
        'l0::dir:accept_wb_c0','l0::dir:grant_S_c1',
        'l0::net:deliver_grS_c1','core1:complete_read_line0'
    ]
    r4=run_trace(u,leak,[
         '(= s1__sq_value0_0 77)',
         '(= s16__observed_1 77)',
         '(= s16__ref_0 1)'
    ],os.path.join(path,'BUG_unresolved_store_visible.smt2'))
    results={'good_confirmed_fifo':r1,'good_squashed':r2,
             'bad_out_of_order':r3,'bad_unresolved_visible':r4}
    with open(os.path.join(path,'results.json'),'w') as f:json.dump(results,f,indent=2)
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
