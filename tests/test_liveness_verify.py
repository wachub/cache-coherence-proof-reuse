"""Regression tests for local progress and intentionally reachable liveness defects.

These tests import the *unchanged* models; no transition definitions are edited.
"""
import json
import subprocess
import sys
import unittest
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import liveness_verify as lv


def solve(decls,formula):
    raw=lv.z3_smt(decls+'\n(assert '+formula+')\n(check-sat)\n').strip()
    return raw.splitlines()[0] if raw else 'error'


class ProgressProofTests(unittest.TestCase):
    def test_four_core_transaction_progress_rank_and_enabling(self):
        dec,goals,_=lv.protocol_obligations(4)
        self.assertEqual(len(goals),7)
        for label,formula in goals.items():
            with self.subTest(label=label):
                self.assertEqual(solve(dec,formula),'unsat')

    def test_four_core_speculative_frontend_progress(self):
        for lines in (2,3):
            dec,goals,_=lv.frontend_obligations(4,lines)
            self.assertEqual(len(goals),12)
            for label,formula in goals.items():
                with self.subTest(lines=lines,label=label):
                    self.assertEqual(solve(dec,formula),'unsat')

    def test_conditional_no_terminal_stall_both_configurations(self):
        for lines in (2,3):
            dec,goals,_=lv.combined_no_terminal_stall_obligation(4,lines)
            for label,formula in goals.items():
                with self.subTest(lines=lines,label=label):
                    self.assertEqual(solve(dec,formula),'unsat')

    def test_rank_is_framed_by_other_lines_and_frontends(self):
        for lines in (2,3):
            dec,goals,_=lv.rank_frame_obligations(4,lines)
            self.assertEqual(len(goals),lines)
            for label,formula in goals.items():
                with self.subTest(lines=lines,label=label):
                    self.assertEqual(solve(dec,formula),'unsat')

    def test_negative_controls_are_sat(self):
        dec,goals=lv.protocol_negative_controls(4)
        for label,formula in goals.items():
            with self.subTest(label=label):
                self.assertEqual(solve(dec,formula),'sat')

    def test_symbolic_payload_stall_is_reachable(self):
        text,path=lv.bmc_reachable_data_stall(4,2)
        self.assertEqual(len(path),6)
        self.assertEqual(lv.z3_smt(text).strip().splitlines()[0],'sat')

    def test_combined_four_core_starvation_lasso_is_reachable(self):
        for lines in (2,3):
            text,prefix,cycle=lv.combined_starvation_lasso(4,lines)
            self.assertEqual(len(prefix),18)
            self.assertEqual(len(cycle),18)
            with self.subTest(lines=lines):
                self.assertEqual(lv.z3_smt(text).strip().splitlines()[0],'sat')

    def test_weak_fair_starvation_lasso_is_reachable(self):
        text,prefix,cycle=lv.starvation_lasso_weak_fairness()
        self.assertEqual(len(prefix),13)
        self.assertEqual(len(cycle),14)
        self.assertEqual(lv.z3_smt(text).strip().splitlines()[0],'sat')


if __name__=='__main__':unittest.main()
