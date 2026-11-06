"""Regression tests for v1.9 minimized-directory liveness premise audit."""
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from directory_invariant_minimize import MinimizedDirectorySpec,TemporalFairSpec
from progress_v16_verify import (a,neg,z3_smt,invariant_queries, local_progress_queries,
    unconditional_no_terminal_stall_queries)
from temporal_v17_verify import lemmas
from fair_lasso_v17 import run_case


def unsat(m,formula):
    return z3_smt(m.declarations()+'\n(assert '+formula+')\n(check-sat)\n').strip().splitlines()[0]=='unsat'

class MinimizedTemporalProgressTests(unittest.TestCase):
    def test_minimized_model_has_identical_transitions(self):
        n,k=2,1
        full=TemporalFairSpec(n,k);reduced=MinimizedDirectorySpec(n,k)
        self.assertEqual(full.T(),reduced.T())
        self.assertEqual(full.init(),reduced.init())

    def test_equivalence_and_induction_small(self):
        m=MinimizedDirectorySpec(2,1);full=TemporalFairSpec(2,1)
        self.assertTrue(unsat(m,a(m.inv(),neg(full.inv()))))
        self.assertTrue(unsat(m,a(full.inv(),neg(m.inv()))))
        for formula in invariant_queries(m).values():self.assertTrue(unsat(m,formula))

    def test_progress_deadlock_and_temporal_premises_small(self):
        m=MinimizedDirectorySpec(2,1)
        for family in [local_progress_queries(m),unconditional_no_terminal_stall_queries(m),lemmas(m)]:
            for label,formula in family.items():
                with self.subTest(label=label):
                    self.assertTrue(unsat(m,formula))

    def test_fair_lasso_and_negative_controls(self):
        for n in (2,3):
            self.assertFalse(run_case(n)['fair_incomplete_lasso_exists'])
            self.assertTrue(run_case(n,unfair=True)['fair_incomplete_lasso_exists'])
            self.assertTrue(run_case(n,strong_completion=False)['fair_incomplete_lasso_exists'])

if __name__=='__main__':unittest.main()
