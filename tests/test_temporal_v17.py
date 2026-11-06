"""v1.7 regression tests for fair-path progress and negative controls."""
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from temporal_v17_verify import TemporalFairSpec,lemmas
from fair_lasso_v17 import run_case
from progress_v16_verify import FairProgressSpec
from cache_smt_verifier import a,o,neg,eq,z3_smt

class TemporalV17Tests(unittest.TestCase):
    def test_strengthened_speculative_invariant_is_really_inductive(self):
        m=TemporalFairSpec(2,1)
        from progress_v16_verify import invariant_queries
        for name,q in invariant_queries(m).items():
            with self.subTest(name=name):
                self.assertEqual(z3_smt(m.declarations()+'\n(assert '+q+')\n(check-sat)\n').strip().splitlines()[0],'unsat')

    def test_concrete_transition_progress_premises(self):
        m=TemporalFairSpec(2,1)
        for name,g in lemmas(m).items():
            with self.subTest(name=name):
                self.assertEqual(z3_smt(m.declarations()+'\n(assert '+g+')\n(check-sat)\n').strip().splitlines()[0],'unsat')

    def test_old_invariant_is_too_weak_for_confirmed_read_persistence(self):
        m=FairProgressSpec(2,1)
        steps=dict(m.steps());I=m.inv()
        settle=o(*(t for label,t in steps.items()
                   if label.startswith('core0:spec_retire_fast_') or label.startswith('core0:spec_replay_')))
        conf=a(m.x(0,'load_active'),m.x(0,'load_confirmed'))
        conf_next=a(m.x(0,'load_active',True),m.x(0,'load_confirmed',True))
        query=a(I,conf,m.T(),neg(settle),neg(conf_next))
        # A genuine SAT witness for inductive *strengthening*, not a reachable
        # execution counterexample.
        self.assertEqual(z3_smt(m.declarations()+'\n(assert '+query+')\n(check-sat)\n').strip().splitlines()[0],'sat')

    def test_abstract_fair_lasso_proofs_and_negative_controls(self):
        for n in (2,3,4):
            cases=[({},False),({'unfair':True},True),
                  ({'strong_completion':False},True),
                  ({'service_fair':False},True),
                  ({'start_fair':False},True)]
            for kw,expected in cases:
                with self.subTest(n=n,variant=kw):
                    self.assertEqual(run_case(n,**kw)['fair_incomplete_lasso_exists'],expected)

if __name__=='__main__':unittest.main()
