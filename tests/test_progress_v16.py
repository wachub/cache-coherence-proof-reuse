"""Focused v1.6 new semantics / negative controls; old tests remain intact."""
import sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from progress_v16_verify import generic_rr_arithmetic,generic_transaction_rank_arithmetic,invariant_queries,unconditional_no_terminal_stall_queries
from progress_v16_witnesses import repaired_arbitrary_write,starving_queued_core_lasso
from fair_progress_model import FairProgressSpec
from cache_smt_verifier import z3_smt


def check(d,q):
    return z3_smt(d+'\n(assert '+q+')\n(check-sat)\n').strip().splitlines()[0]

class ProgressV16Tests(unittest.TestCase):
    def test_symbolic_n_rr_and_transaction_rank(self):
        for mk in (generic_rr_arithmetic,generic_transaction_rank_arithmetic):
            decl,goals=mk()
            for name,goal in goals.items():
                with self.subTest(kind=mk.__name__,name=name):
                    self.assertEqual(check(decl,goal),'unsat')

    def test_revised_four_core_inductive_invariant(self):
        for lines in (2,3):
            m=FairProgressSpec(4,lines)
            for name,goal in invariant_queries(m).items():
                with self.subTest(lines=lines,obligation=name):
                    self.assertEqual(check(m.declarations(),goal),'unsat')

    def test_global_no_terminal_stall_without_payload_assumptions(self):
        for lines in (2,3):
            m=FairProgressSpec(4,lines)
            for name,goal in unconditional_no_terminal_stall_queries(m).items():
                with self.subTest(lines=lines,name=name):
                    self.assertEqual(check(m.declarations(),goal),'unsat')

    def test_arbitrary_write_value_really_reachable(self):
        self.assertEqual(z3_smt(repaired_arbitrary_write()[0]).strip().splitlines()[0],'sat')

    def test_old_starvation_trace_excluded_but_unfair_mutant_admits_it(self):
        self.assertEqual(z3_smt(starving_queued_core_lasso(False)[0]).strip().splitlines()[0],'unsat')
        self.assertEqual(z3_smt(starving_queued_core_lasso(True)[0]).strip().splitlines()[0],'sat')

if __name__=='__main__':unittest.main()
