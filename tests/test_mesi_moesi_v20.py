"""Fast independent checks for the v2.0 MESI/MOESI abstraction."""
from __future__ import annotations
import tempfile,unittest,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/12_mesi_moesi'))
sys.path.insert(0,str(ROOT/'tools'))
from extended_system import ExtendedFairSpec
from verify_mesi_moesi_v20 import checks
from verify_extended_progress_v20 import goals as progress_goals
from cache_smt_verifier import z3_smt
from witnesses import run as witness_run
from negative_controls import run as negative_run

class MesiMoesiV20Tests(unittest.TestCase):
    def test_inductive_safety_and_speculation(self):
        with tempfile.TemporaryDirectory() as td:
            for variant in ('MESI','MOESI'):
                with self.subTest(variant=variant):
                    m=ExtendedFairSpec(2,1,variant)
                    results=checks(m,Path(td)/variant)
                    self.assertTrue(all(x['passed'] for x in results),results)
    def test_live_E_and_O_reachability(self):
        with tempfile.TemporaryDirectory() as td:self.assertTrue(witness_run(td))
    def test_negative_controls(self):
        with tempfile.TemporaryDirectory() as td:self.assertTrue(negative_run(td))
    def test_no_terminal_stall_premise(self):
        for variant in ('MESI','MOESI'):
            m=ExtendedFairSpec(2,1,variant)
            for name in ('global_no_terminal_stall_enabledness',
                         'line0_some_service_guard_stable_without_service'):
                with self.subTest(variant=variant,goal=name):
                    formula=progress_goals(m)[name]
                    query=m.declarations()+'\n(assert '+formula+')\n(check-sat)\n'
                    self.assertEqual(z3_smt(query).strip().splitlines()[0],'unsat')
if __name__=='__main__':unittest.main()
