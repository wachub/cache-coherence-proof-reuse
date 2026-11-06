"""Regression tests for v2.1 atomic hierarchy and proof checkers."""
from __future__ import annotations
import json,sys,tempfile,unittest,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/13_hierarchy'))
sys.path.insert(0,str(ROOT/'experiments/09_combined_speculative_reads_writes'))
sys.path.insert(0,str(ROOT/'tools'))
from hierarchy import Hierarchy,Topology,AND,NOT
from cache_smt_verifier import z3_smt
from verify_hierarchy_equivalence_v21 import check_pair as compare_shape
from verify_width_extension_v21 import check_pair as extend_width
from verify_hierarchy_progress_v21 import verify as check_progress
_ws=importlib.util.spec_from_file_location('hierarchy_v21_witnesses',ROOT/'experiments/13_hierarchy/witnesses.py')
_wm=importlib.util.module_from_spec(_ws);_ws.loader.exec_module(_wm)
witnesses=_wm.run

class HierarchyV21Tests(unittest.TestCase):
    def z3(self,m,expr):
        return z3_smt(m.declarations()+'\n(assert '+expr+')\n(check-sat)\n').strip().splitlines()[0]
    def test_independent_topology_levels(self):
        for fs,n,nodes in [((4,),4,1),((2,2),4,3),((2,4),8,3),
                           ((4,2),8,5),((2,2,2),8,7)]:
            t=Topology(fs)
            self.assertEqual((t.leaves,len(t.nodes)),(n,nodes))
            self.assertEqual(set(t.leaf_paths),set(range(n)))
            self.assertTrue(all(path[0]==t.root for path in t.leaf_paths.values()))
    def test_interface_is_topology_independent(self):
        shapes=[Hierarchy((4,),'MESI'),Hierarchy((2,2),'MOESI'),Hierarchy((2,2,2),'MSI')]
        self.assertEqual(len({str(x.interface_signature()) for x in shapes}),1)
    def test_concrete_small_inductive_safety(self):
        for protocol in ('MSI','MESI','MOESI'):
            m=Hierarchy((2,),protocol)
            self.assertEqual(self.z3(m,AND(m.init(),NOT(m.invariant()))),'unsat')
            for _,step in m.steps():
                self.assertEqual(self.z3(m,AND(m.invariant(),step,NOT(m.invariant(True)))),'unsat')
    def test_reachable_features_and_negative_controls(self):
        with tempfile.TemporaryDirectory() as d:
            results=witnesses(Path(d))
            self.assertTrue(results['passed'])
            self.assertEqual(len(results['checks']),7)
    def test_pairwise_shape_refinement(self):
        with tempfile.TemporaryDirectory() as d:
            x=compare_shape([2],[1,2],'MOESI',Path(d))
            self.assertTrue(x['passed'])
    def test_width_extension(self):
        with tempfile.TemporaryDirectory() as d:
            x=extend_width([2],[3],'MESI',Path(d))
            self.assertTrue(x['pass'])
    def test_service_progress(self):
        with tempfile.TemporaryDirectory() as d:
            x=check_progress([2],'MOESI',Path(d))
            self.assertTrue(x['passed'])

if __name__=='__main__':unittest.main()
