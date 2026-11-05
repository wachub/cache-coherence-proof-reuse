"""Regression tests for solver reuse (unittest, no pytest dependency)."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import fast_verify as fv

class FastVerifyTests(unittest.TestCase):
    def test_batch_isolated_agree_and_no_push_leak(self):
        # SAT/UNSAT/SAT in the SAME context catches forgotten pop(s).
        decl='(declare-const x Int)'
        goals={'one':'(= x 1)', 'impossible':'(and (= x 1) (= x 2))',
               'two':'(= x 2)'}
        a=fv.solve_goals(decl,goals,cache_dir=None,mode='batch')
        b=fv.solve_goals(decl,goals,cache_dir=None,mode='isolated')
        self.assertEqual({k:v['status'] for k,v in a['goals'].items()},
                         {k:v['status'] for k,v in b['goals'].items()})
        self.assertEqual([v['status'] for v in a['goals'].values()],
                         ['sat','unsat','sat'])

    def test_cache_keys_include_semantics_and_options(self):
        with tempfile.TemporaryDirectory() as folder:
            d=Path(folder)
            g={'a':'(= x 1)','b':'(and (= x 1) (= x 2))'}
            first=fv.solve_goals('(declare-const x Int)',g,cache_dir=d)
            second=fv.solve_goals('(declare-const x Int)',g,cache_dir=d)
            self.assertEqual(first['cache_hits'],0)
            self.assertEqual(second['cache_hits'],2)
            changed=fv.solve_goals('(declare-const x Int)',{'a':'(= x 3)'},cache_dir=d)
            self.assertEqual(changed['cache_hits'],0)
            another_seed=fv.solve_goals('(declare-const x Int)',g,cache_dir=d,seed=1)
            self.assertEqual(another_seed['cache_hits'],0)

    def test_full_four_core_delta_and_mutant_sensitivity(self):
        model=fv.load_combined(4,2)
        results=fv.solve_goals(model.declarations(),model.proof_goals(),cache_dir=None)
        self.assertTrue(results['passed'])
        self.assertEqual(len(results['goals']),7)
        self.assertTrue(fv.mutant_sensitivity(model)['detected'])

    def test_failed_interface_localizes_bad_retirement(self):
        regular=fv.load_combined(4,2)
        class Broken(type(regular)):
            def delta_steps(self,mutant=None):
                return super().delta_steps(mutant='premature_read')
        model=Broken(4,2)
        result=fv.solve_goals(model.declarations(),
                              {'interface':model.proof_goals()['new_transition_obeys_interface']},
                              cache_dir=None)
        self.assertEqual(result['goals']['interface']['status'],'sat')
        report=fv.failure_localization(model,['new_transition_obeys_interface'],
                                        timeout_ms=0,seed=0)
        self.assertTrue(report['new_transition_obeys_interface']['complete'])
        self.assertTrue(any('spec_retire_fast' in name for name in
                 report['new_transition_obeys_interface']['sat_schemas']))

    def test_generated_queries_unchanged(self):
        model=fv.load_combined(4,2)
        folder=ROOT/'experiments'/'09_combined_speculative_reads_writes'/'smt_delta_4_2'
        for name,goal in model.proof_goals().items():
            actual=model.declarations()+'\n(assert '+goal+')\n(check-sat)\n'
            self.assertEqual(actual,(folder/(name+'.smt2')).read_text(),name)

if __name__=='__main__': unittest.main()
