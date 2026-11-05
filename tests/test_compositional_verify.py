"""Tests for compositional verification, no changes to cache model source."""
from collections import OrderedDict
from pathlib import Path
import json
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import compositional_verify as cv
from fast_verify import solve_goals


class CompositionalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.model = cv.load_combined(4,2)
        cls.prelude,cls.goals,cls.families,cls.contracts,cls.groups = cv.build_layers(cls.model)

    def test_partition_all_actions_no_implicit_symmetry(self):
        original=[label for label,_ in self.model.delta_steps()]
        grouped=[label for actions in self.families.values() for label,_ in actions]
        self.assertCountEqual(original,grouped)
        self.assertEqual(len(original),76)
        self.assertEqual(len(set(original)),len(original))
        self.assertEqual(set(self.families),set(cv.FAMILIES))
        for lab in original:
            self.assertTrue(lab.startswith('core'))
        with self.assertRaises(ValueError):
            cv.family_of('core0:new_unclassified_action')

    def test_full_contract_checks_unsat(self):
        contexts=cv.sliced_contexts(self.model,self.goals,self.groups)
        result=cv.solve_sliced(contexts,self.goals,cache_dir=None)
        self.assertTrue(result['passed'])
        self.assertEqual(len(self.goals),29)
        self.assertGreater(result['solver_contexts'],1)
        self.assertTrue(all(x['status']=='unsat' for x in result['goals'].values()))

    def test_typed_contracts_detect_all_mutants(self):
        result=cv.mutant_contract_tests(self.model)
        self.assertTrue(result['detected'])
        self.assertEqual(set(result['goals']),{'unvalidated_read','premature_read',
                                               'stuttering_store_issue'})

    def test_sliced_proof_context_has_no_unrelated_family(self):
        contexts=cv.sliced_contexts(self.model,self.goals,self.groups)
        store=contexts['store_issue__satisfies_typed_contract']
        load=contexts['load_retire__satisfies_typed_contract']
        self.assertIn('(define-fun delta_store_issue',store)
        self.assertNotIn('(define-fun delta_load_retire',store)
        self.assertNotIn('(define-fun contract_load_retire',store)
        self.assertIn('(define-fun delta_load_retire',load)
        self.assertNotIn('(define-fun delta_store_issue',load)
        # Hypothetical *new* read-retirement transition, injected into a
        # verifier test subclass only. The production cache model is untouched.
        class ExtraReadRetirement(type(self.model)):
            def delta_steps(self,mutant=None):
                orig=super().delta_steps(mutant=mutant)
                return orig+[self.step('core0:spec_retire_fast_extra_line0',
                                        '(= spec_qlen_0 7)',{})]
        future=ExtraReadRetirement(4,2)
        _,later_goals,_,_,later_groups=cv.build_layers(future)
        later_contexts=cv.sliced_contexts(future,later_goals,later_groups)
        from fast_verify import proof_cache_key,z3_version
        store_name='store_issue__satisfies_typed_contract'
        load_name='load_retire__satisfies_typed_contract'
        self.assertEqual(contexts[store_name],later_contexts[store_name])
        self.assertEqual(self.goals[store_name],later_goals[store_name])
        self.assertNotEqual(contexts[load_name],later_contexts[load_name])
        self.assertEqual(proof_cache_key(contexts[store_name],self.goals[store_name],0,0,z3_version()),
                         proof_cache_key(later_contexts[store_name],later_goals[store_name],0,0,z3_version()))
        self.assertNotEqual(proof_cache_key(contexts[load_name],self.goals[load_name],0,0,z3_version()),
                            proof_cache_key(later_contexts[load_name],later_goals[load_name],0,0,z3_version()))

    def test_bundle_manifest_tracks_exact_hashes(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest=Path(tmp)
            manifest=cv.write_bundle(dest,self.model,self.prelude,
                                     self.goals,self.families,self.groups)
            self.assertEqual(len(manifest['goals']),29)
            self.assertEqual(manifest['configuration']['cores'],4)
            self.assertEqual(sum(x['count'] for x in manifest['transition_families'].values()),76)
            for path in cv.MODEL_FILES:
                self.assertEqual(manifest['source_hashes'][str(path.relative_to(ROOT))],
                                 cv._file_hash(path))
            self.assertTrue((dest/'all_contract_queries.smt2').is_file())
            self.assertTrue((dest/'sliced_queries'/'store_issue__satisfies_typed_contract.smt2').is_file())
            # All partial scripts are independent complete SMT-LIB2 queries.
            one=(dest/'sliced_queries'/'store_issue__satisfies_typed_contract.smt2').read_text()
            from fast_verify import eval_z3
            self.assertEqual(eval_z3(one).strip(),'unsat')


if __name__=='__main__':
    unittest.main()
