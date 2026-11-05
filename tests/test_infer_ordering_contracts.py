"""Actual solver regressions for automatically inferred event-level contracts."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import infer_ordering_contracts as ic
from fast_verify import load_combined, eval_z3

EXPECTED={
    'store_stage':['stutter'],
    'resolve_speculation':['stutter'],
    'store_issue':['issue_store'],
    'load_forward':['stutter'],
    'load_cache_capture':['stutter'],
    'load_retire':['retire_read'],
    'load_replay':['replay_read'],
}

class InferContractsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.model=load_combined(4,2)
        cls.report=ic.prove_contracts(cls.model,cache_dir=None)

    def test_inferred_all_families_and_oracle_equivalence(self):
        self.assertTrue(self.report['all_passed'])
        self.assertEqual(set(self.report['families']),set(EXPECTED))
        for name,events in EXPECTED.items():
            proof=self.report['families'][name]
            self.assertEqual(proof['selected_events'],events)
            self.assertEqual(proof['grammar_coverage']['status'],'unsat')
            self.assertEqual(proof['feasibility']['status'],'sat')
            self.assertEqual(proof['final_coverage']['status'],'unsat')
            self.assertTrue(proof['oracle']['equivalent_under_invariants'])

    def test_export_independently_checkable_smtlib(self):
        with tempfile.TemporaryDirectory() as td:
            folder=Path(td)
            report=ic.write_proof_bundle(folder,self.model,self.report)
            self.assertEqual(report['format'],'smt-inferred-contracts-v1')
            self.assertEqual(len(list(folder.glob('*_coverage.smt2'))),7)
            one=(folder/'load_retire_coverage.smt2').read_text()
            self.assertEqual(eval_z3(one).strip(),'unsat')
            self.assertIn('shared_abstraction_sha256',report)

    def test_exact_reuse_and_localized_changed_transition(self):
        old=ic.write_proof_bundle(Path(tempfile.mkdtemp()),self.model,self.report)
        again=ic.prove_contracts(self.model,cache_dir=None,
                                  previous_manifest=old,compare_handwritten=False)
        self.assertTrue(all(f['reuse_assessment']['status']=='unchanged_exact_certificate'
                            for f in again['families'].values()))
        base=type(self.model)
        class ExtraValidRetire(base):
            def delta_steps(self,mutant=None):
                steps=list(super().delta_steps(mutant=mutant))
                label,transition=next((l,t) for l,t in steps
                                      if l=='core0:spec_retire_fast_line0')
                # Redundant but feasible new transition to model a localized
                # future branch. No actual production model changes.
                steps.append(('core0:spec_retire_fast_extra_line0',transition))
                return steps
        changed=ExtraValidRetire(4,2)
        newer=ic.prove_contracts(changed,cache_dir=None,
                                 previous_manifest=old,compare_handwritten=False)
        for family,result in newer['families'].items():
            kind=result['reuse_assessment']['status']
            self.assertEqual(kind,
                'changed_family_reverified_compatible' if family=='load_retire'
                else 'unchanged_exact_certificate')

    def test_bad_retirement_mutants_fail_coverage(self):
        base=type(self.model)
        for bad in ('unvalidated_read','premature_read'):
            with self.subTest(mutant=bad):
                class BadRetirement(base):
                    def delta_steps(self,mutant=None):
                        originals=super().delta_steps(mutant=None)
                        bad_only=dict(super().delta_steps(mutant=bad))
                        # Keep replay transitions: built-in mutants omit them
                        # as a convenience for their original witness scripts.
                        return [(lab,bad_only.get(lab,step)) for lab,step in originals]
                model=BadRetirement(4,2)
                with self.assertRaisesRegex(RuntimeError,'effect vocabulary is incomplete'):
                    ic.prove_contracts(model,cache_dir=None,compare_handwritten=False)

    def test_stuttering_store_issue_rejected_by_previous_contract(self):
        base=type(self.model)
        old=ic.write_proof_bundle(Path(tempfile.mkdtemp()),self.model,self.report)
        class BadStoreIssue(base):
            def delta_steps(self,mutant=None):
                from sc_msi_4core_verifier import a,eq,neg
                steps=list(super().delta_steps(mutant=mutant))
                # Replaces one real issue with an abstract architectural
                # stutter while draining a queue entry, i.e. a lost write.
                bad=self.step('core0:issue_confirmed_store_line0',
                    a(eq(self.x(0,'qlen'),'1'),eq(self.x(0,'ready'),'1'),
                      neg(self.cpu(0,'busy'))),
                    {'spec_qlen_0':'0','spec_ready_0':'0'})
                return [(l,bad[1] if l==bad[0] else f) for l,f in steps]
        with self.assertRaisesRegex(RuntimeError,'weakens a previously'):
            ic.prove_contracts(BadStoreIssue(4,2),cache_dir=None,
                               previous_manifest=old,compare_handwritten=False)

    def test_incompatible_shared_assumptions_fail_closed(self):
        old=ic.write_proof_bundle(Path(tempfile.mkdtemp()),self.model,self.report)
        old['shared_abstraction_sha256']='not-the-same-invariants'
        with self.assertRaisesRegex(ValueError,'Shared state declarations'):
            ic.prove_contracts(self.model,cache_dir=None,
                               previous_manifest=old,compare_handwritten=False)

if __name__=='__main__': unittest.main()
