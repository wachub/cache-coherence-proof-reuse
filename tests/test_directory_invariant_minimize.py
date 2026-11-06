"""Tests for v1.8 purely logical, grouped minimization experiment."""
import sys
import tempfile
import unittest
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from directory_invariant_minimize import (DIRECTORY,TemporalFairSpec,
    indexed_terms,invariant_without,clauses_by_schema,minimize_one,query)
from cache_smt_verifier import a,neg

class DirectoryInvariantMinimizationTests(unittest.TestCase):
    def test_grouping_covers_every_core_and_line(self):
        m=TemporalFairSpec(4,2)
        terms=indexed_terms(m)
        self.assertEqual(len(terms),140)
        self.assertEqual(sum(1 for name,_ in terms if name=='C22'),4)
        self.assertEqual(len(DIRECTORY),35)
        self.assertEqual(clauses_by_schema(m,{'C22'}).count('not (and'),8)

    def test_no_change_is_exactly_original_invariant(self):
        m=TemporalFairSpec(2,1)
        self.assertEqual(invariant_without(m,set()),m.inv())
        self.assertEqual(invariant_without(m,set(),True),m.inv(True))

    def test_group_redundancy_and_independence(self):
        m=TemporalFairSpec(2,1)
        for name,expected in [('C22','unsat'),('G07','unsat'),('G06','sat'),('C16','sat')]:
            candidate=invariant_without(m,{name})
            status,_=query(m,a(candidate,neg(clauses_by_schema(m,{name}))),10000)
            self.assertEqual(status['status'],expected,name)

    def test_complete_minimized_inductive_invariant(self):
        with tempfile.TemporaryDirectory() as d:
            result=minimize_one(2,1,Path(d),10000)
            self.assertEqual(len(result['removed']),10)
            self.assertEqual(result['inductive_step']['status'],'unsat')
            self.assertEqual(result['reduced_implies_all_removed']['status'],'unsat')
            self.assertEqual(result['other_invariants_imply_all_directory_clauses']['status'],'sat')

if __name__=='__main__': unittest.main()
