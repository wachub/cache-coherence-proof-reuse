from cache_smt_verifier import Protocol,check,z3_smt
from cache_bmc import run_bmc
import pytest

@pytest.mark.parametrize('n',[2,3,4,8])
def test_unbounded_safety(n):
    r=check(n,None)
    assert r['unbounded_depth_proof'],r
    assert all(x['result']=='unsat' for x in r['checks'].values())

def test_mutation_breaks_inductive_proof():
    r=check(2,None,early_grant=True)
    assert not r['unbounded_depth_proof']
    assert r['checks']['induction']['result']=='sat'

def test_actual_reachable_double_writer():
    r=run_bmc(2,9,early_grant=True,double_writer=True)
    assert r['result']=='COUNTEREXAMPLE' and r['first_depth']==9
    assert [c['mode'] for c in r['witness_states'][-1]['cores']]==['M','M']

def test_correct_model_reaches_modified_mode():
    p=Protocol(2,2,False)
    # One exclusive write to a line really is possible, not blocked by invariant construction.
    from cache_bmc import smt_depth
    q=smt_depth(p,5)
    q=q[:q.rfind('(assert')]+'''(assert (and (= latest_t5 1) (or (= mode_0_t5 2) (= mode_1_t5 2))))
(check-sat)
'''
    assert z3_smt(q).strip()=='sat'
