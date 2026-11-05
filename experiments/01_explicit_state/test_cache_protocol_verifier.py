from cache_protocol_verifier import explore, explore_publication, explore_cas_race

def test_coherence_two_to_four_cores():
    for n in (2,3,4):
        r=explore(n,max_writes=2)
        assert r['result']=='PASS',r

def test_premature_grant_fails():
    r=explore(2,max_writes=2,mutant=True)
    assert r['result']=='COUNTEREXAMPLE',r
    assert 'GRANT' in r['trace'][-1]

def test_publication_arbitrary_core_migration():
    r=explore_publication(2)
    assert r['result']=='PASS',r
    assert r['completed_states']>0

def test_premature_publication_fails():
    r=explore_publication(2,reorder_release=True)
    assert r['result']=='COUNTEREXAMPLE',r
    assert 'obtained 0' in r['reason']

def test_concurrent_cas_exactly_one_wins():
    for n in (2,3):
        r=explore_cas_race(n)
        assert r['result']=='PASS',r
        assert r['completed_states']>0

def test_lost_dirty_writeback_fails():
    r=explore(2,max_writes=2,drop_writeback=True)
    assert r['result']=='COUNTEREXAMPLE',r
    assert 'stale' in r['reason']
