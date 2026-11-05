#!/usr/bin/env python3
"""Small executable explicit-state checker for a deliberately inefficient
release-consistent shared-memory protocol.

Model restrictions:
* One global mutex protects ALL modelled shared addresses.
* Only the current mutex owner issues shared loads/stores.
* Each core has private cache entries: None = invalid, integer = valid.
* Writes are privately dirty until the owner releases and drains them to home.
* A successful acquire invalidates the acquiring core's private cached data.
* Lock CAS is serialized at an abstract home controller.
* Writeback is one address per transition; lock stays held throughout.
* A ghost sequential memory ('spec') represents the last sequential write.

This checks all finite interleavings and data values for given parameter sizes,
not a general proof for all parameter sizes, real RTL, or progress.
"""
from collections import deque
from dataclasses import dataclass, replace
from typing import Optional
import argparse, json

@dataclass(frozen=True)
class S:
    owner: int  # -1 means unlocked
    flushing: bool
    mem: tuple
    spec: tuple
    cache: tuple  # core -> address -> None or value
    dirty: tuple  # core -> address -> bool


def initialize(ncore, naddr):
    return S(-1, False, (0,)*naddr, (0,)*naddr,
             tuple((None,)*naddr for _ in range(ncore)),
             tuple((False,)*naddr for _ in range(ncore)))


def put_at(t, ix, value):
    t=list(t);t[ix]=value;return tuple(t)


def modify_cache(s,core,addr,val,markdirty=None):
    cache=put_at(s.cache, core, put_at(s.cache[core],addr,val))
    dirty=s.dirty
    if markdirty is not None:
        dirty=put_at(s.dirty,core,put_at(s.dirty[core],addr,markdirty))
    return replace(s,cache=cache,dirty=dirty)


def invariant(s):
    n=len(s.cache)
    if s.owner == -1:
        assert not s.flushing
        assert s.mem == s.spec, 'Unlocked home must equal sequential specification'
        assert not any(any(ds) for ds in s.dirty), 'No dirty cache when unlocked'
    else:
        assert 0 <= s.owner < n
        for i in range(n):
            if i != s.owner:
                assert not any(s.dirty[i]), 'Only owner may hold dirty data'
        for addr in range(len(s.mem)):
            if s.dirty[s.owner][addr]:
                assert s.cache[s.owner][addr] == s.spec[addr]
            else:
                assert s.mem[addr] == s.spec[addr]
                if s.cache[s.owner][addr] is not None:
                    assert s.cache[s.owner][addr] == s.spec[addr], 'Owner has stale read-capable cache entry'


def actions(s, values, invalidate_on_acquire=True):
    n=len(s.cache); a_count=len(s.mem)
    if s.owner == -1:
        for i in range(n):
            # Atomic successful CAS(lock,unlocked,i), followed by local invalidation
            # before the new owner can issue any loads or stores.
            new_cache=put_at(s.cache,i,(None,)*a_count) if invalidate_on_acquire else s.cache
            yield f'core{i}: CAS acquire and '+('invalidate local lines' if invalidate_on_acquire else 'SKIP invalidation'),replace(s,owner=i,cache=new_cache)
        return
    i=s.owner
    if s.flushing:
        for addr in range(a_count):
            if s.dirty[i][addr]:
                ns=modify_cache(s,i,addr,s.cache[i][addr],False)
                ns=replace(ns,mem=put_at(ns.mem,addr,s.cache[i][addr]))
                yield f'core{i}: write back address{addr}',ns
        if not any(s.dirty[i]):
            yield f'core{i}: release mutex',replace(s,owner=-1,flushing=False)
        return
    # The reads are observable actions. A stale result should fail the check,
    # rather than being filtered out by the transition relation.
    for addr in range(a_count):
        v=s.cache[i][addr]
        ns=s if v is not None else modify_cache(s,i,addr,s.mem[addr])
        result=s.mem[addr] if v is None else v
        yield f'core{i}: read address{addr} -> {result}',ns
        for value in values:
            ns=modify_cache(s,i,addr,value,True)
            ns=replace(ns,spec=put_at(ns.spec,addr,value))
            yield f'core{i}: write address{addr}={value}',ns
    yield f'core{i}: begin release (flush all dirty lines)',replace(s,flushing=True)


def check(ncore=2,naddr=2,values=(0,1),invalidate_on_acquire=True,max_states=1000000):
    start=initialize(ncore,naddr)
    q=deque([start]);prev={start:None}; transition_count=0
    while q:
        s=q.popleft()
        try:
            invariant(s)
        except AssertionError as err:
            trace=[]; cur=s
            while prev[cur] is not None:
                p,action=prev[cur];trace.append(action);cur=p
            trace.reverse()
            return dict(status='VIOLATION',reason=str(err),states=len(prev),transitions=transition_count,trace=trace)
        for action,ns in actions(s,values,invalidate_on_acquire):
            transition_count+=1
            if ns not in prev:
                prev[ns]=(s,action);q.append(ns)
                if len(prev)>max_states:
                    return dict(status='INCOMPLETE',states=len(prev),transitions=transition_count)
    return dict(status='PASS_EXHAUSTIVE',states=len(prev),transitions=transition_count)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--cores',type=int,default=2);parser.add_argument('--addresses',type=int,default=2);parser.add_argument('--broken',action='store_true');parser.add_argument('--max-states',type=int,default=1000000)
    a=parser.parse_args()
    print(json.dumps(check(a.cores,a.addresses,invalidate_on_acquire=not a.broken,max_states=a.max_states),indent=2))
