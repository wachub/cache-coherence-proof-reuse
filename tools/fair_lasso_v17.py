#!/usr/bin/env python3
"""Exhaustive fair-lasso model checker for a FINITE progress abstraction.

This is a second, independent check of the scheduling/round-robin progress
argument. It is NOT a whole-concrete-system LTL proof. Abstraction components:
  - request queue and round-robin pointer (one tracked line)
  - active coherence transaction in two servicing phases
  - target-core ask/permission/complete behavior with revocation
  - arbitrary interfering traffic and scheduler stuttering

The fair SCC algorithm is exact for finite directed graphs with weak and strong
event fairness. It checks the absence of ultimately periodic fair executions
that leave an issued request incomplete.
"""
from __future__ import annotations
import argparse
import collections
import json
from dataclasses import dataclass, replace
from typing import NamedTuple

WF=('start','service','ask')
SF=('complete',)

@dataclass(frozen=True)
class S:
    rr:int
    other:int
    tx:int      # -1 = idle, 0 = target core, 1..N-1 = competitor
    phase:int   # 2,1 servicing phases; 0 idle
    target:int  # 0=needs ask, 1=queued, 2=has permission, 3=completed

class Edge(NamedTuple):
    to:S
    event:str


def enabled(s:S,n:int,unfair=False):
    avail=s.other | (1 if s.target==1 else 0)
    e={'stutter'}
    if s.target==0: e.add('ask')
    if s.target==2: e.add('complete')
    for c in range(1,n):
        if not (s.other & (1<<c)) and s.tx!=c: e.add('request')
    if s.tx>=0:
        e.add('service')
    if s.tx==-1 and avail:
        e.add('start')
    return e


def succ(s:S,n:int,unfair=False):
    yield Edge(s,'stutter')
    if s.target==0: yield Edge(replace(s,target=1),'ask')
    if s.target==2: yield Edge(replace(s,target=3),'complete')
    for c in range(1,n):
        if not (s.other & (1<<c)) and s.tx!=c:
            yield Edge(replace(s,other=s.other | (1<<c)),'request')
    if s.tx>=0:
        if s.phase==2:
            yield Edge(replace(s,phase=1),'service')
        else:
            assert s.phase==1
            if s.tx==0:
                yield Edge(replace(s,tx=-1,phase=0,target=2),'service')
            else:
                # Competing core takes exclusive ownership; if tracked core
                # had permission, it must ask again.
                t=0 if s.target==2 else s.target
                yield Edge(replace(s,tx=-1,phase=0,target=t),'service')
    else:
        avail=s.other|(1 if s.target==1 else 0)
        if avail:
            candidates=[]
            for off in range(n):
                c=(s.rr+off)%n
                if avail & (1<<c):
                    candidates.append(c)
                    if not unfair: break
            for c in candidates:
                changes={'tx':c,'phase':2,'rr':(c+1)%n}
                if c==0:
                    changes['target']=1 # queued until grant has actually arrived
                else:
                    changes['other']=s.other & ~(1<<c)
                yield Edge(replace(s,**changes),'start')


def graph(n:int,unfair=False):
    first=S(0,0,-1,0,1) # already-issued tracked request
    edges={};work=collections.deque([first]);seen={first}
    while work:
        s=work.popleft()
        edges[s]=[edge for edge in succ(s,n,unfair)]
        for next_s,_ in edges[s]:
            if next_s not in seen:
                seen.add(next_s);work.append(next_s)
    return first,edges


def sccs(nodes,edges):
    """Tarjan strongly connected components of an induced subgraph."""
    nodes=set(nodes);index=0; stack=[]; on=set();num={};low={};result=[]
    def visit(v):
        nonlocal index
        num[v]=low[v]=index;index+=1;stack.append(v);on.add(v)
        for next_v,_ in edges[v]:
            if next_v not in nodes: continue
            if next_v not in num:
                visit(next_v);low[v]=min(low[v],low[next_v])
            elif next_v in on: low[v]=min(low[v],num[next_v])
        if low[v]==num[v]:
            comp=set()
            while True:
                x=stack.pop();on.remove(x);comp.add(x)
                if x==v:break
            result.append(comp)
    for s in nodes:
        if s not in num: visit(s)
    return result


def recurrent(nodes,edges):
    if len(nodes)>1:return True
    s=next(iter(nodes))
    return any(edge.to==s for edge in edges[s])


def fair_scc(edges,n,unfair=False,wf=WF,sf=SF):
    """Return a reachable fair SCC with target incomplete, if one exists.

    For an SCC visited infinitely often, SF(e) requires e-edge on recurrent
    walk whenever e is enabled at least once there. WF(e) requires e-edge
    whenever enabled at every recurrent state. If no suitable e-edge exists,
    refine by removing enabled states (for SF). Exact existence algorithm.
    """
    candidates=[{s for s in edges if s.target!=3}]
    checked=0
    while candidates:
        subset=candidates.pop()
        if not subset:continue
        for comp in sccs(subset,edges):
            if not recurrent(comp,edges):continue
            checked+=1
            internal={event for s in comp for dest,event in edges[s] if dest in comp}
            for event in sf:
                en={s for s in comp if event in enabled(s,n,unfair)}
                if en and event not in internal:
                    rest=comp-en
                    if rest:candidates.append(rest)
                    break
            else:
                for event in wf:
                    if all(event in enabled(s,n,unfair) for s in comp) and event not in internal:
                        break
                else:
                    return comp,checked
    return None,checked


def run_case(n,unfair=False,strong_completion=True,service_fair=True,start_fair=True):
    first,edges=graph(n,unfair)
    wf=tuple(event for event in WF if (event!='service' or service_fair) and (event!='start' or start_fair))
    sf=('complete',) if strong_completion else ()
    if not strong_completion:wf=wf+('complete',)
    comp,checked=fair_scc(edges,n,unfair,wf,sf)
    return {'cores':n,'unfair_arbiter':unfair,'strong_completion':strong_completion,
            'service_fair':service_fair,'start_fair':start_fair,
            'abstract_reachable_states':len(edges), 'examined_sccs':checked,
            'fair_incomplete_lasso_exists':comp is not None,
            'counterexample_recurrence_size':len(comp) if comp else 0,
            'sample_recurrent_state':str(next(iter(comp))) if comp else None}


def main():
    p=argparse.ArgumentParser();p.add_argument('--max-cores',type=int,default=4);p.add_argument('--output',default='artifacts/temporal_fairness_v1_7/fair_lasso.json');x=p.parse_args()
    results=[]
    for n in range(2,x.max_cores+1):
        for options,expected in [({},False),({'unfair':True},True),
                                 ({'strong_completion':False},True),
                                 ({'service_fair':False},True),
                                 ({'start_fair':False},True)]:
            result=run_case(n,**options)
            result['expected_fair_incomplete_lasso']=expected
            result['passed']=result['fair_incomplete_lasso_exists']==expected
            print(result,flush=True);results.append(result)
    from pathlib import Path
    dest=Path(x.output);dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps({'passed':all(r['passed'] for r in results),'cases':results},indent=2)+'\n')
    return all(r['passed'] for r in results)
if __name__=='__main__':raise SystemExit(0 if main() else 1)
