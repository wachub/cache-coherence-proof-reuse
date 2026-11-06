#!/usr/bin/env python3
"""Relational proof: tree topology changes preserve frontend-visible behavior.

The two models must have the same leaf count and coherence variant. The
proof hides microarchitectural reply_source and internal directory/data cache
fields. It establishes paired-step preservation and equal action enabledness.
No claim is made about asynchronous v2.0 message-level refinement.
"""
from __future__ import annotations
import argparse,hashlib,json,re,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/13_hierarchy'))
sys.path.insert(0,str(ROOT/'experiments/09_combined_speculative_reads_writes'))
from hierarchy import Hierarchy,AND,OR,NOT,EQ,SELECT
from cache_smt_verifier import z3_smt

def with_prefix(m,formula,prefix):
    """Rename SMT variables, leaving operation input ports shared."""
    names=[k+('_next' if nxt else '') for nxt in (True,False) for k in m.keys]
    expr=re.compile(r'(?<![A-Za-z0-9_])('+ '|'.join(map(re.escape,sorted(names,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
    return expr.sub(lambda x:prefix+x.group(0),formula)

def decl(m,prefix):
    return '\n'.join(f'(declare-const {prefix}{k}{"_next" if nxt else ""} {typ})'
        for nxt in (False,True) for k,typ in m.types.items())

def rel(a,b,nxt=False):
    names=['latest','mem','payload']
    for c in range(a.n):
        names += [f'c{c}_{z}' for z in ('mode','ver','pending','op','arg',
                    'expected','reply_ver','reply_val','reply_ok')]
    return AND(*(EQ('A__'+k+('_next' if nxt else ''),
                    'B__'+k+('_next' if nxt else '')) for k in names))

def guard(m,label):
    import re
    mt=re.match(r'core(\d+):(issue|serve)_(.*)',label)
    c=int(mt[1]);what=mt[2];kind=mt[3]
    if what=='issue':return NOT(m.c(c,'pending'))
    op=kind.split('_',1)[0]
    number={'read':1,'write':2,'cas':3,'evict':4}[op]
    g=AND(m.c(c,'pending'),EQ(m.c(c,'op'),str(number)))
    if op=='cas':
        good=EQ(SELECT(m.v('payload'),m.v('latest')),m.c(c,'expected'))
        return AND(g,good if kind=='cas_success' else NOT(good))
    return g

def check_pair(fan_a,fan_b,variant,output,timeout=20000,quick=False):
    a=Hierarchy(fan_a,variant);b=Hierarchy(fan_b,variant)
    if a.n!=b.n:raise ValueError('same leaf count required for observational equivalence')
    output.mkdir(parents=True,exist_ok=True)
    steps_a=dict(a.steps());steps_b=dict(b.steps())
    assert set(steps_a)==set(steps_b)
    base=decl(a,'A__')+'\n'+decl(b,'B__')+'\n(declare-const input_value Int)\n(declare-const input_expected Int)\n'
    inv=AND(with_prefix(a,a.invariant(),'A__'),with_prefix(b,b.invariant(),'B__'))
    relation=rel(a,b)
    results=[]
    def run(name,expr,expected='unsat'):
        q=f'(set-option :timeout {timeout})\n'+base+'(assert '+expr+')\n(check-sat)\n'
        (output/(name+'.smt2')).write_text(q)
        start=time.monotonic();raw=z3_smt(q).strip();status=raw.splitlines()[0] if raw else 'error'
        r={'name':name,'result':status,'expected':expected,'passed':status==expected,
           'sha256':hashlib.sha256(q.encode()).hexdigest(),
           'seconds':round(time.monotonic()-start,4)}
        results.append(r)
        print(variant,fan_a,fan_b,name,status,flush=True)
        if not r['passed']:raise AssertionError(r)
    run('initial_projection',AND(with_prefix(a,a.init(),'A__'),
        with_prefix(b,b.init(),'B__'),EQ('A__payload','B__payload'),NOT(relation)))
    # Reachable initial paired state exists (anti-vacuity).
    run('initial_joint_sat',AND(with_prefix(a,a.init(),'A__'),
        with_prefix(b,b.init(),'B__'),relation),'sat')
    for name in steps_a:
        if quick and not (name.startswith('core0:') or name.startswith(f'core{a.n-1}:')):continue
        safe=name.replace(':','_')
        ga=with_prefix(a,guard(a,name),'A__');gb=with_prefix(b,guard(b,name),'B__')
        run('same_enabled_'+safe,AND(inv,relation,NOT(EQ(ga,gb))))
        ta=with_prefix(a,steps_a[name],'A__');tb=with_prefix(b,steps_b[name],'B__')
        run('step_refines_'+safe,AND(inv,relation,ta,tb,NOT(rel(a,b,True))))
    summary={'topology_a':a.top.summary(),'topology_b':b.top.summary(),
             'variant':variant,'steps':len(steps_a),'checks':len(results),
             'passed':all(x['passed'] for x in results),'results':results,
             'observable':'memory versions and payload, L1 states, request/reply API except performance source',
             'assumption':'atomic backend; no asynchronous channel semantics'}
    (output/'summary.json').write_text(json.dumps(summary,indent=2))
    return summary

def main():
    p=argparse.ArgumentParser();p.add_argument('--a',nargs='+',type=int,required=True)
    p.add_argument('--b',nargs='+',type=int,required=True)
    p.add_argument('--variant',choices=['MSI','MESI','MOESI','all'],default='all')
    p.add_argument('--timeout-ms',type=int,default=20000)
    p.add_argument('--quick',action='store_true')
    p.add_argument('--output-dir',type=Path,default=ROOT/'artifacts/hierarchy_v21_equivalence')
    ar=p.parse_args();v=('MSI','MESI','MOESI') if ar.variant=='all' else (ar.variant,)
    x=[check_pair(tuple(ar.a),tuple(ar.b),name,
       ar.output_dir/(name.lower()+'_'+'_'.join(map(str,ar.a))+'__'+'_'.join(map(str,ar.b))),
       ar.timeout_ms,ar.quick) for name in v]
    print(json.dumps({'passed':all(y['passed'] for y in x),'checks':sum(y['checks'] for y in x)},indent=2))
if __name__=='__main__':main()
