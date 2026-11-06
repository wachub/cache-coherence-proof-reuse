#!/usr/bin/env python3
"""Noninterference proof for plugging in additional *idle* leaf cores.

Existing cores c0..c(n-1) preserve responses and cache states under a
wider/deeper hierarchy if newly added cores start Invalid, have no pending
request, and do not issue operations during the comparison.
"""
from __future__ import annotations
import argparse,json,hashlib,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/13_hierarchy'))
sys.path.insert(0,str(ROOT/'experiments/09_combined_speculative_reads_writes'))
from hierarchy import Hierarchy,AND,NOT,EQ
from cache_smt_verifier import z3_smt
from verify_hierarchy_equivalence_v21 import with_prefix,decl,rel,guard

def check_pair(small,large,variant,od,timeout=20000):
    a=Hierarchy(small,variant);b=Hierarchy(large,variant)
    if a.n>=b.n:raise ValueError('new topology must have additional cores')
    od.mkdir(parents=True,exist_ok=True)
    frame=AND(*(AND(EQ(f'B__c{c}_mode','0'),EQ(f'B__c{c}_pending','false'))
                for c in range(a.n,b.n)))
    frame_p=AND(*(AND(EQ(f'B__c{c}_mode_next','0'),EQ(f'B__c{c}_pending_next','false'))
                for c in range(a.n,b.n)))
    base='(set-option :timeout '+str(timeout)+')\n'+decl(a,'A__')+'\n'+decl(b,'B__')+\
         '\n(declare-const input_value Int)\n(declare-const input_expected Int)\n'
    inv=AND(with_prefix(a,a.invariant(),'A__'),with_prefix(b,b.invariant(),'B__'))
    r=rel(a,b)
    results=[]
    def run(name,expr,expected='unsat'):
        s=base+'(assert '+expr+')\n(check-sat)\n'
        (od/(name+'.smt2')).write_text(s)
        now=time.monotonic();out=z3_smt(s).strip();status=out.splitlines()[0] if out else 'error'
        e={'check':name,'result':status,'expected':expected,'passed':status==expected,
            'sha256':hashlib.sha256(s.encode()).hexdigest(),
            'elapsed_sec':round(time.monotonic()-now,4)}
        results.append(e)
        if not e['passed']:raise AssertionError(e)
    run('initial_agreement',AND(with_prefix(a,a.init(),'A__'),
        with_prefix(b,b.init(),'B__'),EQ('A__payload','B__payload'),NOT(AND(r,frame))))
    run('joint_initial_reachable',AND(with_prefix(a,a.init(),'A__'),
        with_prefix(b,b.init(),'B__'),r,frame),'sat')
    sa=dict(a.steps());sb=dict(b.steps())
    for name in sa:
        safe=name.replace(':','_')
        ga=with_prefix(a,guard(a,name),'A__');gb=with_prefix(b,guard(b,name),'B__')
        run('enabled_'+safe,AND(inv,r,frame,NOT(EQ(ga,gb))))
        run('stuttering_extension_'+safe,AND(inv,r,frame,
            with_prefix(a,sa[name],'A__'),with_prefix(b,sb[name],'B__'),
            NOT(AND(rel(a,b,True),frame_p))))
    out={'variant':variant,'small':a.top.summary(),'large':b.top.summary(),
        'pass':all(x['passed'] for x in results),'checks':len(results),'results':results,
        'restriction':'All newly added cores are Invalid and stay idle; their presence changes topology but not old-core semantics.'}
    (od/'summary.json').write_text(json.dumps(out,indent=2))
    return out

def main():
    p=argparse.ArgumentParser();p.add_argument('--small',nargs='+',type=int,default=[2,2]);p.add_argument('--large',nargs='+',type=int,default=[2,4]);p.add_argument('--variant',choices=['MSI','MESI','MOESI','all'],default='all');p.add_argument('--output-dir',type=Path,default=ROOT/'artifacts/hierarchy_v21_width_extension')
    x=p.parse_args();variants=['MSI','MESI','MOESI'] if x.variant=='all' else [x.variant]
    res=[check_pair(x.small,x.large,v,x.output_dir/(v.lower()+'_'+'_'.join(map(str,x.small))+'__'+'_'.join(map(str,x.large)))) for v in variants]
    print(json.dumps({'passed':all(y['pass'] for y in res),'checks':sum(y['checks'] for y in res)},indent=2))
if __name__=='__main__':main()
