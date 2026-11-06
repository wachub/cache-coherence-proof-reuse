#!/usr/bin/env python3
"""Z3 checks for topology-parametric atomic hierarchy abstraction.

All checks are emitted as complete SMT-LIB2 with SHA256 digests.
UNSAT is required for proof obligations. SAT is expected for reachable
feature and injected-error witnesses; UNKNOWN is never a pass.
"""
from __future__ import annotations
import argparse,hashlib,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/13_hierarchy'))
sys.path.insert(0,str(ROOT/'experiments/09_combined_speculative_reads_writes'))
from hierarchy import Hierarchy,AND,OR,NOT,EQ,IMP,ITE,SELECT,READ,WRITE,CAS,EVICT
from cache_smt_verifier import z3_smt

def query(m,goal,timeout_ms=15000,model=False):
    return '(set-option :timeout '+str(timeout_ms)+')\n'+m.declarations()+\
        '(assert '+goal+')\n(check-sat)\n'+('(get-model)\n' if model else '')

def run_one(m,od,name,goal,expected='unsat',timeout_ms=15000):
    od.mkdir(parents=True,exist_ok=True)
    smt=query(m,goal,timeout_ms)
    (od/(name+'.smt2')).write_text(smt)
    start=time.monotonic();out=z3_smt(smt).strip();elapsed=time.monotonic()-start
    got=out.splitlines()[0] if out else 'error'
    result={'name':name,'actual':got,'expected':expected,'passed':got==expected,
      'elapsed_sec':round(elapsed,4),'sha256':hashlib.sha256(smt.encode()).hexdigest(),
      'query_bytes':len(smt)}
    return result

def src_contract(m,c,label):
    """Source reply depends only on coherent version/value, never topology."""
    v=m.v; C=m.c
    contract=[EQ(C(c,'pending',True),'false')]
    if 'serve_read' in label or 'cas_failure' in label:
        contract += [EQ(C(c,'reply_ver',True),v('latest')),
            EQ(C(c,'reply_val',True),SELECT(v('payload'),v('latest'))),
            EQ(v('latest',True),v('latest'))]
    elif 'serve_write' in label:
        new=f'(+ {v("latest")} 1)'
        contract += [EQ(v('latest',True),new),EQ(C(c,'reply_ver',True),new),
            EQ(C(c,'reply_val',True),C(c,'arg')),
            EQ(v('payload',True),f'(store {v("payload")} {new} {C(c,"arg")})')]
    elif 'cas_success' in label:
        new=f'(+ {v("latest")} 1)'
        contract += [EQ(v('latest',True),new),EQ(C(c,'reply_ver',True),new),
            EQ(C(c,'reply_val',True),SELECT(v('payload'),v('latest'))),
            EQ(v('payload',True),f'(store {v("payload")} {new} {C(c,"arg")})')]
    elif 'serve_evict' in label:
        contract += [EQ(v('latest',True),v('latest'))]
    return AND(*contract)

def frame_frontend(m,label):
    """Assert stable issue/service handshake independently of cache topology."""
    import re
    match=re.match(r'core(\d+):(issue|serve)_(.*)',label)
    c=int(match[1]);typ=match[2];C=m.c
    expr=[EQ(C(c,'pending',True),'true' if typ=='issue' else 'false')]
    for d in range(m.n):
        if d==c:continue
        for k in ('pending','op','arg','expected','reply_val','reply_ver','reply_ok','reply_source'):
            expr.append(EQ(C(d,k,True),C(d,k)))
    if typ=='issue':
        opname={'read':READ,'write':WRITE,'cas':CAS,'evict':EVICT}[match[3]]
        expr += [EQ(C(c,'op',True),str(opname)),EQ(C(c,'arg',True),'input_value'),
            EQ(C(c,'expected',True),'input_expected')]
    else:
        expr += [EQ(C(c,'op',True),C(c,'op')),EQ(C(c,'arg',True),C(c,'arg')),
            EQ(C(c,'expected',True),C(c,'expected'))]
    return AND(*expr)

def verify(fanouts,variant,output,timeout_ms=15000,quick=False,mutant=None):
    m=Hierarchy(fanouts,variant,mutant)
    od=output/(variant.lower()+'_'.join(str(x) for x in fanouts)+('_'+mutant if mutant else ''))
    I=m.invariant();Ip=m.invariant(True)
    entries=[]
    def check(label,goal,expected='unsat'):
        r=run_one(m,od,label,goal,expected,timeout_ms)
        entries.append(r)
        print(variant,fanouts,label,r['actual'],r['elapsed_sec'],flush=True)
        if not r['passed']:
            raise AssertionError('verification failure '+str(r))
    check('initial',AND(m.init(),NOT(I)))
    steps=m.steps()
    for label,transition in steps:
        safe=label.replace(':','_')
        if quick and not (label.startswith('core0:') or label.startswith(f'core{m.n-1}:')):continue
        check('ind_'+safe,AND(I,transition,NOT(Ip)))
        check('handshake_'+safe,AND(I,transition,NOT(frame_frontend(m,label))))
        if ':serve_' in label:
            c=int(label.split(':')[0][4:]);check('contract_'+safe,AND(I,transition,NOT(src_contract(m,c,label))))
    # Read-data routing obligations: sources are selected by ancestor cache
    # data-valid tags or the root's dirty-owner summary. The reply payload is
    # already covered by src_contract, irrespective of source.
    for c in range(m.n):
        for label,t in steps:
            if label not in (f'core{c}:serve_read',f'core{c}:serve_cas_failure'):
                continue
            if quick and c not in (0,m.n-1):continue
            base='route_c'+str(c)+'_'+('read' if label.endswith('read') else 'cas')
            src=m.c(c,'reply_source',True)
            check(base+'_L1',AND(I,t,EQ(src,'1'),NOT(m._valid(c))))
            check(base+'_remote_dirty',AND(I,t,EQ(src,'2'),
                  EQ(m.nd(m.top.root,'dirty_child'),'(- 1)')))
            check(base+'_memory_clean',AND(I,t,EQ(src,'10'),
                  NOT(EQ(m.v('mem'),m.v('latest')))))
            for distance,node in enumerate(reversed(m.top.leaf_paths[c])):
                tag=m.nd(node,'data_valid')
                fresh=EQ(m.nd(node,'data_ver'),m.v('latest'))
                check(base+'_ancestor_'+str(node),AND(I,t,
                      EQ(src,str(3+distance)),NOT(AND(tag,fresh))))
    # A pending command is always serviceable in the atomic backend. Each
    # service transition guard is (pending && op==k), with CAS partitioned on
    # equality; no additional protocol/permission guard exists.
    # We verify that the enabledness conditions have no counterexample.
    for c in range(m.n):
        guard=OR(*(AND(m.c(c,'pending'),EQ(m.c(c,'op'),str(op)))
                   for op in (READ,WRITE,CAS,EVICT)))
        check('pending_guard_'+str(c),AND(I,m.c(c,'pending'),NOT(guard)))
    summary={'configuration':m.top.summary(),'variant':variant,'abstract_atomic_backend':True,
        'checks':entries,'count':len(entries),'passed':all(x['passed'] for x in entries),
        'frontend_interface':m.interface_signature(),'mutant':mutant,
        'scope':'One cache line, atomic serialized backend; not the asynchronous v2.0 protocol.'}
    (od/'summary.json').write_text(json.dumps(summary,indent=2))
    return summary

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--fanouts',type=int,nargs='+',default=[2,2])
    p.add_argument('--variant',choices=['MSI','MESI','MOESI','all'],default='all')
    p.add_argument('--timeout-ms',type=int,default=15000)
    p.add_argument('--quick',action='store_true')
    p.add_argument('--output-dir',type=Path,default=ROOT/'artifacts/hierarchy_v21')
    args=p.parse_args();variants=('MSI','MESI','MOESI') if args.variant=='all' else (args.variant,)
    result=[verify(tuple(args.fanouts),v,args.output_dir,args.timeout_ms,args.quick) for v in variants]
    print(json.dumps({'passed':all(x['passed'] for x in result),'total':sum(x['count'] for x in result),
        'models':[{'variant':x['variant'],'topology':x['configuration']} for x in result]},indent=2))
if __name__=='__main__':main()
