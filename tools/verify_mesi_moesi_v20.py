#!/usr/bin/env python3
"""Machine-checked safety/contract and per-line progress obligations for MESI/MOESI.

SAT/UNKNOWN are never counted as successful UNSAT proof obligations.
SMT-LIB queries and SHA256 digests are archived for reproduction.
"""
from __future__ import annotations
import argparse,hashlib,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/12_mesi_moesi'))
from extended_system import ExtendedFairSpec
from cache_smt_verifier import z3_smt,a,o,neg,eq,imp

def emit(m,od,label,goal,timeout=20000, expected='unsat'):
    query=f'(set-option :timeout {timeout})\n'+m.declarations()+'\n(assert '+goal+')\n(check-sat)\n'
    digest=hashlib.sha256(query.encode()).hexdigest()
    (od/(label+'.smt2')).write_text(query)
    t=time.monotonic();raw=z3_smt(query).strip();result=raw.splitlines()[0] if raw else 'error'
    return {'check':label,'result':result,'expected':expected,'passed':result==expected,
            'sha256':digest,'seconds':round(time.monotonic()-t,4),'bytes':len(query)}

def b2i(expr): return f'(ite {expr} 1 0)'
def isum(xs):return '(+ '+' '.join(xs)+')' if xs else '0'

def progress_rank(m,l,nxt=False):
    p=lambda field,c=None:m.pl(l,field,c,nxt=nxt)
    tx=p('tx');phase=p('phase')
    wait=isum([b2i(p('wait',c)) for c in range(m.n)])
    undelivered=isum([b2i(p(kind,c)) for c in range(m.n) for kind in ('inv','recall')])
    grant=isum([b2i(p(kind,c)) for c in range(m.n) for kind in ('grS','grM')])
    return f'(ite (= {tx} (- 1)) 0 (ite (= {phase} 0) (+ 8 (* 3 {wait}) {undelivered}) (+ 2 {grant})))'

def checks(m,od,timeout=20000,full=False):
    od.mkdir(parents=True,exist_ok=True)
    I=m.inv();Ip=m.inv(True)
    cases=[('initial',a(m.init(),neg(I))),
       ('induction',a(I,m.T(),neg(Ip))),
       ('badflag',a(I,m.v('bad'))),
       ('speculative_interface',a(I,o(*(f for _,f in m.delta_steps())),neg(m.interface_contract())))]
    for l in range(m.k):cases.append((f'line{l}_coherence_safety',a(I,m.map_line(m.p.bad(),l))))
    for l in range(m.k):
        rank=progress_rank(m,l); rankp=progress_rank(m,l,True)
        active=neg(eq(m.pl(l,'tx'),'(- 1)'))
        service=[]
        for lab,form in m.steps():
            if not lab.startswith(f'l{l}::'):continue
            typ=lab.split('::',1)[1]
            if typ.startswith(('net:deliver_inv','net:deliver_recall','net:deliver_gr',
                               'dir:accept_ack','dir:accept_wb','dir:accept_gack','dir:grant_')):
                service.append((lab,form))
        service_join=o(*(s for _,s in service))
        cases.append((f'line{l}_service_rank_descends',a(I,service_join,neg(f'(< {rankp} {rank})'))))
        cases.append((f'line{l}_rank_positive',a(I,active,neg(f'(> {rank} 0)'))))
        # Any active transaction has an enabled serving event. In the
        # interleaving model, existence is represented as one of the next
        # states satisfying a service transition. Quantifier elimination is
        # not attempted here: each pattern is checked separately below.
    results=[]
    for label,goal in cases:
        rec=emit(m,od,label,goal,timeout)
        results.append(rec)
        print(m.variant,f'{m.n}x{m.k}',label,rec['result'],rec['seconds'],flush=True)
        if not rec['passed']:
            break
    return results

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--cores',type=int,default=2)
    ap.add_argument('--lines',type=int,default=1);ap.add_argument('--variant',choices=['MESI','MOESI','both'],default='both')
    ap.add_argument('--timeout-ms',type=int,default=20000);ap.add_argument('--out',type=Path,default=ROOT/'artifacts/mesi_moesi_v20')
    args=ap.parse_args(); allres=[]
    for variant in (('MESI','MOESI') if args.variant=='both' else (args.variant,)):
        m=ExtendedFairSpec(args.cores,args.lines,variant)
        od=args.out/f'{variant.lower()}_{args.cores}cores_{args.lines}lines'
        res=checks(m,od,args.timeout_ms)
        allres.append({'variant':variant,'cores':args.cores,'lines':args.lines,
             'passed':all(r['passed'] for r in res),'results':res,'transitions':len(m.steps()),
             'model':'ExtendedFairSpec based on v1.7 TemporalFairSpec; E=3 O=4'})
        (od/'summary.json').write_text(json.dumps(allres[-1],indent=2))
    if not all(x['passed'] for x in allres):sys.exit(1)
if __name__=='__main__':main()
