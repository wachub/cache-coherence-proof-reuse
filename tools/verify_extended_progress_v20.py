#!/usr/bin/env python3
"""Progress enabledness / compositional temporal premises for MESI and MOESI.

Not a global fair-path LTL proof. A service *event class* is the fairness unit:
local E->M can disable recall_E and enable recall_M without blocking service.
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'experiments/12_mesi_moesi'))
sys.path.insert(0,str(ROOT/'tools'))
from extended_system import ExtendedFairSpec
from verify_mesi_moesi_v20 import emit
from liveness_verify import capture_protocol_guards,is_service
from progress_v16_verify import local_progress_queries,nextify_formula
from cache_smt_verifier import a,o,neg,eq

def goals(m):
    inv=m.inv(); T=m.T();steps=dict(m.steps())
    result={k:v for k,v in local_progress_queries(m).items()
            if not k.endswith('_service_guard_stable_without_service')}
    pguards,_=capture_protocol_guards(m.p)
    front=m.effective_frontend_guards()
    service_any=[]; start_any=[]
    for l in range(m.k):
        pref=f'l{l}::';active=neg(eq(m.pl(l,'tx'),'(- 1)'))
        service_enabled=o(*(m.map_line(g,l) for k,g in pguards.items() if is_service(k)))
        service_taken=o(*(form for name,form in steps.items()
            if name.startswith(pref) and is_service(name[len(pref):])))
        start_enabled=o(*(a(m.map_line(g,l),m._rr_selected(l,c))
            for c in range(m.n) for name,g in pguards.items()
            if name.startswith('dir:start_') and name.endswith(f'_c{c}')))
        service_any.append(service_enabled);start_any.append(start_enabled)
        result[f'line{l}_some_service_guard_stable_without_service']=a(inv,active,service_enabled,
            T,neg(service_taken),neg(nextify_formula(m,service_enabled)))
    def useful(name):return (':ask_' in name or ':complete_' in name or
          ':issue_confirmed_store_' in name or ':spec_retire_fast_' in name or
          ':spec_replay_' in name or name.endswith((':confirm',':squash_suffix',':squash_read')))
    frontend=o(*(guard for name,guard in front.items() if useful(name)))
    work=o(*(m.cpu(c,'busy') for c in range(m.n)),
           *(f'(> {m.x(c,"qlen")} 0)' for c in range(m.n)),
           *(m.x(c,'load_active') for c in range(m.n)),
           *(neg(eq(m.pl(l,'tx'),'(- 1)')) for l in range(m.k)),
           *(m.pl(l,z,c) for l in range(m.k) for c in range(m.n) for z in ('rqR','rqW')))
    result['global_no_terminal_stall_enabledness']=a(inv,work,neg(o(*service_any,*start_any,frontend)))
    for c in range(m.n):
        busy=m.cpu(c,'busy');busy1=m.cpu(c,'busy',True)
        q=m.x(c,'qlen'); r=m.x(c,'ready'); act=m.x(c,'load_active');conf=m.x(c,'load_confirmed')
        local_pending=o(*(m.pl(l,'pending',c) for l in range(m.k)))
        cpu_steps=o(*(guard for name,guard in front.items() if name.startswith(f'core{c}:ask_') or name.startswith(f'core{c}:complete_')))
        result[f'core{c}_busy_without_pending_has_ask_or_complete']=a(inv,busy,neg(local_pending),neg(cpu_steps))
        completed=o(*(form for name,form in steps.items() if name.startswith(f'core{c}:complete_')))
        result[f'core{c}_busy_persists_until_completion']=a(inv,busy,T,neg(completed),neg(busy1))
        for l in range(m.k):
            mode=m.pl(l,'mode',c)
            pre=a(inv,busy,neg(m.pl(l,'pending',c)),eq(m.cpu(c,'target'),str(l)))
            read_allowed=m._valid(mode)
            write_allowed=o(eq(mode,'2'),eq(mode,'3'))
            for opname,n,permission in (('read',1,read_allowed),('store',2,write_allowed),('cas',3,write_allowed)):
                result[f'core{c}_line{l}_{opname}_permission_enables_completion']=a(pre,eq(m.cpu(c,'op'),str(n)),permission,
                    neg(front[f'core{c}:complete_{opname}_line{l}']))
        unresolved_queue=f'(> {q} {r})'
        resolve_queue=o(front[f'core{c}:confirm'],front[f'core{c}:squash_suffix'])
        result[f'core{c}_unconfirmed_queue_has_resolution']=a(inv,unresolved_queue,neg(resolve_queue))
        unresolved_load=a(act,neg(conf))
        resolve_load=o(front[f'core{c}:confirm'],front[f'core{c}:squash_suffix'],front[f'core{c}:squash_read'])
        result[f'core{c}_unconfirmed_load_has_resolution']=a(inv,unresolved_load,neg(resolve_load))
        issue=o(*(guard for name,guard in front.items() if name.startswith(f'core{c}:issue_confirmed_store_line')))
        result[f'core{c}_confirmed_store_head_can_issue']=a(inv,f'(> {r} 0)',neg(busy),neg(issue))
        settle=o(*(guard for name,guard in front.items() if name.startswith(f'core{c}:spec_retire_fast_') or
            name.startswith(f'core{c}:spec_replay_')))
        result[f'core{c}_confirmed_read_can_settle']=a(inv,act,conf,eq(q,'0'),neg(busy),neg(settle))
    return result

def run(args):
    summaries=[]
    for variant in (('MESI','MOESI') if args.variant=='both' else (args.variant,)):
        m=ExtendedFairSpec(args.cores,args.lines,variant)
        od=args.out/f'{variant.lower()}_{args.cores}cores_{args.lines}lines';od.mkdir(parents=True,exist_ok=True)
        results=[]
        for label,formula in goals(m).items():
            r=emit(m,od,label,formula,args.timeout_ms);results.append(r)
            print(variant,args.cores,args.lines,label,r['result'],flush=True)
            if not r['passed']:break
        summary={'variant':variant,'cores':args.cores,'lines':args.lines,'passed':all(z['passed'] for z in results),
                 'results':results,'scope':'concrete SMT progress premises, not a temporal LTL certificate',
                 'fairness':'WF of per-line SomeService/SomeStart plus speculative resolution; SF for CPU completion'}
        summaries.append(summary);(od/'summary.json').write_text(json.dumps(summary,indent=2))
    return all(s['passed'] for s in summaries)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--cores',type=int,default=4)
    ap.add_argument('--lines',type=int,default=2);ap.add_argument('--variant',choices=['MESI','MOESI','both'],default='both')
    ap.add_argument('--timeout-ms',type=int,default=20000);ap.add_argument('--out',type=Path,default=ROOT/'artifacts/mesi_moesi_v20/progress')
    x=ap.parse_args();sys.exit(0 if run(x) else 1)
