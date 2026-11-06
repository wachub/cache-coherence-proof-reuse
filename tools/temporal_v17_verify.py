#!/usr/bin/env python3
"""v1.7 fairness-specific SMT premises for compositional temporal reasoning.

Each UNSAT result establishes a *single-step* premise, not an independently
certified LTL theorem. See TEMPORAL_FAIRNESS_v1_7.md for the temporal argument,
fairness specification, logical proof rules, and limitations.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import sys
import time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from progress_v16_verify import FairProgressSpec,rr_distance,invariant_queries
from liveness_verify import capture_protocol_guards, is_service
from cache_smt_verifier import a,o,neg,eq,imp,z3_smt

class TemporalFairSpec(FairProgressSpec):
    """Reachability-strengthening invariant for confirmed speculative reads."""
    def inv(self,nxt=False):
        return a(super().inv(nxt), *(imp(self.x(c,'load_confirmed',nxt),
            eq(self.x(c,'ready',nxt),self.x(c,'qlen',nxt)))
            for c in range(self.n)))



def frontend_effective_guards(m):
    """Capture the true *repaired* guards from the v1.6 transition schema."""
    guards={}
    old=m.step
    def capture(label,guard,patch):
        original_guard=guard
        mo=re.fullmatch(r'core(\d+):complete_(store|cas)_line(\d+)',label)
        if mo:
            c,l=int(mo[1]),int(mo[3]);fresh=f'(+ {m.pl(l,"latest")} 1)'
            required=eq(f'(select payload_{l} {fresh})',m.cpu(c,'newval'))
            if required not in guard:
                raise AssertionError(f'missing repaired payload guard {label}')
            guard=guard.replace(required,'true')
        if label in guards: raise AssertionError(f'duplicate label {label}')
        guards[label]=guard
        return old(label,original_guard,patch)
    m.step=capture
    try: m.inherited_steps();m.delta_steps()
    finally: m.step=old
    return guards


def join(guards,condition):
    return o(*(f for label,f in guards.items() if condition(label)))


def lemmas(m):
    I=m.inv()
    steps=dict(m.steps()); T=o(*steps.values())
    pguards,_=capture_protocol_guards(m.p)
    fg=frontend_effective_guards(m)
    goals=dict(invariant_queries(m))
    n=m.n;k=m.k
    for l in range(k):
        prefix=f'l{l}::'
        idle=eq(m.pl(l,'tx'),'(- 1)')
        idle1=eq(m.pl(l,'tx',nxt=True),'(- 1)')
        queue=o(*(m.pl(l,kind,c) for c in range(n) for kind in ('rqR','rqW')))
        queue1=o(*(m.pl(l,kind,c,nxt=True) for c in range(n) for kind in ('rqR','rqW')))
        starts=join(steps,lambda label:label.startswith(prefix+'dir:start_'))
        # Coarse event SomeStart(line) remains continuously enabled until taken.
        goals[f'line{l}__idle_queued_persists_until_some_start']=a(I,idle,queue,T,neg(starts),neg(a(idle1,queue1)))
        # Starting a queued request must not leave a same-core request behind.
        # A new request by a different core can still be queued in this step? no.
        for c in range(n):
            busy=m.cpu(c,'busy')
            busy1=m.cpu(c,'busy',True)
            pending=m.pl(l,'pending',c)
            pending1=m.pl(l,'pending',c,nxt=True)
            starts_c=join(steps,lambda label:label.startswith(prefix+'dir:start_') and label.endswith(f'_c{c}'))
            grants_c=join(steps,lambda label:label in (f'{prefix}net:deliver_grS_c{c}', f'{prefix}net:deliver_grM_c{c}'))
            completes_c=join(steps,lambda label:label.startswith(f'core{c}:complete_'))
            ask_c=join(steps,lambda label:label.startswith(f'core{c}:ask_'))
            queue_c=o(m.pl(l,'rqR',c),m.pl(l,'rqW',c))
            queue_c1=o(m.pl(l,'rqR',c,nxt=True),m.pl(l,'rqW',c,nxt=True))
            goals[f'line{l}_core{c}__start_installs_active_transaction']=a(I,starts_c,neg(a(
                eq(m.pl(l,'tx',nxt=True),str(c)),neg(queue_c1),pending1)))
            goals[f'line{l}_core{c}__grant_clears_pending_and_sets_permission']=a(I,grants_c,neg(a(
                neg(pending1),o(eq(m.pl(l,'mode',c,nxt=True),'1'),eq(m.pl(l,'mode',c,nxt=True),'2')))))
            goals[f'line{l}_core{c}__ask_enqueues_pending_request']=a(I,ask_c,eq(m.cpu(c,'target'),str(l)),
                neg(a(pending1,queue_c1)))
            goals[f'line{l}_core{c}__completion_clears_busy']=a(I,completes_c,busy1)
            goals[f'line{l}_core{c}__pending_persists_until_grant']=a(I,pending,T,neg(grants_c),neg(pending1))
            goals[f'line{l}_core{c}__pending_belongs_to_busy']=a(I,pending,neg(busy))
            goals[f'line{l}_core{c}__busy_persists_until_completion']=a(I,busy,T,neg(completes_c),neg(busy1))
            # Ensure if service has acquired permission, an architectural completion
            # is in fact enabled -- with no data representability condition.
            base=a(I,busy,eq(m.cpu(c,'target'),str(l)),neg(pending))
            op=m.cpu(c,'op');mode=m.pl(l,'mode',c)
            r=o(eq(mode,'1'),eq(mode,'2'))
            for opname,idn,permission in [('read',1,r),('store',2,eq(mode,'2')),('cas',3,eq(mode,'2'))]:
                guard=fg[f'core{c}:complete_{opname}_line{l}']
                goals[f'line{l}_core{c}__{opname}_permission_enables_completion']=a(
                    base,eq(op,str(idn)),permission,neg(guard))
        # Some service for active transaction is continuously possible until it
        # fires; v1.6 additionally checks individual service guard persistence.
        active=neg(idle)
        service_guards=o(*(m.map_line(g,l) for label,g in pguards.items() if is_service(label)))
        goals[f'line{l}__active_has_service_enabled']=a(I,active,neg(service_guards))
    for c in range(n):
        q=m.x(c,'qlen');r=m.x(c,'ready');act=m.x(c,'load_active');conf=m.x(c,'load_confirmed')
        busy=m.cpu(c,'busy');busy1=m.cpu(c,'busy',True)
        # Two DISTINCT fairness events are needed. A scheduler that only fairly
        # executes "some resolution" could squash reads forever while ignoring
        # unconfirmed stores (squash_read does not change q > ready).
        queue_resolves=join(steps,lambda label:label in (f'core{c}:confirm', f'core{c}:squash_suffix'))
        queue_resolution_enabled=o(fg[f'core{c}:confirm'], fg[f'core{c}:squash_suffix'])
        unconfirmed_queue=f'(> {q} {r})'
        unconfirmed_queue1=f'(> {m.x(c,"qlen",True)} {m.x(c,"ready",True)})'
        goals[f'core{c}__unconfirmed_queue_can_resolve']=a(I,unconfirmed_queue,neg(queue_resolution_enabled))
        goals[f'core{c}__unconfirmed_queue_stable_until_resolution']=a(I,unconfirmed_queue,T,neg(queue_resolves),neg(unconfirmed_queue1))
        read_resolves=join(steps,lambda label:label in (f'core{c}:confirm', f'core{c}:squash_suffix',f'core{c}:squash_read'))
        read_resolution_enabled=o(fg[f'core{c}:confirm'],fg[f'core{c}:squash_suffix'],fg[f'core{c}:squash_read'])
        unconfirmed_read=a(act,neg(conf))
        unconfirmed_read1=a(m.x(c,'load_active',True),neg(m.x(c,'load_confirmed',True)))
        goals[f'core{c}__unconfirmed_read_can_resolve']=a(I,unconfirmed_read,neg(read_resolution_enabled))
        goals[f'core{c}__unconfirmed_read_stable_until_resolution']=a(I,unconfirmed_read,T,neg(read_resolves),neg(unconfirmed_read1))
        issue=join(steps,lambda label:label.startswith(f'core{c}:issue_confirmed_store_line'))
        issue_enabled=join(fg,lambda label:label.startswith(f'core{c}:issue_confirmed_store_line'))
        head=a(f'(> {r} 0)',neg(busy))
        head1=a(f'(> {m.x(c,"ready",True)} 0)',neg(busy1))
        goals[f'core{c}__confirmed_head_issues_when_not_busy']=a(I,head,neg(issue_enabled))
        goals[f'core{c}__confirmed_head_stable_until_issue']=a(I,head,T,neg(issue),neg(head1))
        settles=join(steps,lambda label:label.startswith(f'core{c}:spec_retire_fast_') or label.startswith(f'core{c}:spec_replay_'))
        settle_enabled=join(fg,lambda label:label.startswith(f'core{c}:spec_retire_fast_') or label.startswith(f'core{c}:spec_replay_'))
        settle=a(act,conf,eq(q,'0'),neg(busy))
        settle1=a(m.x(c,'load_active',True),m.x(c,'load_confirmed',True),eq(m.x(c,'qlen',True),'0'),neg(busy1))
        goals[f'core{c}__confirmed_read_has_settlement']=a(I,settle,neg(settle_enabled))
        goals[f'core{c}__confirmed_read_stable_until_settlement']=a(I,settle,T,neg(settles),neg(settle1))
        # The speculative read cannot lose confirmation without retiring or replaying.
        confirmed=a(act,conf)
        confirmed1=a(m.x(c,'load_active',True),m.x(c,'load_confirmed',True))
        goals[f'core{c}__confirmed_read_persists_until_settlement']=a(I,confirmed,T,neg(settles),neg(confirmed1))
    return goals


def run(cores=(4,),lines=(2,3),output=ROOT/'artifacts'/'temporal_fairness_v1_7'):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    summary={'version':'v1.7', 'branch':'proof/temporal-fairness-v1.7',
             'type':'concrete-transition SMT premises for compositional temporal fairness theorem',
             'fairness':'weak event fairness for servicing, starts, unconfirmed-store resolution, unconfirmed-read resolution, confirmed-store issue, load settlement; strong per-action fairness for CPU ask and completion',
             'configurations':{}}
    for n in cores:
      for k in lines:
        key=f'{n}cores_{k}lines';m=TemporalFairSpec(n,k)
        goals=lemmas(m);d=m.declarations();dest=output/key;dest.mkdir(exist_ok=True,parents=True)
        results={}
        for label,g in goals.items():
            query=d+'\n(assert '+g+')\n(check-sat)\n'
            (dest/(label+'.smt2')).write_text(query)
            start=time.monotonic();raw=z3_smt(query).strip();result=raw.splitlines()[0] if raw else 'error'
            results[label]={'result':result,'passed':result=='unsat','time_s':round(time.monotonic()-start,4),'sha256':hashlib.sha256(query.encode()).hexdigest()}
            print(key,label,result,flush=True)
        summary['configurations'][key]={'passed':all(v['passed'] for v in results.values()),'queries':len(results),'checks':results}
    summary['passed']=all(d['passed'] for d in summary['configurations'].values())
    (output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('V1.7 SMT PREMISES:', 'PASS' if summary['passed'] else 'FAIL',flush=True)
    return summary

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--cores',nargs='+',type=int,default=[4]);p.add_argument('--lines',nargs='+',type=int,default=[2,3]);p.add_argument('--output-dir',type=Path,default=ROOT/'artifacts'/'temporal_fairness_v1_7')
    a1=p.parse_args();sys.exit(0 if run(a1.cores,a1.lines,a1.output_dir)['passed'] else 1)
