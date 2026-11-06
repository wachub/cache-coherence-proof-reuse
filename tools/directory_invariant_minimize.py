#!/usr/bin/env python3
"""Sound, solver-backed redundancy analysis for v1.7 directory invariant schemas.

Each candidate is one schema simultaneously removed from EVERY core and cache
line. "redundant" means that all other retained invariant conjuncts imply the
removed schema, not that a single one-step induction query happened to pass.
An inclusion-minimal collection need not have minimum cardinality.

No protocol state/transition rules are changed. This experiment does not claim
that SAT states are reachable, nor that local redundancy implies temporal liveness.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from temporal_v17_verify import TemporalFairSpec
from cache_smt_verifier import a, neg, z3_smt

# Protocol.invariant_terms() = 8 global terms, then 33 clauses per core.
GLOBAL={
 0:'field_domain_bounds',1:'memory_version_bound',2:'unowned_memory_is_latest',
 3:'owner_excludes_directory_sharers',4:'active_transaction_has_valid_kind',
 5:'owner_during_phase0_retains_dirty_data',6:'idle_directory_has_no_inflight_messages',
 7:'grant_phase_has_active_transaction_and_no_waiters',
}
LOCAL={
 0:'modified_cache_has_exclusive_owner_and_latest_value',
 1:'directory_sharer_metadata_supported',
 2:'shared_cache_has_latest_value_and_owner_metadata',
 3:'no_simultaneous_read_write_requests',4:'read_request_implies_pending_invalid',
 5:'write_request_implies_pending_invalid_or_shared',
 6:'pending_has_queue_or_active_transaction',
 7:'active_phase0_requester_is_pending',
 8:'active_phase0_requester_not_also_queued',
 9:'outstanding_grant_implies_no_queue',
 10:'active_phase0_read_requester_invalid',
 11:'invalidation_message_matches_phase_and_sharer',
 12:'recall_message_matches_phase_and_owner',
 13:'ack_message_matches_phase_and_sharer',
 14:'writeback_message_matches_phase_and_data',
 15:'shared_grant_matches_requester_and_version',
 16:'modified_grant_matches_requester_and_version',
 17:'grant_ack_matches_transaction_and_latest_data',
 18:'phase1_has_some_grant_or_ack',
 19:'write_grant_ack_implies_modified_owner',
 20:'pending_grant_ack_has_a_queued_request',
 21:'read_grant_ack_implies_shared_metadata',
 22:'no_simultaneous_inv_and_recall',23:'no_simultaneous_inv_and_ack',
 24:'no_simultaneous_inv_and_writeback',25:'no_simultaneous_recall_and_ack',
 26:'no_simultaneous_recall_and_writeback',27:'no_simultaneous_ack_and_writeback',
 28:'phase0_owner_must_be_waited_for',
 29:'phase0_writer_waits_for_other_sharer',
 30:'waiter_requires_inflight_message',
 31:'inflight_message_requires_waiter',
 32:'stale_directory_memory_preserved_in_modified_or_writeback',
}

# Conservative directory/interface group. Keep explicit architectural safety,
# data freshness, and domain clauses, and examine all protocol control metadata.
DIRECTORY={*(f'G{i:02}' for i in range(3,8)),
           *(f'C{i:02}' for i in [1,*range(3,32)])}
ALL={*(f'G{i:02}' for i in GLOBAL), *(f'C{i:02}' for i in LOCAL)}


def schema_name(name):
    return GLOBAL[int(name[1:])] if name.startswith('G') else LOCAL[int(name[1:])]


def indexed_terms(model,nxt=False):
    pieces=model.p.invariant_terms(nxt)
    expected=8+33*model.n
    if len(pieces)!=expected:
        raise AssertionError(f'protocol schema changed: {len(pieces)} != {expected}')
    out=[(f'G{i:02}',pieces[i]) for i in range(8)]
    for c in range(model.n):
        out.extend((f'C{j:02}',pieces[8+33*c+j]) for j in range(33))
    return out


def protocol_with_removed(model,removed,nxt=False):
    terms=[t for name,t in indexed_terms(model,nxt) if name not in removed]
    return a(*terms)


def clauses_by_schema(model,selected,nxt=False):
    out=[]
    for l in range(model.k):
        for name,expr in indexed_terms(model,nxt):
            if name in selected:
                out.append(model.map_line(expr,l))
    return a(*out)


def invariant_without(model,removed,nxt=False):
    # Reconstruct exactly the already-proved invariant, replacing ONLY the
    # per-line cache protocol sub-conjunctions. This avoids accidentally
    # dropping CPU, speculative, payload, or RR bounds.
    inv=TemporalFairSpec.inv(model,nxt)
    for l in range(model.k):
        original=model.map_line(model.p.inv(nxt),l)
        reduced=model.map_line(protocol_with_removed(model,removed,nxt),l)
        if inv.count(original)!=1:
            raise AssertionError(f'expected exactly one per-line occurrence: {l}')
        inv=inv.replace(original,reduced,1)
    return inv


def query(model,formula,timeout_ms=20000,model_values=False):
    hdr=f'(set-option :timeout {timeout_ms})\n'
    txt=hdr+model.declarations()+'\n(assert '+formula+')\n(check-sat)\n'
    if model_values:
        fields=[model.pl(0,'tx'),model.pl(0,'phase'),model.pl(0,'kind'),
                model.pl(0,'owner'),model.pl(0,'wait',0),
                model.pl(0,'inv',0),model.pl(0,'grM',0),
                model.pl(0,'mode',0)]
        txt+='(get-value ('+' '.join(fields)+'))\n'
    start=time.monotonic()
    raw=z3_smt(txt).strip()
    status=raw.splitlines()[0] if raw else 'error'
    return {'status':status, 'seconds':round(time.monotonic()-start,4),
            'sha256':hashlib.sha256(txt.encode()).hexdigest(),
            'model_excerpt':raw[4:1200] if model_values and status=='sat' else None},txt


def minimize_one(n,k,out,timeout_ms=20000,candidates=DIRECTORY):
    m=TemporalFairSpec(n,k)
    out.mkdir(exist_ok=True,parents=True)
    results={'config':f'{n}cores_{k}lines','model':'TemporalFairSpec_v1.7',
             'candidate_definitions':{x:schema_name(x) for x in sorted(candidates)},
             'meaning':'solver-checked logical equivalence of all retained conjuncts',
             'results':{},'removed':[],'retained':[]}
    init_status,_=query(m,a(m.init(),m.inv()),timeout_ms)
    results['init_is_consistent']=init_status
    if init_status['status']!='sat':raise RuntimeError('Full invariant not satisfiable in initial state')
    removed=set()
    clause_output=out/'schema_checks'
    clause_output.mkdir(exist_ok=True)
    for schema in sorted(candidates):
        proposed=removed|{schema}
        prem=invariant_without(m,proposed)
        deleted=clauses_by_schema(m,{schema})
        check=a(prem,neg(deleted))
        record,qtext=query(m,check,timeout_ms)
        (clause_output/(schema+'.smt2')).write_text(qtext)
        record.update({'schema':schema_name(schema),'interpretation':'unsat=logically redundant; sat=independent; unknown=inconclusive'})
        results['results'][schema]=record
        if record['status']=='unsat':
            removed.add(schema)
            record['removed']=True
        elif record['status']=='sat':
            record['removed']=False
        else:
            record['removed']=False
        print(f'{n}c {k}l {schema} {schema_name(schema)} {record["status"]} {record["seconds"]:.3f}s',flush=True)
    results['removed']=sorted(removed)
    results['retained']=sorted(set(candidates)-removed)
    results['removed_count']=len(removed)
    # One final check that the entire removed conjunction follows from the
    # resulting invariant. This is stronger than separate per-schema checks.
    if removed:
        implication=a(invariant_without(m,removed),neg(clauses_by_schema(m,removed)))
        result,querytext=query(m,implication,timeout_ms)
        (out/'reduced_implies_all_removed.smt2').write_text(querytext)
        results['reduced_implies_all_removed']=result
        if result['status']!='unsat':raise RuntimeError('Global equivalence check failed: '+repr(result))
    else:
        results['reduced_implies_all_removed']={'status':'vacuous'}
    # The reverse direction is syntactic since the reduced invariant removes
    # conjuncts. Nonetheless, check the same fixed-size, concrete transition
    # system's initiation/induction/safety for the reduced form.
    inv=invariant_without(m,removed)
    checks={
        'initial':a(m.init(),neg(inv)),
        'inductive_step':a(inv,m.T(),neg(invariant_without(m,removed,True))),
        'safety':a(inv,m.v('bad')),
    }
    for label,formula in checks.items():
        print(f'{n}c {k}l checking {label}',flush=True)
        rec,qt=query(m,formula,timeout_ms=max(timeout_ms,60000))
        (out/(label+'.smt2')).write_text(qt)
        results[label]=rec
        print(f'{n}c {k}l {label} {rec["status"]} {rec["seconds"]:.3f}s',flush=True)
    if any(results[x]['status']!='unsat' for x in checks):
        raise RuntimeError('One or more key post-minimization proofs did not pass')
    # Test if all directory clauses could have been omitted while retaining
    # the other categories. SAT means directory information is not implied.
    all_dir_removed=invariant_without(m,candidates)
    violation=clauses_by_schema(m,candidates)
    result,qtext=query(m,a(all_dir_removed,neg(violation)),timeout_ms,model_values=True)
    (out/'remove_entire_directory_block.smt2').write_text(qtext)
    results['other_invariants_imply_all_directory_clauses']=result
    results['success']=True
    (out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
    return results


# Solver-discovered schema set, common to 4x2 and 4x3 configurations.
# This removes ASSERTED conjuncts only, not safety requirements or transitions.
REMOVED_SCHEMAS=frozenset({'C03','C22','C23','C24','C25','C26','C27','C31','G05','G07'})

class MinimizedDirectorySpec(TemporalFairSpec):
    """Original transition system with a logically equivalent reduced invariant.

    Logical equivalence has been checked for 4 cores x 2/3 lines; use other
    configurations only after checking their own equivalence/proof obligations.
    """
    def inv(self,nxt=False):
        return invariant_without(self,REMOVED_SCHEMAS,nxt)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cores',type=int,nargs='+',default=[4])
    p.add_argument('--lines',type=int,nargs='+',default=[2,3])
    p.add_argument('--timeout-ms',type=int,default=15000)
    p.add_argument('--output',type=Path,default=ROOT/'artifacts'/'directory_minimization_v1_8')
    args=p.parse_args()
    if min(args.cores)<=0 or min(args.lines)<=0: p.error('cores/lines must be positive')
    summary={}
    for n in args.cores:
        for k in args.lines:
            name=f'{n}cores_{k}lines'
            summary[name]=minimize_one(n,k,args.output/name,args.timeout_ms)
    (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('FINAL',json.dumps({key:{'removed':r['removed'], 'retained':r['retained'],
            'block_status':r['other_invariants_imply_all_directory_clauses']['status']}
            for key,r in summary.items()},indent=2),flush=True)

if __name__=='__main__':main()
