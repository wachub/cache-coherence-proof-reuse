#!/usr/bin/env python3
"""Contract-based incremental verification of the EXISTING combined MSI model.

This is an *external proof harness*: no transition, invariant, or cache state
in the historical models is modified.  All contracts are expansions of the
existing model state and actual transition formulas.

Use Python stdlib + libz3.so.4; no z3py dependency.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from collections import OrderedDict

from fast_verify import (ROOT, EXPERIMENT, baseline_goals, full_system_goals,
                         load_combined, mutant_sensitivity, proof_cache_key,
                         solve_goals, z3_version)

FAMILIES = (
    'store_stage', 'resolve_speculation', 'store_issue', 'load_forward',
    'load_cache_capture', 'load_retire', 'load_replay',
)
STUTTER_FAMILIES = frozenset((
    'store_stage', 'resolve_speculation', 'load_forward', 'load_cache_capture'))
MODEL_FILES = (
    EXPERIMENT / 'combined_speculative_model.py',
    EXPERIMENT / 'sc_msi_4core_verifier.py',
    EXPERIMENT / 'cache_smt_verifier.py',
)


def family_of(label: str) -> str:
    """Exhaustive classification; fail closed if a future model adds an action."""
    action = label.split(':', 1)[-1]
    if action.startswith(('stage0_', 'stage1_')):
        return 'store_stage'
    if action in ('confirm', 'squash_suffix', 'squash_read'):
        return 'resolve_speculation'
    if action.startswith('issue_confirmed_store_'):
        return 'store_issue'
    if action.startswith('spec_forward_'):
        return 'load_forward'
    if action.startswith('spec_cache_'):
        return 'load_cache_capture'
    if action.startswith('spec_retire_fast_'):
        return 'load_retire'
    if action.startswith('spec_replay_'):
        return 'load_replay'
    raise ValueError(f'Unclassified transition (contract proof is incomplete): {label}')


def partition_transitions(model):
    result = OrderedDict((family, []) for family in FAMILIES)
    steps = model.delta_steps()
    labels = set()
    for label, formula in steps:
        if label in labels:
            raise AssertionError(f'Duplicate transition label: {label}')
        labels.add(label)
        result[family_of(label)].append((label, formula))
    if len(steps) != sum(map(len, result.values())) or any(not steps for steps in result.values()):
        raise AssertionError('Transition partition incomplete or empty')
    return result


def _contracts(model):
    """Typed architectural effect for each *existing* transition family.

    Stronger than the old generic interface's union: a store-issue must
    actually issue the oldest confirmed store, not merely stutter.
    """
    from sc_msi_4core_verifier import a, o, eq, neg
    contracts = {name: model._old_stutter() for name in STUTTER_FAMILIES}
    cases = {name: [] for name in ('store_issue', 'load_retire', 'load_replay')}
    for c in range(model.n):
        busy = model.cpu(c, 'busy')
        q = model.x(c, 'qlen')
        r = model.x(c, 'ready')
        active = model.x(c, 'load_active')
        confirmed = model.x(c, 'load_confirmed')
        for l in range(model.k):
            cases['store_issue'].append(a(
                neg(busy), f'(> {r} 0)', eq(model.x(c, 'addr0'), str(l)),
                model._old_patch({
                    f'busy_{c}': 'true', f'op_{c}': '2',
                    f'target_{c}': str(l), f'newval_{c}': model.x(c, 'value0')
                })))
            read_guard = a(neg(busy), eq(q, '0'), active, confirmed,
                           eq(model.x(c, 'load_addr'), str(l)))
            cases['load_retire'].append(a(
                read_guard,
                eq(model.x(c, 'load_value'),
                   f'(select payload_{l} {model.v(f"ref_{l}")})'),
                model._old_patch({f'observed_{c}': model.x(c, 'load_value')})))
            cases['load_replay'].append(a(
                read_guard,
                model._old_patch({f'busy_{c}': 'true', f'op_{c}': '1',
                                  f'target_{c}': str(l)})))
    contracts.update({name: o(*items) for name, items in cases.items()})
    return OrderedDict((name, contracts[name]) for name in FAMILIES)


def _definition(name: str, expr: str) -> str:
    return f'(define-fun {name} () Bool {expr})\n'


def build_layers(model):
    """Return a shared SMT-LIB namespace and small contract-level queries."""
    from sc_msi_4core_verifier import System, a, o, neg, eq
    families = partition_transitions(model)
    contracts = _contracts(model)

    # Named DAG nodes: SMT-LIB define-fun is portable, unlike a private
    # Python-side string abbreviation or a hypothetical SMT include command.
    names = [
        ('msi_inv', System.inv(model)),
        ('msi_inv_next', System.inv(model, True)),
        ('spec_inv', model.new_inv()),
        ('spec_inv_next', model.new_inv(True)),
        ('arch_interface', model.interface_contract()),
    ]
    for name, contract in contracts.items():
        names.append((f'contract_{name}', contract))
    for name, steps in families.items():
        names.append((f'delta_{name}', o(*(s for _, s in steps))))
    names.append(('delta_all', o(*(f'delta_{name}' for name in FAMILIES))))
    names.append(('inherited', o(*(s for _, s in model.inherited_steps()))))
    prelude = ('; Compositional CONTRACT LIBRARY, generated from unchanged models\n'
               '; For exact assurance do not edit by hand; rerun generation.\n'
               + model.declarations() + '\n'
               + ''.join(_definition(n, e) for n,e in names))

    premises = '(and msi_inv spec_inv)'
    goals = OrderedDict()
    goal_group = {}
    def add(name, group, formula):
        goals[name] = formula
        goal_group[name] = group

    add('spec_initial', 'foundation', a(model.init(), neg('spec_inv')))
    add('inherited_preserves_spec', 'frame', a(premises, 'inherited', neg('spec_inv_next')))
    add('inherited_preserves_msi', 'frame', a(premises, 'inherited', neg('msi_inv_next')))
    # For every new action family: inheritance from old MSI, speculation
    # well-formedness, and the *typed* architectural event contract.
    for family in FAMILIES:
        cond = a(premises, f'delta_{family}')
        add(f'{family}__preserves_msi', family, a(cond, neg('msi_inv_next')))
        add(f'{family}__preserves_spec', family, a(cond, neg('spec_inv_next')))
        add(f'{family}__satisfies_typed_contract', family,
            a(cond, neg(f'contract_{family}')))
    # Check the modular contracts collectively are exactly the original
    # interface, rather than silently specifying a different memory model.
    family_union = o(*(f'contract_{name}' for name in FAMILIES))
    add('typed_contracts_equal_original_interface', 'foundation',
        neg(eq('arch_interface', family_union)))
    # The transition partition is complete by construction and independently
    # checked as an SMT equivalence. No unclassified new actions are omitted.
    old_delta = o(*(s for _,s in model.delta_steps()))
    add('transition_partition_exact', 'foundation',neg(eq('delta_all',old_delta)))

    # The already-verified semantics-specific checks remain separate reusable
    # contracts; merely maintaining old MSI invariants is not enough.
    earlier = model.proof_goals()
    add('read_result_correct', 'load_retire', earlier['fast_read_returns_current_value'])
    add('youngest_store_forwarded', 'load_forward', earlier['forwarding_uses_youngest_prior_store'])
    add('read_order_respected', 'load_retire', earlier['fast_read_not_before_prior_memory_ops'])
    return prelude, goals, families, contracts, goal_group



def sliced_contexts(model, all_goals, goal_group):
    """Build MINIMAL contract contexts, with unrelated delta families absent.

    An added transition within family A therefore does not invalidate the
    exact proof-cache key for unchanged family B. A changed shared invariant,
    state declaration, or observable contract does invalidate relevant proofs.
    """
    from sc_msi_4core_verifier import System, o
    family_steps = partition_transitions(model)
    contracts = _contracts(model)
    base = (model.declarations() + '\n'
            + _definition('msi_inv', System.inv(model))
            + _definition('msi_inv_next', System.inv(model,True))
            + _definition('spec_inv', model.new_inv())
            + _definition('spec_inv_next', model.new_inv(True)))
    contexts = {}
    for name, group in goal_group.items():
        if name == 'typed_contracts_equal_original_interface':
            tail = _definition('arch_interface', model.interface_contract())
            tail += ''.join(_definition('contract_'+f,contracts[f]) for f in FAMILIES)
        elif name == 'transition_partition_exact':
            tail = ''.join(_definition('delta_'+f,o(*(s for _,s in family_steps[f])))
                           for f in FAMILIES)
            tail += _definition('delta_all',o(*(f'delta_{f}' for f in FAMILIES)))
        elif name in ('inherited_preserves_spec','inherited_preserves_msi'):
            tail = _definition('inherited',o(*(s for _,s in model.inherited_steps())))
        elif group in FAMILIES:
            tail = (_definition('contract_'+group,contracts[group])
                    + _definition('delta_'+group,o(*(s for _,s in family_steps[group]))))
        else:
            tail = ''
        contexts[name] = base + tail
    return contexts


def solve_sliced(contexts, goals, *, cache_dir, timeout_ms=0, seed=0):
    """Batch goals that share a context; cache only the exact dependencies."""
    import time
    start=time.monotonic()
    by_context=OrderedDict()
    for name,goal in goals.items():
        by_context.setdefault(contexts[name],OrderedDict())[name]=goal
    found={}
    cache_hits=0
    solved=0
    for declaration_context,group in by_context.items():
        outcome=solve_goals(declaration_context,group,cache_dir=cache_dir,
                            timeout_ms=timeout_ms,seed=seed)
        found.update(outcome['goals'])
        cache_hits+=outcome['cache_hits']
        solved+=outcome['solved']
    ordered=OrderedDict((name,found[name]) for name in goals)
    return {'passed':all(v['status']=='unsat' for v in ordered.values()),
            'solver_version':z3_version(),'mode':'sliced',
            'seconds':round(time.monotonic()-start,4),'cache_hits':cache_hits,
            'solved':solved,'solver_contexts':len(by_context),'goals':ordered}


def _file_hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_bundle(output: Path, model, prelude: str, goals, families, goal_group, *,
                 report: dict|None=None):
    """Emit small include-like fragments AND one standalone portable SMT file.

    SMT-LIB 2 doesn't mandate a #include: any standalone proof file must
    repeat declarations, but within a session define-fun nodes are shared.
    """
    output.mkdir(parents=True,exist_ok=True)
    (output/'shared_contracts.smt2').write_text(prelude)
    fragment_dir = output/'goals'
    fragment_dir.mkdir(exist_ok=True)
    steps = []
    for name,goal in goals.items():
        fragment = f'; {name}\n(push 1)\n(assert {goal})\n(check-sat)\n(pop 1)\n'
        (fragment_dir/f'{name}.smt2frag').write_text(fragment)
        steps.append(fragment)
    (output/'all_contract_queries.smt2').write_text(prelude+'\n'+''.join(steps)+'(exit)\n')
    slices = sliced_contexts(model,goals,goal_group)
    minimal_dir = output/'sliced_queries'
    minimal_dir.mkdir(exist_ok=True)
    for name,goal in goals.items():
        (minimal_dir/f'{name}.smt2').write_text(
            slices[name]+'\n(assert '+goal+')\n(check-sat)\n(exit)\n')
    schema = {
        'format': 'compositional-contract-manifest-v1',
        'claims': 'SMT-LIB2 scoped inductive checks, NOT a certified SC trace refinement',
        'configuration': {'cores':model.n, 'lines':model.k, 'write_queue_capacity':2,
                          'younger_speculative_load_capacity':1},
        'source_hashes': {str(f.relative_to(ROOT)): _file_hash(f) for f in MODEL_FILES},
        'shared_contracts_sha256': hashlib.sha256(prelude.encode()).hexdigest(),
        'transition_families': {
            name: {'count':len(items),'action_labels':[lab for lab,_ in items]}
            for name,items in families.items()},
        'goals': {name:{'layer':goal_group[name],
                         'sha256':hashlib.sha256((prelude+goal).encode()).hexdigest(),
                        'sliced_context_sha256':hashlib.sha256(slices[name].encode()).hexdigest(),
                        'sliced_query_sha256':hashlib.sha256((slices[name]+goal).encode()).hexdigest(),
                        'requires':['baseline_MSI_inductive','spec_inv']
                        if name not in ('spec_initial','transition_partition_exact','typed_contracts_equal_original_interface')
                        else []} for name,goal in goals.items()},
        'result':report,
    }
    (output/'contract_manifest.json').write_text(json.dumps(schema,indent=2)+'\n')
    return schema


def mutant_contract_tests(model):
    from sc_msi_4core_verifier import System, a, o, neg
    typed = _contracts(model)['load_retire']
    checks = OrderedDict()
    for mutant in ('unvalidated_read','premature_read'):
        changes = (formula for label,formula in model.delta_steps(mutant=mutant)
                   if family_of(label)=='load_retire')
        checks[mutant] = a(System.inv(model),model.new_inv(),o(*changes),neg(typed))
    # Negative control demonstrating that the old *generic* interface is too
    # weak by itself: stuttering while 'issuing' a store is permitted by its
    # broad union, but forbidden by the family-specific store-issue contract.
    from sc_msi_4core_verifier import eq
    c=0
    bad_issue=model.step('mutant:stuttering_store_issue',
        a(eq(model.x(c,'qlen'),'1'),eq(model.x(c,'ready'),'1'),
          neg(model.cpu(c,'busy'))),
        {f'spec_qlen_{c}':'0',f'spec_ready_{c}':'0'})[1]
    checks['stuttering_store_issue'] = a(
        System.inv(model),model.new_inv(),bad_issue,
        model.interface_contract(),neg(_contracts(model)['store_issue']))
    result=solve_goals(model.declarations(),checks,cache_dir=None)
    result['detected'] = all(v['status']=='sat' for v in result['goals'].values())
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cores', type=int, default=4)
    p.add_argument('--lines', type=int, default=2)
    p.add_argument('--output-dir', type=Path)
    p.add_argument('--cache-dir', type=Path, default=ROOT/'.proof_cache')
    p.add_argument('--no-cache', action='store_true')
    p.add_argument('--baseline', action='store_true', help='recheck the inherited MSI proof')
    p.add_argument('--full-regression', action='store_true', help='independent full-system induction')
    p.add_argument('--check-mutants', action='store_true')
    p.add_argument('--execution', choices=('sliced','shared'),default='sliced',
                   help='sliced contexts cache each proof by its contract dependencies')
    p.add_argument('--only', choices=FAMILIES,
                   help='fast feedback on one contract family; not a complete proof')
    p.add_argument('--timeout-ms', type=int, default=0)
    p.add_argument('--seed', type=int, default=0)
    args=p.parse_args()
    model=load_combined(args.cores,args.lines)
    prelude,all_goals,families,_,groups=build_layers(model)
    selected = (OrderedDict((k,v) for k,v in all_goals.items()
                           if groups[k] in ('foundation','frame',args.only))
                if args.only else all_goals)
    cache = None if args.no_cache else args.cache_dir
    if args.execution=='sliced':
        contexts=sliced_contexts(model, all_goals,groups)
        result=solve_sliced(contexts,selected,cache_dir=cache,
                            timeout_ms=args.timeout_ms,seed=args.seed)
    else:
        result=solve_goals(prelude,selected,cache_dir=cache,
                           timeout_ms=args.timeout_ms,seed=args.seed)
    result['complete_contract_suite'] = args.only is None
    result['module_counts']={name:len(items) for name,items in families.items()}
    if args.baseline:
        decl,base_goals=baseline_goals(args.cores,args.lines)
        result['baseline']=solve_goals(decl,base_goals,cache_dir=cache,
                                       timeout_ms=args.timeout_ms,seed=args.seed)
    if args.full_regression:
        result['full_regression']=solve_goals(model.declarations(),full_system_goals(model),
                                cache_dir=cache,timeout_ms=args.timeout_ms,seed=args.seed)
    if args.check_mutants:
        result['mutants']=mutant_contract_tests(model)
    result['all_requested_checks_passed']=(result['passed'] and
        (not args.baseline or result['baseline']['passed']) and
        (not args.full_regression or result['full_regression']['passed']) and
        (not args.check_mutants or result['mutants']['detected']))
    if args.output_dir:
        write_bundle(args.output_dir, model, prelude, all_goals,families,groups,report=result)
    print(json.dumps(result,indent=2))
    if not result['all_requested_checks_passed']:
        raise SystemExit(1)

if __name__=='__main__': main()
