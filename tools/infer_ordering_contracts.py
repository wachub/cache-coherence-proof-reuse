#!/usr/bin/env python3
"""SMT-guided *template* inference of speculative-ordering effect contracts.

External verification harness only: imports existing model unchanged.

We DO NOT discover arbitrary new semantics. The user-defined effect vocabulary
(stutter / store issue / read retire / read replay) specifies the abstraction;
Z3 selects an irredundant family-specific disjunction from that vocabulary.
Each generated contract comes with a solver-checked coverage certificate and a
one-step feasibility check. A separately checked handwritten v1.3 contract is
an optional regression oracle, not an input to the learner.

The proof is for the *fixed* configurations of the existing MSI/speculation
model, conditional on its existing inductive invariants. It is not a complete
mechanized trace-level sequential-consistency refinement proof.
"""
from __future__ import annotations

import argparse
from collections import OrderedDict
import hashlib
import json
from pathlib import Path

from compositional_verify import (_contracts, FAMILIES, MODEL_FILES,
                                  partition_transitions, _definition)
from fast_verify import (ROOT, load_combined, proof_cache_key, solve_goals,
                         z3_version)

EFFECT_TYPES = ('stutter', 'issue_store', 'retire_read', 'replay_read')


def effect_vocabulary(model):
    """Abstract one-step event grammar, independent of the action families.

    All effects are expressed over *existing* old MSI state. The grammar
    describes observable interface actions, not a family's implementation.
    Formula construction deliberately does not call v1.3's _contracts().
    """
    from sc_msi_4core_verifier import a, o, eq, neg
    effect = OrderedDict([('stutter', model._old_stutter())])
    issue, retire, replay = [], [], []
    for c in range(model.n):
        busy = model.cpu(c, 'busy')
        queue = model.x(c, 'qlen')
        ready = model.x(c, 'ready')
        active = model.x(c, 'load_active')
        confirmed = model.x(c, 'load_confirmed')
        for l in range(model.k):
            # Only the published architectural operation is in the grammar;
            # internals of the speculative queues are not touched.
            issue.append(a(
                neg(busy), f'(> {ready} 0)',
                eq(model.x(c, 'addr0'), str(l)),
                model._old_patch({
                    f'busy_{c}': 'true', f'op_{c}': '2',
                    f'target_{c}': str(l),
                    f'newval_{c}': model.x(c, 'value0'),
                })))
            head_done = a(neg(busy), eq(queue, '0'), active, confirmed,
                          eq(model.x(c, 'load_addr'), str(l)))
            retire.append(a(
                head_done,
                eq(model.x(c, 'load_value'),
                   f'(select payload_{l} {model.v(f"ref_{l}")})'),
                model._old_patch({f'observed_{c}': model.x(c, 'load_value')})))
            replay.append(a(
                head_done,
                model._old_patch({
                    f'busy_{c}': 'true', f'op_{c}': '1',
                    f'target_{c}': str(l),
                })))
    effect['issue_store'] = o(*issue)
    effect['retire_read'] = o(*retire)
    effect['replay_read'] = o(*replay)
    return effect


def _base_context(model, effects):
    from sc_msi_4core_verifier import System
    return (model.declarations() + '\n'
            + _definition('base_msi_inv', System.inv(model))
            + _definition('base_spec_inv', model.new_inv())
            + ''.join(_definition(f'effect_{key}', formula)
                      for key, formula in effects.items()))


def _and(*terms):
    from sc_msi_4core_verifier import a
    return a(*terms)


def _or(*terms):
    from sc_msi_4core_verifier import o
    return o(*terms)


def _not(term):
    from sc_msi_4core_verifier import neg
    return neg(term)


def certificate_key(context: str, goal: str, timeout_ms=0, seed=0):
    """Exact dependency key: unchanged other families cannot affect it."""
    return proof_cache_key(context, goal, timeout_ms, seed, z3_version())


def family_context(model, base, actions, family):
    return base + _definition(f'family_{family}', _or(*(step for _,step in actions)))


def prove_contracts(model, *, cache_dir=None, timeout_ms=0, seed=0,
                    compare_handwritten=True, previous_manifest=None):
    """Infer by sound Houdini-style elimination from an explicit event grammar.

    A candidate event can be removed only when Z3 proves every transition in
    the family satisfies some *other* candidate. This guarantees coverage.
    The result is irredundant with respect to the elimination order; it is
    not guaranteed globally minimum among all Boolean expressions.
    """
    effects = effect_vocabulary(model)
    families = partition_transitions(model)
    base = _base_context(model, effects)
    oracle = _contracts(model) if compare_handwritten else None
    if previous_manifest is not None:
        if not previous_manifest.get('all_passed',False):
            raise ValueError('Previous certificate manifest does not report successful proof')
        if previous_manifest.get('format') != 'smt-inferred-contracts-v1':
            raise ValueError('Unsupported previous contract manifest format')
        if previous_manifest.get('configuration') != {
                'cores':model.n, 'lines':model.k,
                'max_speculative_stores':2,'max_speculative_reads':1}:
            raise ValueError('Changed model parameters: no automatic contract proof reuse')
        if previous_manifest.get('shared_abstraction_sha256') != hashlib.sha256(base.encode()).hexdigest():
            raise ValueError('Shared state declarations, invariants or event grammar changed: '
                             'cannot reuse old contracts without a new cross-abstraction proof')
    result = OrderedDict()
    cache = cache_dir

    for family, actions in families.items():
        ctx = family_context(model, base, actions, family)
        family_atom = f'family_{family}'
        pre = _and('base_msi_inv', 'base_spec_inv', family_atom)
        full = _or(*(f'effect_{kind}' for kind in EFFECT_TYPES))
        initial = OrderedDict([
            ('family_feasible', pre),
            ('effect_grammar_covers_all_steps', _and(pre, _not(full))),
        ])
        checks = solve_goals(ctx, initial, cache_dir=cache,
                             timeout_ms=timeout_ms, seed=seed)
        if checks['goals']['family_feasible']['status'] != 'sat':
            raise RuntimeError(f'{family}: unsatisfiable or unknown transition family; '
                               'refusing to infer a vacuous contract')
        if checks['goals']['effect_grammar_covers_all_steps']['status'] != 'unsat':
            raise RuntimeError(f'{family}: effect vocabulary is incomplete or solver '
                               f'could not prove coverage ({checks["goals"]["effect_grammar_covers_all_steps"]["status"]})')

        selected = list(EFFECT_TYPES)
        elimination = OrderedDict()
        # This order is a documented heuristic. If a stuttering alternative is
        # dispensable we prefer an explicit architectural effect. Other ties
        # are resolved in vocabulary order, not by a claim of uniqueness.
        for kind in EFFECT_TYPES:
            remaining = [other for other in selected if other != kind]
            q = _and(pre, _not(_or(*(f'effect_{x}' for x in remaining))))
            name = f'remove_{kind}'
            res = solve_goals(ctx, {name:q}, cache_dir=cache,
                              timeout_ms=timeout_ms, seed=seed)
            status = res['goals'][name]['status']
            elimination[name] = {
                **res['goals'][name],
                'key':certificate_key(ctx, q, timeout_ms, seed),
            }
            if status == 'unsat':
                selected.remove(kind)
            elif status == 'unknown':
                raise RuntimeError(f'{family}: unknown while minimizing {kind}')
        if not selected:
            raise AssertionError(f'{family}: empty inferred contract despite feasible actions')
        inferred = _or(*(f'effect_{x}' for x in selected))
        coverage_goal = _and(pre, _not(inferred))
        post = solve_goals(ctx, {'synthesized_contract_coverage':coverage_goal},
                           cache_dir=cache, timeout_ms=timeout_ms, seed=seed)
        if not post['passed']:
            raise RuntimeError(f'{family}: final learned contract not proved')

        compatible = None
        if oracle is not None:
            # Oracle is strictly a test fixture: no oracle formula or assumed
            # family classification influences inference or elimination.
            oracle_ctx = ctx + _definition('manual_regression_oracle', oracle[family])
            oracle_goals = {
                'learned_implies_manual': _and('base_msi_inv', 'base_spec_inv',
                                               inferred, _not('manual_regression_oracle')),
                'manual_implies_learned': _and('base_msi_inv', 'base_spec_inv',
                                               'manual_regression_oracle', _not(inferred)),
            }
            chk = solve_goals(oracle_ctx,oracle_goals, cache_dir=cache,
                              timeout_ms=timeout_ms,seed=seed)
            compatible = {
                'equivalent_under_invariants': chk['passed'],
                'goals':chk['goals'],
            }
            if not compatible['equivalent_under_invariants']:
                raise RuntimeError(f'{family}: inferred contract differs from verified '
                                   'v1.3 handwritten reference contract')

        reuse = None
        if previous_manifest is not None:
            previous_fam = previous_manifest.get('families',{}).get(family)
            if previous_fam is None:
                reuse = {'status':'new_family_no_existing_contract'}
            else:
                if (previous_fam.get('final_coverage',{}).get('status') != 'unsat'
                    or previous_fam.get('feasibility',{}).get('status') != 'sat'):
                    raise ValueError(f'{family}: previous certificate not validated')
                prior_events = previous_fam.get('selected_events',[])
                if not prior_events or any(e not in EFFECT_TYPES for e in prior_events):
                    raise ValueError(f'{family}: malformed prior event certificate')
                prior_contract = _or(*(f'effect_{x}' for x in prior_events))
                implication = _and('base_msi_inv','base_spec_inv',inferred,_not(prior_contract))
                res = solve_goals(ctx,{'preserves_previous_contract':implication},
                                  cache_dir=cache,timeout_ms=timeout_ms,seed=seed)
                status = res['goals']['preserves_previous_contract']['status']
                if status != 'unsat':
                    raise RuntimeError(f'{family}: proposed model weakens a previously '
                                       f'certified ordering contract ({status})')
                same_query = (previous_fam.get('certificate_key') ==
                              certificate_key(ctx,coverage_goal,timeout_ms,seed))
                reuse = {'status':('unchanged_exact_certificate' if same_query
                                   else 'changed_family_reverified_compatible'),
                         'old_contract_events':prior_events,
                         'backward_implication':res['goals']['preserves_previous_contract']}

        # A family-local proof hash excludes all OTHER transition families;
        # any change to the common abstraction/invariants correctly expires it.
        result[family] = {
            'selected_events': selected,
            'actions':len(actions),
            'transition_labels':[lab for lab,_ in actions],
            'feasibility':checks['goals']['family_feasible'],
            'grammar_coverage':checks['goals']['effect_grammar_covers_all_steps'],
            'elimination':elimination,
            'final_coverage':post['goals']['synthesized_contract_coverage'],
            'certificate_key':certificate_key(ctx, coverage_goal,timeout_ms,seed),
            'context_sha256': hashlib.sha256(ctx.encode()).hexdigest(),
            'effect_formula':inferred,
            'oracle':compatible,
            'reuse_assessment':reuse,
            'passed':post['passed'],
        }
    return {
        'format':'smt-inferred-contracts-v1',
        'scope':'one-step safety under inherited MSI+speculation invariants, not trace refinement',
        'configuration':{'cores':model.n,'lines':model.k,
                         'max_speculative_stores':2,'max_speculative_reads':1},
        'engine':'Z3 SMT-LIB via libz3',
        'solver_version':z3_version(),
        'model_hashes':{str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                        for path in MODEL_FILES},
        'abstraction_events':list(EFFECT_TYPES),
        'shared_abstraction_sha256':hashlib.sha256(base.encode()).hexdigest(),
        'all_passed':all(v['passed'] for v in result.values()),
        'families':result,
    }


def write_proof_bundle(dest:Path, model, report):
    """Export self-contained SMT-LIB2 proof scripts and a compact manifest."""
    dest.mkdir(parents=True, exist_ok=True)
    effects=effect_vocabulary(model)
    base=_base_context(model,effects)
    families=partition_transitions(model)
    for family, actions in families.items():
        context=family_context(model,base,actions,family)
        selected=report['families'][family]['selected_events']
        goal=_and('base_msi_inv','base_spec_inv',f'family_{family}',
                  _not(_or(*(f'effect_{x}' for x in selected))))
        (dest/f'{family}_coverage.smt2').write_text(
            context+'\n(assert '+goal+')\n(check-sat)\n(exit)\n')
    compact=json.loads(json.dumps(report))
    for fam in compact['families'].values():
        # Keep all checks and their exact proof keys, but avoid giant formulas
        # in the concise manifest. The scripts retain the complete formulas.
        fam.pop('effect_formula',None)
    (dest/'inferred_contracts_manifest.json').write_text(json.dumps(compact,indent=2)+'\n')
    return compact


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cores',type=int,default=4)
    parser.add_argument('--lines',type=int,default=2)
    parser.add_argument('--cache-dir',type=Path, default=ROOT/'.proof_cache')
    parser.add_argument('--no-cache',action='store_true')
    parser.add_argument('--no-oracle',action='store_true',help='skip comparison with v1.3 handwritten contracts')
    parser.add_argument('--previous-contracts',type=Path,help='verified prior generated manifest for a conservative reuse and compatibility check')
    parser.add_argument('--output-dir',type=Path)
    parser.add_argument('--timeout-ms',type=int,default=0)
    parser.add_argument('--seed',type=int,default=0)
    args=parser.parse_args()
    model=load_combined(args.cores,args.lines)
    previous_manifest=json.loads(args.previous_contracts.read_text()) if args.previous_contracts else None
    result=prove_contracts(model,cache_dir=None if args.no_cache else args.cache_dir,
                           timeout_ms=args.timeout_ms,seed=args.seed,
                           compare_handwritten=not args.no_oracle,
                           previous_manifest=previous_manifest)
    if args.output_dir:
        write_proof_bundle(args.output_dir,model,result)
    summary = {'configuration':result['configuration'],'all_passed':result['all_passed'],
               'families':{key:{'selected_events':v['selected_events'],
                                  'proof_key':v['certificate_key'][:16],
                                  'oracle_equivalent':(v['oracle']['equivalent_under_invariants']
                                                      if v['oracle'] is not None else None),
                                  'reuse':(v['reuse_assessment']['status']
                                           if v['reuse_assessment'] is not None else None)}
                            for key,v in result['families'].items()}}
    print(json.dumps(summary,indent=2))
    if not result['all_passed']:
        raise SystemExit(1)

if __name__=='__main__':main()
