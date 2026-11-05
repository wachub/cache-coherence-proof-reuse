#!/usr/bin/env python3
"""Fast incremental SMT obligation runner for the abstract speculative MSI models.

Key correctness principle: these are only *solver scheduling* optimizations.
Every obligation's exact formula is checked with the same Z3 semantics as the
original verifier. Cache hits are explicitly labeled; unknown is never passed.
The predecessor MSI proof remains a separate prerequisite.

Standard library + libz3.so.4, no pip dependencies.
"""
from __future__ import annotations

import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time
from typing import Mapping

ROOT = Path(__file__).resolve().parents[1]
EXPERIMENT = ROOT / 'experiments' / '09_combined_speculative_reads_writes'
STATUSES = ('unsat', 'sat', 'unknown')


def _z3_library():
    lib = ctypes.CDLL('libz3.so.4')
    lib.Z3_get_full_version.restype = ctypes.c_char_p
    lib.Z3_mk_config.restype = ctypes.c_void_p
    lib.Z3_mk_context.argtypes = [ctypes.c_void_p]
    lib.Z3_mk_context.restype = ctypes.c_void_p
    lib.Z3_eval_smtlib2_string.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
    lib.Z3_eval_smtlib2_string.restype = ctypes.c_char_p
    lib.Z3_del_context.argtypes = [ctypes.c_void_p]
    lib.Z3_del_config.argtypes = [ctypes.c_void_p]
    return lib


def z3_version():
    return _z3_library().Z3_get_full_version().decode()


def eval_z3(script: str) -> str:
    """All checks within one Z3 context; context is always released."""
    lib = _z3_library()
    cfg = lib.Z3_mk_config()
    ctx = lib.Z3_mk_context(cfg)
    try:
        output = lib.Z3_eval_smtlib2_string(ctx, script.encode('utf-8'))
        if output is None:
            raise RuntimeError('Z3 returned no response')
        return output.decode('utf-8', errors='replace')
    finally:
        lib.Z3_del_context(ctx)
        lib.Z3_del_config(cfg)


def _read_statuses(output: str, expected: int) -> list[str]:
    # Don't turn an SMT parser error into a spurious success.
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if len(lines) != expected or any(line not in STATUSES for line in lines):
        raise RuntimeError(f'Unexpected Z3 output for {expected} goals: {output[:2000]!r}')
    return lines


def _options(timeout_ms: int, seed: int) -> str:
    # Z3's :timeout is an internal solver timeout, NOT a wall-clock process limit.
    if timeout_ms < 0 or seed < 0:
        raise ValueError('timeout and seed must be nonnegative')
    return f'(set-option :timeout {timeout_ms})\n(set-option :smt.random_seed {seed})\n'


def proof_cache_key(declarations: str, goal: str, timeout_ms: int, seed: int, version: str) -> str:
    # Full declarations + formula, Z3 version, seed and timeout: safe across renames.
    data = json.dumps({'declarations': declarations, 'goal': goal,
        'timeout_ms': timeout_ms, 'seed': seed, 'z3_version': version},
        sort_keys=True, separators=(',', ':'))
    return hashlib.sha256(data.encode()).hexdigest()


def solve_goals(declarations: str, goals: Mapping[str,str], *,
                cache_dir: Path|None, timeout_ms: int=0, seed: int=0,
                mode: str='batch') -> dict:
    """Returns proof statuses and provenance for each named goal.

    Runs all cache misses with push/assert/check-sat/pop in one shared context
    (batch), or in separate contexts for benchmarking (isolated).
    Cache records are accepted only on an exact content/version/options match.
    """
    if mode not in ('batch', 'isolated'):
        raise ValueError('mode must be batch or isolated')
    start = time.monotonic()
    version = z3_version()
    result: dict[str,dict] = {}
    pending = []
    for name, goal in goals.items():
        key = proof_cache_key(declarations, goal, timeout_ms, seed, version)
        if cache_dir is not None:
            file = cache_dir / f'{key}.json'
            if file.is_file():
                try:
                    saved = json.loads(file.read_text())
                    if saved['key'] == key and saved['status'] in STATUSES:
                        result[name] = {'status': saved['status'], 'source': 'cache',
                                        'hash': key[:16]}
                        continue
                except (OSError, ValueError, KeyError, TypeError):
                    pass  # corrupt/incomplete cache is a miss
        pending.append((name, goal, key))

    if pending:
        prelude = _options(timeout_ms, seed) + declarations + '\n'
        if mode == 'batch':
            script = prelude + ''.join(
                '(push 1)\n(assert '+goal+')\n(check-sat)\n(pop 1)\n'
                for _,goal,_ in pending)
            statuses = _read_statuses(eval_z3(script), len(pending))
        else:
            statuses = [
                _read_statuses(eval_z3(prelude+'(assert '+goal+')\n(check-sat)\n'),1)[0]
                for _,goal,_ in pending]
        for (name,_,key),status in zip(pending,statuses):
            result[name] = {'status':status, 'source':'solver','hash':key[:16]}
            if cache_dir is not None and status in ('sat','unsat'):
                cache_dir.mkdir(parents=True,exist_ok=True)
                path = cache_dir / f'{key}.json'
                # Atomic replace: partial interrupted writes are never used.
                tmp = cache_dir / f'{key}.{os.getpid()}.tmp'
                try:
                    tmp.write_text(json.dumps({'key':key,'status':status,'z3_version':version}))
                    os.replace(tmp,path)
                finally:
                    tmp.unlink(missing_ok=True)
    # Preserve named obligation order even when some are cached.
    ordered={name:result[name] for name in goals}
    return {'passed':all(v['status']=='unsat' for v in ordered.values()),
            'solver_version':version,'mode':mode,'seconds':round(time.monotonic()-start,4),
            'cache_hits':sum(v['source']=='cache' for v in ordered.values()),
            'solved':sum(v['source']=='solver' for v in ordered.values()),
            'goals':ordered}


def load_combined(cores: int, lines: int):
    if cores < 1 or lines < 1:
        raise ValueError('cores and lines must be positive')
    sys.path.insert(0,str(EXPERIMENT))
    from combined_speculative_model import CombinedSpec
    return CombinedSpec(cores,lines)


def failure_localization(model, failed: list[str], *, timeout_ms: int,
                         seed: int, max_checks: int=0) -> dict:
    """Exact transition-by-transition rechecks of failing aggregated goals.

    No core symmetry is assumed. An UNSAT subcase is a verified exclusion;
    no subcase set substitutes for the original complete proof obligation.
    """
    from sc_msi_4core_verifier import System, a, neg
    oldinv=System.inv(model)
    newinv=model.new_inv()
    conditions={
       'new_transition_preserves_new_invariant':neg(model.new_inv(True)),
       'new_transition_preserves_MSI_invariant':neg(System.inv(model,True)),
       'new_transition_obeys_interface':neg(model.interface_contract()),
    }
    output={}
    for name in failed:
        if name not in conditions:
            continue
        choices=model.delta_steps()
        if max_checks: choices=choices[:max_checks]
        queries={label:a(oldinv,newinv,trans,conditions[name]) for label,trans in choices}
        checked=solve_goals(model.declarations(),queries,cache_dir=None,
                            timeout_ms=timeout_ms,seed=seed,mode='batch')
        output[name]={
          'sat_schemas':[label for label,v in checked['goals'].items() if v['status']=='sat'],
          'unknown_schemas':[label for label,v in checked['goals'].items() if v['status']=='unknown'],
          'checked_schemas':len(queries),'complete':len(queries)==len(model.delta_steps()),
          'seconds':checked['seconds']}
    return output


def mutant_sensitivity(model, *, timeout_ms: int=0, seed: int=0):
    """SAT sanity checks: intentionally broken retirement must be detectable."""
    from sc_msi_4core_verifier import System, a, o, neg
    clauses={}
    for mutant in ('unvalidated_read','premature_read'):
        transitions=o(*(s for label,s in model.delta_steps(mutant=mutant)
                        if ':spec_retire_fast_' in label))
        clauses[mutant]=a(System.inv(model),model.new_inv(),transitions,
                          neg(model.interface_contract()))
    report=solve_goals(model.declarations(),clauses,cache_dir=None,
                       timeout_ms=timeout_ms,seed=seed)
    report['detected']=all(item['status']=='sat' for item in report['goals'].values())
    return report


def baseline_goals(cores: int, lines: int):
    """The exact three old-system induction/safety obligations."""
    sys.path.insert(0,str(EXPERIMENT))
    from sc_msi_4core_verifier import System, a, neg
    base=System(cores,lines)
    return base.declarations(), {
        'initial':a(base.init(),neg(base.inv())),
        'induction':a(base.inv(),base.T(),neg(base.inv(True))),
        'safety':a(base.inv(),base.v('bad')),
    }


def full_system_goals(model):
    """Independent complete induction, including inherited network steps."""
    from sc_msi_4core_verifier import System, a, neg
    inv=a(System.inv(model),model.new_inv())
    inv_next=a(System.inv(model,True),model.new_inv(True))
    return {
        'initial':a(model.init(),neg(inv)),
        'induction':a(inv,model.T(),neg(inv_next)),
        'safety':a(inv,model.v('bad')),
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cores',type=int,default=4)
    parser.add_argument('--lines',type=int,default=2)
    parser.add_argument('--cache-dir',type=Path,default=ROOT/'.proof_cache')
    parser.add_argument('--no-cache',action='store_true')
    parser.add_argument('--mode',choices=['batch','isolated'],default='batch')
    parser.add_argument('--timeout-ms',type=int,default=0)
    parser.add_argument('--seed',type=int,default=0)
    parser.add_argument('--localize',action='store_true',help='On failure, test each delta transition')
    parser.add_argument('--check-mutants',action='store_true')
    parser.add_argument('--verify-baseline',action='store_true',help='Also check/reuse all three predecessor MSI proof queries')
    parser.add_argument('--full-regression',action='store_true',help='Also check/reuse complete combined-system induction')
    parser.add_argument('--output-json',type=Path)
    parser.add_argument('--emit-smt',type=Path,help='Write complete exact goal formulas for audit')
    args=parser.parse_args()
    model=load_combined(args.cores,args.lines)
    goals=model.proof_goals()
    if args.emit_smt:
        args.emit_smt.mkdir(parents=True,exist_ok=True)
        for name,goal in goals.items():
            (args.emit_smt/(name+'.smt2')).write_text(model.declarations()+'\n(assert '+goal+')\n(check-sat)\n')
    result=solve_goals(model.declarations(),goals,
            cache_dir=None if args.no_cache else args.cache_dir,
            timeout_ms=args.timeout_ms,seed=args.seed,mode=args.mode)
    result['configuration']={'cores':args.cores,'lines':args.lines,
          'store_slots_per_core':2,'speculative_loads_per_core':1}
    result['scope']='Inductive delta obligations; predecessor MSI proof assumed unless --verify-baseline; not a full SC trace-refinement theorem'
    cache=None if args.no_cache else args.cache_dir
    if args.verify_baseline:
        base_decl,base_goals=baseline_goals(args.cores,args.lines)
        result['baseline']=solve_goals(base_decl,base_goals,cache_dir=cache,
                           timeout_ms=args.timeout_ms,seed=args.seed,mode=args.mode)
    if args.full_regression:
        result['full_regression']=solve_goals(model.declarations(),full_system_goals(model),
                 cache_dir=cache,timeout_ms=args.timeout_ms,seed=args.seed,mode=args.mode)
    result['all_requested_proofs_passed']=(result['passed'] and
          (not args.verify_baseline or result['baseline']['passed']) and
          (not args.full_regression or result['full_regression']['passed']))
    if args.localize and not result['passed']:
        result['localization']=failure_localization(model,
              [name for name,v in result['goals'].items() if v['status']!='unsat'],
              timeout_ms=args.timeout_ms,seed=args.seed)
    if args.check_mutants:
        result['mutants']=mutant_sensitivity(model,timeout_ms=args.timeout_ms,seed=args.seed)
    if args.output_json:
        args.output_json.parent.mkdir(parents=True,exist_ok=True)
        args.output_json.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    if not result['all_requested_proofs_passed'] or (args.check_mutants and not result['mutants']['detected']):
        raise SystemExit(1)

if __name__=='__main__': main()
