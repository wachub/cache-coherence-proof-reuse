# Fast SAT/SMT workflow for the next cache-model feature (v1.1)

This repo keeps the original MSI protocol and proof history intact. The *new* tools accelerate checking **the same logical obligations**, not by weakening or silently dropping properties.

## Start here

From the repository root on Linux with `libz3.so.4`:

```bash
# Only incremental combined-speculation obligations; same seven queries as v1.0
python tools/fast_verify.py --cores 4 --lines 2

# Reuse prior proof safely: baseline, delta, and independent full induction
python tools/fast_verify.py --cores 4 --lines 2 \
  --verify-baseline --full-regression --check-mutants

# A second identical run loads certified cached solver results
python tools/fast_verify.py --cores 4 --lines 2 \
  --verify-baseline --full-regression --check-mutants

# Recheck a larger configuration and export every actual SMT-LIB formula
python tools/fast_verify.py --cores 4 --lines 3 --no-cache \
  --emit-smt .fast_verify_outputs/queries_4_3

# Compare real solving with context-sharing and cache reuse
python tools/benchmark_solver.py --cores 4 --lines 2 --repeats 3

# Investigate one existing proof for irrelevant invariant assumptions
python tools/invariant_core_hints.py --cores 4 --lines 2

# Toolkit regression suite
python -m unittest discover -s tests -v
```

`--no-cache` always reruns the solver. `--mode isolated` disables the shared context for performance diagnosis. `--localize` automatically checks each concrete added transition **only if** a delta proof fails. `--check-mutants` must find SAT for the intentionally broken read-validation and read-ordering mutants.

## What actually improves speed

| Technique | Implemented? | Safety / meaning | Where |
| --- | --- | --- | --- |
| Shared declarations and `push` / `pop` solver contexts | Yes | Exactly the same seven queries; each has fresh temporary assertions | `tools/fast_verify.py` |
| Exact-content proof cache | Yes | Hash contains full declaration/formula text, Z3 version, timeout and seed; cache hits labeled, never presented as a fresh run | `tools/fast_verify.py` |
| Reuse the MSI predecessor induction | Yes | `--verify-baseline` either reruns or retrieves the **exact** baseline obligations; a changed formula becomes a cache miss | `tools/fast_verify.py` |
| Separate delta and full-system induction | Yes | Delta is fast path; `--full-regression` is independent confirmation | `tools/fast_verify.py` |
| Transition-by-transition counterexample localization | Yes | On a failing aggregated obligation, solve every constituent new transition, report all SAT schemas | `failure_localization()` |
| Deliberately incorrect mutants | Yes | SAT sanity check detects vacuous or accidentally weakened safety queries | `mutant_sensitivity()` |
| Named invariant clauses / UNSAT-core mining | Yes, **diagnostic** | Core is rechecked for the *exact* query; NOT automatically a reusable theorem for a changed model | `tools/invariant_core_hints.py` |
| Generalized symmetry reduction over cores | Not yet | Only sound with an explicit permutation-invariance argument | Research candidate |
| Parameterized induction for arbitrary queue length | Not yet | Current finite queue bound remains exactly two stores | Research candidate |
| Solver portfolio, k-induction, interpolation/PDR | Not yet | Could help harder changes, but requires separate implementation and verification | Research candidate |

## New-feature recipe, ordered by time-to-counterexample

1. **Keep the original reference untouched.** Add feature state `q`, state its initial value and new invariant `J`, and add only the changed/added transitions `Δ`. Specify what is architecturally observable.
2. **Generate pure goals** before solver calls. `CombinedSpec.proof_goals()` is the example. Keeping declarations and goals separate allows batching and exact hashing. Ensure `Init_new ∧ ¬J`, `I_old ∧ J ∧ Δ ∧ ¬J'`, `I_old ∧ J ∧ Δ ∧ ¬I_old'`, and `I_old ∧ J ∧ Δ ∧ ¬Interface` are included.
3. **Check the exact old-step preservation assumptions.** If an old transition was changed, or changes newly added state, you **cannot** simply inherit the old proof. Recheck its effect on `I_old` and `J`. If old actions merely acquire additional guards and frame `q`, the old safety argument may transfer but progress may not.
4. **Solve the delta with the fast runner.** A SAT result is a counterexample candidate; use `--localize` to find specific offending transition schemas. Then test a deliberately broken mutant and demand SAT.
5. **Run baseline + full induction as a release gate.** Verify 4-core/2-line and 4-core/3-line configurations, record exact SMT output, and only then commit/tag the feature. The full trace-level SC claim remains a separate refinement task.
6. **Avoid hidden assumptions.** Speculative reads from earlier queued stores require forwarding from the latest matching earlier store; stale loads need validation/replay; writes require in-order confirmed retirement. Any feature allowing a write to affect coherent memory before confirmation changes the proof boundary drastically.

## Problem-specific solver guidance

**Proof decomposition.** Ask for validity of `I_old ∧ J ∧ Δ_j ⇒ Post` separately when triaging, rather than debugging the entire large disjunction of new transitions. The aggregate proof must ultimately cover *all* `Δ_j`—a successful core-0 subcase is not a proof for other cores without symmetry justification.

**Frames.** Each transition should explicitly frame all unrelated MSI and speculation variables. Hidden unframed next-state variables can produce a fabricated SAT bug or, worse, an incomplete specification. `System.step()` already constructs equality frames from the patch map.

**Read values.** A version token is not the payload. Use actual `payload_l(version)` constraints, including repeated payload values and ABA. Don't replace CAS comparisons with version comparisons.

**Conjunction splitting.** Inductive strengthening is usually much cheaper than exploring long execution traces. Mine unsat cores only as *candidates* for simplification. The current core-hints tool rechecks the reduced UNSAT formula but makes **no claim** that selected clauses form a new inductive invariant for future modifications.

**Negative controls.** For stale-load, queue-overtake, unconfirmed-store, or replay bugs, construct intentionally wrong transition variants that produce SAT. A proof suite that stays UNSAT even after breaking a key safety guard may be checking too weak a property.

**Performance knobs.** Fewer duplicated declarations, cached unchanged goals, goal-specific invariants, bounded store capacity, and meaningful abstraction boundaries tend to help more reliably than changing random seeds. Keep `unknown` or solver error as failure; do not call it a proof. Always report exact `N`, number of lines, capacity, and solver version.

**Future improvements worth testing, not assumed sound by default:** line-local cone-of-influence reduction, core-index symmetry, incremental PDR/IC3 frames, Craig interpolation for missing invariants, bit-vectors for bounded payloads, array abstraction with collision cases, portfolio Z3/cvc5, and proof-producing UNSAT certificates. Each requires separate equivalence or soundness justification.

## Measured baseline (not a universal performance guarantee)

On the current sandbox, Z3 `4.13.3.0`, four cores and two cache lines, median over three complete seven-goal runs:

- Independent fresh contexts: **0.6050 s**
- One shared context (with `push`/`pop`): **0.3707 s** (**1.63× faster**)
- Unchanged, content-addressed cache hits: **0.0067 s** (avoids solver work)

These times measure just solver-runner work after Python has generated the formulas; formula construction itself is not included. Larger new features may behave differently. Original `.smt2` files generated by the refactored v1.1 model were byte-for-byte identical to v1.0's seven delta files for 4 cores and 2 lines.

## Proof-status boundaries

`UNSAT` for an inductive query proves unbounded execution length **for the stated configuration**, not arbitrary core count or arbitrary queue depth. A delta check assumes the old MSI theorem and old-transition framing; check that dependency. The separate machine-checked global sequential-consistency trace-refinement theorem and liveness have not been completed. SAT mutants demonstrate sensitivity, not completeness of the specification.
