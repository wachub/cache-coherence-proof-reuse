# v1.4 — Template-guided synthesis and conservative reuse of speculative-ordering contracts

**Objective.** Automatically infer **which abstract architectural effects** an existing speculative transition family may produce; check those effects using Z3; preserve old contracts when a localized change is made. **No cache protocol/model transition/invariant was changed.** This module is a methodological proof harness over v1.3.

## Exactly what is automatic

The solver does **not** invent cache architecture semantics, invent wholly new Boolean expressions, or prove complete sequential consistency. The human supplies a **finite, reusable architectural effect vocabulary** applicable to any core/line:

| Effect type | Generated semantics in SMT-LIB | What it means |
|---|---|---|
| `stutter` | Equality on all inherited MSI/architectural state variables | Only speculative-private state may change |
| `issue_store` | Old MSI frontend begins a store using the oldest queued address/value | Publication of an already confirmed store request |
| `retire_read` | A current-value read result is published into `observed` | Validated architectural read; earlier writes have finished |
| `replay_read` | Old MSI frontend begins an ordinary read | Failed speculation falls back to the preverified reader |

This **effect grammar** is written once in `tools/infer_ordering_contracts.py::effect_vocabulary`. It is not copied from the v1.3 family-by-family `_contracts`; those are used **only as an independent regression oracle**, optionally disabled with `--no-oracle`.

For every transition family, the learner **automatically selects an irredundant disjunction** of these event types. The same grammar is reused for all seven families. Selection is conditional on the inherited `I_MSI ∧ J_spec` invariant and the actual transition relation, and is made by SMT implication queries. Future effects absent from this grammar must first be explicitly specified and tested.

## Algorithm (SMT-guided, Houdini-style elimination)

Let `A(s) = I_MSI(s) ∧ J_spec(s)`, `Δ_f(s,s')` be the **unmodified** disjunction of the source model's transitions in family `f`, and `E = {E_stutter, E_issue, E_read, E_replay}`.

1. **Reject vacuity:** demand `SAT(A ∧ Δ_f)`. This proves there is a state satisfying the inductive invariant in which some family transition is enabled (not necessarily reachable from initial states).
2. **Check grammar completeness:** demand `UNSAT(A ∧ Δ_f ∧ ¬(∨E))`. Otherwise stop: a feature produces a kind of effect we have not specified.
3. **Infer the allowed effects:** start with the whole vocabulary. For each event kind `e`, ask `SAT(A ∧ Δ_f ∧ ¬(∨(selected \ {e})))`. Remove `e` **only if this query is UNSAT**. Repeat once in a documented priority order. The final disjunction is irredundant in that order; no claim of globally smallest formula is made.
4. **Issue a proof certificate:** recheck `UNSAT(A ∧ Δ_f ∧ ¬C_f)`, saving an exact content hash of the family-local declarations, common invariants, effect grammar and this query.
5. **Compare with existing specification:** separately verify both `A ∧ C_f ⇒ C_f^v1.3` and `A ∧ C_f^v1.3 ⇒ C_f` (when enabled). The handwritten contract **never trains the learner**. This is a guard against accidental weakening of the intended semantics.

The procedure has finitely many solver calls for a fixed vocabulary. Z3 `unsat` provides one-step implications for the **specified** model; a satisfiable obligation is a counterexample candidate. The existing full-system invariant induction supplies the necessary induction context, not this learner alone.

## Composition/reuse theorem and its limits

Assume the already checked initial invariant and inherited-transition preservation:

`Init ⇒ A`, and `A ∧ T_inherited ⇒ A'`.

Assume separately `A ∧ Δ_f ⇒ A'` for every speculative family. The learned contract certificates give `A ∧ Δ_f ⇒ C_f`. Together, all executions of the transition system preserve `A` and each speculative transition obeys its selected architectural-effect contract.

When only a family `g` changes, an old certificate for `f ≠ g` can be **reused as an exact formula proof** when the shared declarations/invariants/effect vocabulary and `Δ_f` are unchanged (including solver identity, seed and timeout in the cache key). The changed family must be re-proved. No core symmetry or implicit equivalent-state assumption is involved.

To reuse a **previous interface guarantee** after a changed family, the verifier also proves:

`UNSAT(A ∧ C_f^new ∧ ¬C_f^old)`.

If that implication fails, the extension has weakened a previously certified architectural contract; refuse release even when the broadened vocabulary would technically permit it. A changed common invariant or event grammar invalidates the shared abstraction fingerprint and **requires a new cross-abstraction proof**; do not reuse.

**Important caveat:** unchanged one-step contracts and inductive invariants do not themselves constitute an end-to-end machine-checked theorem that all observable traces are sequentially consistent. The project still needs a separately checked forward-simulation/trace-refinement proof. These are fixed 4-core, 2/3-line models and finite private speculative queues, not arbitrary parameters.

## Generated contracts for the original combined system

| Source family (v1.3) | Automatically selected effect |
|---|---|
| `store_stage` | `stutter` |
| `resolve_speculation` | `stutter` |
| `store_issue` | `issue_store` |
| `load_forward` | `stutter` |
| `load_cache_capture` | `stutter` |
| `load_retire` | `retire_read` |
| `load_replay` | `replay_read` |

All seven one-step coverage certificates are UNSAT, with SAT feasibility checks, for **4 cores / 2 lines and 4 cores / 3 lines**, and the inferred contracts match the handwritten v1.3 ones under the invariant assumptions. Source-level implementation and manually reviewed properties remain in the model's trusted base.

## Detecting incorrect changes

The regression tests deliberately exercise three failure classes *in temporary test-only subclasses*—the production cache model is unchanged:

- **Unvalidated read retirement:** grammar completeness fails because the retired value need not be current.
- **Premature read retirement:** grammar completeness fails because the older memory operations are not necessarily complete.
- **Stuttering store issue (lost write):** the learner would include `stutter` in the store-issue family; the previous-contract implication rejects this weakening. This is a particularly important example: inference alone is not a behavioral specification.

A fourth test adds a semantically redundant retirement transition to a test-only subclass. It demonstrates that the store-issue and unrelated families retain *identical* proof keys, while the changed load-retirement family must be rechecked.

## Portable proof artifacts and formats

The verifier emits standalone **SMT-LIB 2** files (`*_coverage.smt2`) for independently rerunning Z3, and a machine-readable JSON contract manifest with the shared-abstraction hash, family-local proof keys, selected event kinds, solver version, source hashes and optional compatibility evidence.

There is no universally standardized *binary compressed SAT layer* that also communicates assume-guarantee semantics. SMT-LIB `define-fun` allows named shared DAG nodes; separate modules are encoded as distinct contracts/queries. The JSON manifest is a project-defined interface, **not a portable formal proof format**. Future independent proof certificates might use Alethe for SMT proofs or LRAT/FRAT for propositional proofs after a suitable translation; this version relies on rerunnable SMT queries and trusting the solver.

## Reproduce / extend

```bash
# From repository root; requires Python and libz3.so.4
python tools/infer_ordering_contracts.py --cores 4 --lines 2 --no-cache \
  --output-dir /tmp/auto-contracts-4c2l
python tools/infer_ordering_contracts.py --cores 4 --lines 3 --no-cache \
  --output-dir /tmp/auto-contracts-4c3l

# Requires a manifest produced by the current tool version
python tools/infer_ordering_contracts.py --cores 4 --lines 2 \
  --previous-contracts /tmp/auto-contracts-4c2l/inferred_contracts_manifest.json

# IMPORTANT: Inference is a DELTA-level check; do the full release regression:
python tools/compositional_verify.py --cores 4 --lines 2 --no-cache \
  --baseline --full-regression --check-mutants
python -m unittest discover -s tests -v
```

**How to evolve the tool:** introduce an **abstract new effect kind**, define its pre/post conditions independently of a feature's implementation, add the effect to the grammar, and **recheck the shared abstraction** and the contracts' compatibility. To reduce human specification effort further, future research could synthesize predicates for guards and data-dependency conditions, use CHCs/PDR to discover missing inductive summaries, and infer minimal assume-guarantee assumptions; none is implemented here.
