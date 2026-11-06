# v1.8: SMT-based minimization of directory-consistency invariant clauses

**Branch:** `experiment/directory-invariant-minimization-v1.8`, derived from `proof/temporal-fairness-v1.7`.  No protocol transitions, speculation transitions, fairness assumptions, or architectural contracts are changed.

## Research question

Are the directory-consistency constraints logically implied by the other already-proved cache/MSI and frontend invariants? Which *individual schema families* can be omitted without weakening the inductive invariant?

**Answer:** some, but not all. In both the 4-core × 2-line and 4-core × 3-line v1.7 systems, 10 of 35 explicitly selected directory/control-state schema families are redundant. The remaining 25 are individually independent of the other retained conjuncts. This is a deletion-minimal **logically equivalent** assertion set relative to the chosen directory schema families and deletion order; it is not a globally smallest invariant, nor does it prove all retained clauses are necessary for the architectural safety theorem.

## Method

The original `Protocol.invariant_terms()` has 8 global and 33 per-core terms. v1.7 instantiates the per-line protocol invariant once for every cache line, with additional CPU, speculation, reference-memory, payload, and round-robin invariants. We preserve all those other constraints.

The selected directory group comprises 5 global schema families (`G03`–`G07`) and 30 per-core families (`C01`, `C03`–`C31`), totaling **35 schema families**. Explicit mode exclusivity, cache freshness, memory value, domain restrictions, and reference-memory constraints are deliberately *not* considered for deletion. This grouping is a judgment call, documented in code.

For each candidate schema `d`, remove **all** its instances from every core and line. Ask Z3:

```
SAT ? I_remaining(s) AND NOT d_all_instances(s)
```

- `unsat` → the schema is redundant, so remove it permanently.
- `sat` → the schema is not implied; retain it. The model is a logical counterexample **state**, not a reachable execution.
- `unknown` → retain conservatively; never treat it as proven.

Run the candidates sequentially, without restoring already eliminated clauses. Finally recheck **all removed clauses at once**:

```
I_reduced(s) AND NOT all_removed_clauses(s)   -> UNSAT.
```

Since the original invariant trivially implies the reduced invariant, this establishes **equivalence** between them over all symbolic states (for the checked fixed configurations). Z3 also checks initial establishment, full one-step induction over the *actual* combined cache/speculation transition system, and the invariant's `bad`-state safety property.

The equivalence proof automatically preserves every property previously proved under the full invariant, but we additionally independently re-run all v1.7 concrete temporal/progress SMT premises with the reduced invariant.

## Removed (proven redundant) schema families

| Code | Removed rule | Why an assertion is unnecessary |
|---|---|---|
| C03 | A core cannot have both queued read and queued write | Follows from remaining request/transaction clauses |
| C22 | `inv` and `recall` cannot coexist | Implied by their individual message phase/cache-state constraints |
| C23 | `inv` and `ack` cannot coexist | Implied by message/state constraints |
| C24 | `inv` and `wb` cannot coexist | Implied by message/state constraints |
| C25 | `recall` and `ack` cannot coexist | Implied by message/state constraints |
| C26 | `recall` and `wb` cannot coexist | Implied by message/state constraints |
| C27 | `ack` and `wb` cannot coexist | Implied by message/state constraints |
| C31 | An in-flight invalidation/recall/ack/writeback requires a `wait` flag | Already required by the four message-specific clauses |
| G05 | During phase 0, an owner has the Modified copy or an outstanding writeback | Follows from remaining ownership/data-preservation assertions |
| G07 | Grant phase implies an active transaction with no waiters | Follows from other transaction/grant/wait invariants |

The statements about logical entailment above were independently checked by the solver. The English explanations highlight their most direct relationships; they are **not** a separately certified minimal assumption trace.

## Retained (not logically redundant relative to other retained clauses)

`C01, C04–C21, C28–C30, G03, G04, G06` (25 schema families).

Examples include:

- `G06`: when the directory is idle, no grant, acknowledgment, invalidation, recall, or wait may be pending.
- `C15/C16`: outstanding read/write grants must identify the correct requester and version.
- `C06`: a pending request must be queued or belong to the active transaction.
- `C18`: the second transaction phase has a grant or grant acknowledgement in flight.

When we remove the **entire** 35-schema directory group, Z3 finds SAT states that still satisfy the non-directory invariants but violate directory consistency. Thus the whole group is not implied by cache exclusivity/freshness and frontend conditions alone.

## Exact checked results

| Obligation | 4 cores × 2 lines | 4 cores × 3 lines |
|---|---|---|
| Candidate schemas | 35 | 35 |
| Eliminated schemas | 10 | 10 |
| Per-line protocol clauses | 140 → 106 | 140 → 106 |
| Total instantiated protocol clauses | 280 → 212 | 420 → 318 |
| Logical `I_reduced => I_full` | UNSAT violation | UNSAT violation |
| `Init => I_reduced` | UNSAT violation | UNSAT violation |
| `I_reduced ∧ T => I_reduced'` | UNSAT violation | UNSAT violation |
| `I_reduced => ¬bad` | UNSAT violation | UNSAT violation |
| v1.7 temporal/progress SMT premises | 124/124 UNSAT | 166/166 UNSAT |
| Non-directory invariant implies whole directory group? | No: SAT counterexample | No: SAT counterexample |

All SMT queries are fixed-size but **unbounded execution-step induction queries**, not finite-depth bounded model-checking traces.

The protocol clauses removed total 68 individual instances in the 4×2 model and 102 in the 4×3 model. The rest of the invariant (including CPU/speculative state) is preserved exactly.

## What is and is not established

**Established:** 10 schema families are redundant, all removed families are simultaneously implied by the reduced invariant, and replacing the v1.7 invariant with this reduced form preserves every checked concrete induction, safety, and transition-level progress premise.

**Not established:** logical independence is not the same as a clause being necessary for a *weaker* safety invariant; removing independently necessary clauses might still permit some different inductive invariant. No native end-to-end temporal fairness theorem or arbitrary-core parameterized theorem is supplied by this experiment. No additional runtime speedup claim is justified by these tiny queries.

## Reproduction

```bash
python tools/directory_invariant_minimize.py --cores 4 --lines 2 3
python tools/verify_minimized_directory_v18.py --cores 4 --lines 2 3
python -m unittest tests.test_directory_invariant_minimize -q
python -m unittest discover -s tests -q
```

Outputs: `artifacts/directory_minimization_v1_8/summary.json`, per-config `schema_checks/*.smt2`, `reduced_implies_all_removed.smt2`, `initial.smt2`, `inductive_step.smt2`, `safety.smt2`, `remove_entire_directory_block.smt2`, and `v17_premises_rechecked_v18.json`. SAT/UNSAT and SHA-256 digests are recorded.

Use `MinimizedDirectorySpec` from `tools/directory_invariant_minimize.py` for a version of the model exposing the reduced invariant, with unchanged transitions. **Do not assume equivalence is proved for core/line configurations other than those checked here.**
