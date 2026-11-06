# v1.9 — Deadlock and temporal-progress checks after directory-invariant minimization

**Branch:** `proof/minimized-invariant-progress-v1.9` (branched from v1.8 `ee10ecb`).

**Bottom line:** The exact v1.8 reduced directory invariant supports all the previously established safety, nonterminal-deadlock, internal transaction ranking, round-robin fairness, frontend progress and speculative-resolution premises. New independent SMT checks establish full and reduced invariant equivalence, complete one-step inductiveness, safety, and frontend/protocol progress enabledness for both four-core models. **This still does not constitute a native machine-checked global temporal theorem over the infinite-state cache-plus-speculation model.** No claim of unconditional or arbitrary-core liveness is made.

## Scope and model identity

The checked model is `MinimizedDirectorySpec` from `tools/directory_invariant_minimize.py`. It removes 10 of 35 directory schema assertions, and **does not modify any transition, initialization clause, memory abstraction, scheduling assumption, or speculative instruction semantics**. The v1.9 tool checks textual identity of the old and new declarations, initialization formula and the complete concrete transition relation for each tested configuration. All statements below concern exactly these transition systems.

Config | Concrete transition/SMT checks | New checks using solver | Hash-validated reused v1.8 proofs
--- | ---: | ---: | ---:
4 cores × 2 lines | 195 | 71 | 124
4 cores × 3 lines | 264 | 98 | 166
**Total** | **459** | **169** | **290**

The 290 fairness-premise queries are reused only when the exact SHA-256 of the original SMT-LIB formula (including declarations, property and check-sat) matches the previously Z3-verified `v17_premises_rechecked_v18.json`. `unknown` or `sat` never means a successful UNSAT proof, and the tool verifies the old manifest itself reports `passed=true`. The final report records reuse vs fresh execution for each query. All new and reused obligations are emitted as stand-alone `.smt2` files. The 169 fresh queries additionally have newly observed `unsat` responses.

Breakdown by family:

Check family | 4×2 | 4×3 | Interpretation
--- | ---: | ---: | ---
Original ↔ reduced invariant equivalence | 4 | 4 | Removed clauses add no states, including next-state form
Safety induction and speculative architectural contract | 4 | 4 | Full-system one-step inductiveness and `bad` exclusion
Directory/rank/round-robin progress | 38 | 57 | Rank decreases on service, service remains enabled, queued requests persist, bypass distance falls
CPU/frontend progress | 24 | 32 | A busy command with no pending request can ask or complete; store/CAS can complete for arbitrary integer operands
No terminal deadlock with outstanding work | 1 | 1 | Some meaningful progress action is enabled, **not eventual execution**
Temporal fairness and speculative-resolution premises | 124 | 166 | Persistency, fair-service enabling, confirmation/squash, confirmed-store issue, read retirement/replay

Symbolic, arbitrary-positive-core-count **arithmetic alone**: 3/3 round-robin and 7/7 directory-rank SMT checks passed; the parameterized *transition-system invariant* is not universally machine-checked.

## Further counterexample and fairness evidence

Three actual (not just abstract) time-indexed transition queries were executed:

- A write with an arbitrary value that was obstructed by the v1.5 immutable array abstraction: **SAT** (valid completion witness on the revised model).
- A repeating starvation cycle under round-robin arbitration: **UNSAT** for that particular cycle.
- The corresponding cycle with deliberately unfair arbitration: **SAT** (negative control).

An **independent finite-state progress abstraction** was checked by enumerating reachable states and recurrent strongly connected components with weak and strong fairness conditions. Fifteen tests for 2, 3, and 4 cores gave the expected results: no *fair* incomplete-request lasso under the assumed arbitration/scheduling; a lasso reappears with unfair arbitration, unfair servicing/start or weakened completion fairness. This finite abstraction has **not** been independently proved a fairness-preserving abstraction of the entire concrete model. Its fair-lasso results therefore do not establish global concrete temporal liveness.

## Fairness and precise guarantees

- **Weak fairness** for a continuously enabled per-line service event or directory-start event; unresolved speculative writes/reads eventually resolve; confirmed-store issue and confirmed-read settlement get a fair opportunity.
- **Strong fairness** for individual architectural ask/completion events, because another core can repeatedly revoke a cache permission before a CPU completion fires.
- **No assumption** that a newly staged/squashed speculative operation must commit. No fairness assumption for issuing a new architectural command.
- Model messages are not permanently lost; servicing is enabled as specified.

**What is mechanically established:** every reachable state of each checked configuration satisfies the reduced invariant; with work outstanding there is an enabled progress event; an active directory transaction has a descending bounded rank for servicing steps, and round-robin prevents infinite bypass under the specified fairness; frontend/speculation persistence and enabling are supported by concrete SMT queries.

**What is supported by a mathematical but not native end-to-end machine-checked temporal proof:** every *issued* architectural request completes along fair executions of the full concrete model; confirmed speculative operations settle under the separate speculative fairness assumptions.

**Still open:** a mechanically accepted proof/certificate of

```
FairExecution(M) => G(IssuedRequest(c,id) -> F CompletedSameRequest(c,id))
```

for the full concrete infinite-state system. In this model one outstanding ordinary CPU instruction per core makes `busy` persistence until completion a convenient surrogate, but the formal property should track the particular request if the architecture is later generalized. Full trace refinement to sequential consistency and all-core-count machine-checked temporal/inductive proofs remain separate open tasks.

## Reproduction

From the repository root, Python 3 with system `libz3.so.4`:

```bash
python tools/verify_temporal_progress_v19.py --cores 4 --lines 2 3 --max-abstract-cores 4
python -m unittest discover -s tests -q
```

Outputs:

- `artifacts/minimized_temporal_progress_v1_9/summary.json` — results, source query hashes and fresh/reused status.
- `artifacts/minimized_temporal_progress_v1_9/fair_lasso.json` — finite abstraction checks.
- `artifacts/minimized_temporal_progress_v1_9/*cores_*lines/*/*.smt2` — exact concrete proof queries, generated on demand.
- `artifacts/minimized_temporal_progress_v1_9/concrete_trace_witnesses/*.smt2` — real transition witness queries.

The final regression suite result is **41/41 passing** (37 inherited plus 4 v1.9 tests).

## Next proof milestone

A useful route to truly end-to-end temporal verification is to (i) express the full concrete model and the exact weak/strong fairness actions in a temporal proof framework, (ii) mechanically prove the *global* leads-to composition lemma from the checked ranking, request/permission persistence and CPU fairness premises, and (iii) establish a sound connection to this exact SMT transition system rather than treating the finite progress abstraction as the concrete system. Do not advertise a global temporal proof until those steps are checked.
