# v1.6 — Fair arbitration, mutable ghost data, and conditional progress

**Status:** Verified per-configuration SMT obligations for the revised model; mathematically derived *conditional* fair-path progress. Not an all-N machine-checked temporal proof.

## Motivation and relationship to v1.5

The **v1.5 source remains unchanged** and its counterexamples remain valid for that model:

1. An indefinitely queued read can be bypassed by repeated CAS transactions from other cores. Weak fairness of servicing actions does not stop this.
2. An immutable symbolic function `payload_l(version)` cannot represent an arbitrary new store operand when `payload_l(latest+1)` has an incompatible preassigned value. This is an abstraction flaw, not an MSI hardware deadlock.
3. The previous verification enumerated four cores, not arbitrary `N`.

The new transition system lives in `experiments/10_fair_progress/fair_progress_model.py` and extends `CombinedSpec`. **Do not use v1.4/v1.5 proof hashes or old verified contracts as if they verified this changed model.** The new invariant and its induction are checked independently here. We also recheck the speculative architectural-effect projection contract under the revised ghost-array semantics.

## Repairs in the new transition system

### Fair directory arbitration

Each cache line `l` has a pointer `rr_turn_l ∈ {0,...,N-1}`. When idle and at least one queued request exists, its only possible directory start transitions choose the **first queued core in circular order** beginning at `rr_turn_l`. After granting that core `d` a transaction start, `rr_turn_l := (d+1) mod N`. Invalidation/recall, grant delivery, writeback, cache commands, and speculation leave the pointer unchanged. This is not a global scheduler: the OS/transition scheduler must still eventually choose an enabled directory-start event.

Let `Q(c)` mean that core `c` has a queued `rqR` or `rqW` for the line, and define

```
dist_N(c,t) = if c >= t then c-t else c-t+N .
```

When `Q(c)` holds, a start for another core `d != c` can only select a core with `dist_N(d,t) < dist_N(c,t)`. The new pointer `t' = (d+1) mod N` satisfies

```
0 <= dist_N(c,t') < dist_N(c,t) < N .
```

These inequalities are proved **for a symbolic, unbounded positive integer N** by SMT, with no fixed bound on N. The concrete-model obligations also verify that `Q(c)` persists unless `c` itself starts, that the pointer changes only on a start, and that some start is enabled whenever a request is queued and the line is idle. Thus each queued request can be bypassed at most `N-1` directory starts before its own start.

**Scheduler assumption:** weak fairness of the *event* `SomeDirectoryStart(line)` whenever it remains enabled, not weak fairness of every particular `start_c` alternative. An active transaction must also finish (proved below under servicing fairness). Without scheduler fairness, the directory could stay idle forever despite enabled transitions.

### Data representation refinement

The specification-only arrays `payload_l` become transition-system state. A completed store changes

```
latest' = latest+1
payload_l' = store(payload_l, latest+1, requested_value)
```

A successful CAS makes the same change; a failed CAS leaves the array unchanged. All other steps frame each array. The old guard `payload_l[latest+1] == requested_value` is deleted. Therefore a store or successful CAS can complete for **every integer operand**, including repeated values or ABA, without requiring a favorable immutable array interpretation.

This is ghost data, not an implementation of DRAM or an RTL synthesis artifact. As the array can change, the speculative capture invariant must be strengthened with `captured_version <= latest` for active cache-sourced reads, ensuring a new version write never modifies a captured older version. The strengthened full-system invariant is proved inductive for every concretely tested configuration.

## Machine-checked proof obligations

Execute:

```bash
python tools/progress_v16_verify.py --cores 4 --lines 2 3 --output-dir artifacts/progress_v1_6_run
python -m unittest discover -s tests -p 'test_progress_v16.py' -v
python -m unittest discover -s tests -p 'test_liveness_verify.py' -v
```

Every property below is a separate emitted SMT-LIB2 query, with SHA256 hashes and solver responses in `summary.json`. **UNSAT** of a violation formula is required for success; `unknown` is a failure.

- New model: `Init => I`, `I & T => I'`, and impossibility of `bad` under `I`.
- Each active line has an enabled protocol servicing action.
- Service actions strictly lower the transaction rank; nonservice actions cannot increase it; unrelated lines and CPU/speculative frontend steps frame it.
- Every enabled servicing guard persists if no servicing event occurs, so weak fairness of an individual servicing action is sufficient to force a decrease.
- If idle with a queued request, an appropriately RR-selected start event is enabled.
- Queued requests persist until selected. Every other start lowers their RR-distance. Pointer changes only upon directory start.
- For an architectural busy CPU with no pending line protocol work, either an ask or a completion is enabled **without any payload representability condition**. Every pending command has a corresponding queued or active line protocol transaction.
- Store and CAS completion guards are enabled for **all integer write values** whenever core has M permission.
- Any state with outstanding architectural/protocol/speculative work has at least one enabled **meaningful progress** action without payload-representability assumptions. This is global deadlock *enabledness*, not a proof of fair-path termination.
- New SAT witness: a write of `1` completes starting from a payload map constantly `0`.
- Negative control: an old repeating queued-read starvation trace is **UNSAT** under RR, but becomes **SAT** with the deliberate unfair-arbiter mutation.
- Generic symbolic-N SMT lemmas verify RR-distance arithmetic, transaction rank bounds, and the arithmetic descent of each service-step type for every `N >= 1`.

### Transaction progress for any finite N (conditional theorem)

With a currently active directory transaction, let `W` be waiting victim acks/writebacks, `D` undelivered recalls or invalidations, and `G` outstanding grants. Define:

```
R = 0                 if directory idle
R = 8 + 3W + D        during phase 0
R = 2 + G             during phase 1
```

For any finite N, `0 < R <= 8+4N` while active. Every protocol servicing step strictly decreases R:

- Delivering a recall/invalidation: D decreases, so R decreases by 1.
- Accepting an ack/writeback: W decreases, so R decreases by 3.
- Issuing the grant: phase 0 with W=D=0 passes from R=8 to R=3.
- Delivering the grant: G goes 1 to 0, so R decreases by 1.
- Accepting grant acknowledgement: the transaction becomes idle, so R decreases from 2 to 0.

Other steps cannot increase this rank during an active transaction. If the scheduler weakly fairly services enabled internal actions, each active transaction finishes in at most `8+4N` **servicing steps** (not a bounded number of wall-clock transitions). The arithmetic cases have symbolic-N SMT proofs. For concrete system instantiations, we also prove that the real transition formulas satisfy the rank/guard/frame obligations. The *universal* correspondence of every generated `Protocol(N)` transition to these abstract rank cases is explained by the transition schema, but is **not a machine-checked induction over arbitrary N**.

### Conditional fair-path theorem for architectural commands

Assume for every line and core:

1. The system begins in its strengthened inductive invariant.
2. Every continuously enabled protocol servicing action is eventually scheduled (**weak fairness**).
3. A continuously enabled *line directory-start event* is eventually scheduled (**weak fairness of the disjunction**, not individual core start actions).
4. Each architectural CPU ask/complete action that is enabled infinitely often eventually executes (**strong fairness**) — needed because permission may be granted then revoked before completion.
5. For speculative work, branch/environment outcomes eventually confirm or squash unresolved work; confirmed-store issue and confirmed-load retirement/replay receive fair scheduling.

**Claim (ordinary architectural commands):** Under assumptions 1–4, every issued read, store, and CAS eventually completes, for every concrete `N >= 1` and finite number of lines, *provided* the generic inductive MSI invariant and the uniform transition schema's progress lemmas hold for that N.

**Proof argument:** Pending requests persist until selected. An active transaction terminates under servicing fairness. A queued request therefore reaches an idle directory and is eventually selected; the RR distance prevents it being bypassed on infinitely many start events. The selected transaction completes, clearing the requesting core's pending bit and installing its permission. If a busy core has no pending request, it must have an enabled ask or completion. With no further loss of permission, weak/strong fairness forces a completion. If an adversary repeatedly revokes permission before the CPU completes, either the core has another pending transaction (which terminates as above) or an ask eventually occurs; infinitely many successful grants make the appropriate completion action enabled infinitely often. Strong fairness then forces completion, contradicting an indefinitely busy core.

Under assumption 5, confirmed speculative stores make their way into the architectural frontend and complete, and confirmed speculative reads settle or replay. **Squashed speculative instructions do not have to complete**; it is incorrect to claim that every staged speculative write eventually commits.

**Scope:** This is a mathematical assume-guarantee fair-path argument supported by checked local lemmas, **not** an automatically generated Büchi/CTL/LTL temporal-model-checker certificate for the whole system. The full arbitrary-N system invariant is machine-checked only at the concrete instantiations reported below, not as a universal inductive theorem. There is also no independently machine-checked global sequential-consistency trace refinement theorem in this version.

## Verified configurations and limitations

- Fully checked revised model: 4 cores × 2 and 4 cores × 3 lines, including old+new speculative frontends.
- Wider fixed-core regressions: 1–6 cores, selected two-/three-line models, with the exact completed matrices recorded in the accompanying summaries.
- Generic proof obligations: arithmetic correctness of RR scheduling and transaction ranking for symbolic `N>=1`.
- Remaining for a truly universal machine-checked result: encode parameterized cache states/invariants in a proof assistant or obtain an automated parameterized-system proof; establish a full temporal proof certificate and trace refinement as needed. These are genuine open milestones, not silently assumed completed.

## Files

- `experiments/10_fair_progress/fair_progress_model.py`: complete revised transition model with explicit switch for an unfair-arbitration negative control.
- `tools/progress_v16_verify.py`: SAT/SMT validation and reproducible queries.
- `tools/progress_v16_witnesses.py`: time-indexed write-completion and starvation-cycle witnesses.
- `tests/test_progress_v16.py`: targeted tests.
- `tests/test_liveness_verify.py`: unchanged v1.5 negative controls.

## Research perspective

These results provide a solid fairness-aware baseline, **not yet a CAV-level algorithmic contribution**. A more novel follow-on would automatically infer the progress ranks, arbitration assumptions, and reusable local contracts from a changed protocol, with end-to-end temporal certificates and substantial improvements on independent benchmarks.
