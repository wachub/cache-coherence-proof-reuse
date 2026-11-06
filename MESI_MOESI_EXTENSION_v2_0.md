# v2.0 — Plug-in MESI and MOESI coherence models with fresh SMT verification

**Branch:** `feature/mesi-moesi-composable`, forked from v1.9 `proof/minimized-invariant-progress-v1.9`.

## Scope and nonclaims

This is an **abstract, fixed-configuration transition-system verification experiment**; no RTL is generated. `ExtendedProtocol` replaces the per-cache-line MSI protocol, while the original speculative write queue and speculative read/replay logic, unbounded integer-valued ghost payload representation, ordinary CPU commands, and round-robin arbiter are reused. Frontend **permission guards and E->M completion effects** are updated where necessary. The original v1.9 MSI source and earlier proof branches remain unchanged.

**Do not claim that the old MSI SMT proof certificates were reused unchanged:** the protocol transitions and invariants have changed. Our tests *freshly* discharge safety induction and architectural speculative-effect contracts for the new variants. We have achieved a reusable software/model module boundary, not yet an algorithm that automatically detects re-usable proof subcertificates for arbitrary upgrades.

**Do not claim full temporal liveness, sequential-consistency trace refinement, arbitrary-core correctness, or actual hardware data routing.** We have inductive safety proofs and progress premises for the explicitly enumerated fixed-size configurations, plus path witnesses. Fair eventual-completion reasoning remains conditional and not an independently accepted global LTL certificate, as in v1.9.

## Abstract cache and directory states

| Mode integer | MSI | MESI | MOESI |
|---|---|---|---|
| 0 | I | I | I |
| 1 | S | S | S |
| 2 | M | M | M |
| 3 | — | E | E |
| 4 | — | — | O |

### MESI

* A read miss of a line with no current sharers can be granted **E**.
* E->M upon completed store or successful CAS requires **no directory transaction**; failed CAS retains E.
* A remote read of an E owner cleanly downgrades E->S, retaining both Shared copies.
* A remote read of M first recalls/updates memory and then supplies S.

### MOESI

* A read of M or O by another core produces a dirty **O** owner and an S requester; the abstract directory's `mem` can remain stale.
* The owner's response token (`wbv`) is copied into the **requester's response slot** (`grv`) before the Shared grant; an invariant establishes that it equals `latest`.
* On O->M upgrade, the directory invalidates all other sharers and then grants M. An O owned by another core is recalled, and an exclusive writer waits for the response.
* E remains clean; O may be dirty; M/E cannot coexist with other Shared copies, but O can.

This is a symbolic value/version specification: real packet fields, caches with capacity, memory pipelines and L1-to-L2 bus routing are deliberately absent. `wb` represents an abstract owner response, **not necessarily a DRAM writeback** in the O read path.

## Machine-checked safety

All stored safety checks returned **UNSAT** (absence of an initialization, induction, bad-state, or architectural speculative-contract violation):

| Variant | Cores × lines | Obligations | Result |
|---|---|---:|---|
| MESI | 2 × 1 | 7 | Pass |
| MOESI | 2 × 1 | 7 | Pass |
| MESI | 4 × 2 | 10 | Pass |
| MOESI | 4 × 2 | 10 | Pass |
| MESI | 4 × 3 | 13 | Pass |
| MOESI | 4 × 3 | 13 | Pass |
| **Total** | | **60** | **60/60** |

The SMT queries include:

```
Init(s) ∧ ¬I(s)                                      UNSAT
I(s) ∧ T(s,s') ∧ ¬I(s')                             UNSAT
I(s) ∧ Bad(s)                                       UNSAT
I(s) ∧ DeltaSpec(s,s') ∧ ¬ArchitecturalEffects(s,s') UNSAT
```

plus separate per-line coherence checks and transaction rank checks. Each checker emits actual SMT-LIB2 queries, SHA256 hashes, and Z3 verdicts. `unknown` is not accepted.

## Progress and deadlock premises

* 2 cores × 1 line: **64/64** complete SMT progress premises (both variants).
* 4 cores × 2 lines: **174/174** complete SMT progress premises (both variants).
* 4 cores × 3 lines: **28/28** selected key progress premises (both variants), including global no-terminal-stall enabledness, active-directory service enabledness, service-event stability, and CPU ask/complete enabledness. In addition, the full **118/118 MESI** three-line progress suite completed. The complete **MOESI** three-line progress sweep was not finished; no unexecuted/timeout result is counted as proved.

An important distinction from the old MSI proof: while a recall of E is pending, E->M can turn `deliver_recall_E` into `deliver_recall_M`. Thus weak fairness should apply to the **combined service event** `SomeService(line)`, whose continuously enabled status is verified; *individual service guard* persistence is false, and is **not** claimed.

The proved **no-terminal-stall** property establishes that outstanding work has an enabled progress action; by itself it does not rule out a fair infinite livelock. We have not proved global concrete temporal liveness or starvation freedom on every fair execution of the new MOESI/MESI systems.

## Reachability and negative tests

Actual concrete time-indexed SMT traces, starting from `Init`:

| Trace | Steps | Z3 |
|---|---:|---|
| MESI I->E->M after read and local store | 9 | SAT |
| MESI clean E->S downgrade on remote read | 16 | SAT |
| MOESI dirty M->O, another core obtains S, memory stale | 18 | SAT |
| MOESI O->M upgrade, other sharer invalidated | 27 | SAT |

Two deliberately invalid transitions each produce **SAT violations of inductive safety**: granting E with an existing sharer, and dropping an O owner without preserving dirty data. Negative controls are essential; a collection of UNSAT checks could otherwise be vacuous.

## What was reused and what changed

**Inherited unchanged by source:** limited two-slot speculative store queue, forwarding order, confirmation/squash, speculative read replay, CPU one-inflight architectural model, mutable version->value ghost arrays, round-robin arbitration algorithm.

**Changed:** cache permission states; owner/share semantics; recall/grant handling; remote E downgrade and M->O data response; CPU write/read/CAS permission guards; speculative cache-valid guard; associated inductive invariant and proof queries.

**Reproved rather than certificate-reused:** all new-model safety induction, safety and speculative-effect SMT obligations. Any future automatic *certificate reuse* tool must soundly prove an interface relation across the modified systems.

## Reproduce

Requires Python 3 and `libz3.so.4`, no Python z3 package:

```bash
python tools/verify_mesi_moesi_v20.py --cores 4 --lines 2 --variant both
python tools/verify_mesi_moesi_v20.py --cores 4 --lines 3 --variant both
python tools/verify_extended_progress_v20.py --cores 4 --lines 2 --variant both
python tools/verify_extended_focused_v20.py --cores 4 --lines 3
python experiments/12_mesi_moesi/witnesses.py
python experiments/12_mesi_moesi/negative_controls.py
python -m unittest discover -s tests -q
```

A full 4x3 progress sweep can be attempted with `python tools/verify_extended_progress_v20.py --cores 4 --lines 3`; because it is expensive, do not conflate focused 3-line results with the full sweep.

## Research next steps

1. Machine-check a *sound protocol-extension interface/refinement theorem* from MSI to MESI and MOESI; identify truly reusable unchanged proof certificates instead of rerunning full induction.
2. Extend the old fair-path temporal argument and obtain an independent machine-checked global LTL/CTL/fair-progress theorem for the new transition systems.
3. Prove complete architectural memory-model trace refinement, and attempt parameterized N-core correctness.
4. Compare SMT solve cost and certificate reuse against external protocol frameworks; merely adding E and O states is not in itself CAV-level novelty.
