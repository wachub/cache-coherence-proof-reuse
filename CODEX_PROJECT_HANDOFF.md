# Codex Project Handoff — Incremental Formal Verification of Multicore Cache Coherence and Speculation

**Project status:** 2026-11-05  
**Current codebase:** `cache_concurrency_formal_git_v1_1.zip` (Git tags `v0.1`–`v1.1`)  
**Language/tools:** Python 3, SMT-LIB, Z3 (`libz3.so.4`), Git  
**Current abstraction:** directory-based asynchronous MSI, **four cores**, **two or three cache lines**, up to **two private speculative stores and one younger speculative load per core**, with ordinary reads/writes/atomic compare-and-swap (CAS).  
**Intended audience:** Codex or another coding agent continuing research in this repository.

## 1. Project objective and philosophy

Build a *reusable, incrementally verified abstract model* of a multicore shared-memory system. Begin from a deliberately simple, strongly ordered directory-based MSI cache system. Add features such as speculation, store queues, reordering, and buffering **one at a time**, and avoid re-proving unchanged parts of the system when a sound proof decomposition can reuse them.

This is **not** currently an RTL, chip-design, or performance-optimization project. Remain at the level of abstract transition systems, SAT/SMT formulas, operational memory semantics, and proof obligations unless the user explicitly changes that scope. The goal is a coherent foundation for experimenting with increasingly complex memory-system features, checking safety, identifying counterexamples, and measuring **verification effort**.

The central research question is: *Given a verified memory/coherence model, can a new optimization be verified efficiently by checking only its changed state, transitions, ordering/interface contract, and interactions with the old invariants?*

Crucially, optimize **solver work and proof reuse** without weakening a correctness specification or calling an unchecked claim a theorem.

## 2. Conceptual foundation: coherence is not memory ordering

- **MSI/MESI/MOESI coherence** controls access to a *single cache line*. If multiple cores hold a line in `S`, a writer must gain `M`, invalidating other copies before modifying its coherent value. This does not depend on a software lock. The lock and protected data can be on different cache lines.
- **Cross-line memory ordering** imposes restrictions on the order in which operations become architecturally observable. For example, an earlier write to `data` must not be overtaken by a later release of `flag` when release/acquire synchronization requires publication. Per-line coherence does not by itself provide this ordering.
- **Baseline simplification:** no ordinary store buffers, no out-of-order retirement, and no speculation initially. Give each core at most one outstanding architectural memory operation; complete it before allowing a subsequent architectural command to retire. Atomic CAS occurs under the same exclusive-permission discipline as writes. The MSI model plus this strict frontend provides a straightforward paper-level sequential-consistency (SC) argument.
- **Speculation:** execute or compute data early, but do not expose a speculative store to shared memory until it is confirmed and reaches the correct program-order retirement point. Speculative loads may retire only after validation, and can replay through ordinary MSI if stale.
- A **machine-checked invariant** and a **machine-checked end-to-end trace refinement theorem** are not the same thing. Keep them separate throughout the project.

### Terms to preserve

`Read(line)`: an architectural load.  
`Store(line, value)`: an architectural store.  
`CAS(line, expected, desired)`: atomic compare-and-swap; compare **data values**, not write-version tokens.  
`I/S/M`: invalid/shared/modified cache permissions.  
`ref_l`: ghost reference/coherent version for line `l`.  
`payload_l(version)`: immutable symbolic array mapping a write version to an integer data value. Different versions **may have equal payloads** (ABA).  
`busy`: original frontend command still in flight, even when a speculative queue entry has already been issued into that frontend.

## 3. Repository and version history

The Git history was **reconstructed from prior experiment artifacts on 2026-11-05**. Tags represent logical milestones, *not* their original development dates. Do not rewrite historical snapshots into one unverified “clean” implementation; they intentionally have different assumptions and checking methods.

| Tag | Experiment | Accomplishment and limitations |
|---|---|---|
| `v0.1` | `experiments/01_explicit_state` | Explicit-state, asynchronous, single-line MSI exploration; reachable-state safety checks and deliberately broken variants, small finite configurations. |
| `v0.2` | `experiments/02_single_line_smt` | Inductive SMT checks for one-line coherence across several fixed core counts (reported 2–16), with outstanding coherence requests, dirty writeback, grants and acknowledgements. |
| `v0.3` | `experiments/03_two_line_publication` | Fixed-program, two-core/two-line release-acquire publication check. **Not** a universal memory-ordering proof. |
| `v0.4` | `experiments/04_fifo_publication` | Explicit two-entry FIFO store buffer, a fixed two-core, three-line/flag publication program, and a bad bypass mutant. **Not** arbitrary programs. |
| `v0.5` | `experiments/05_flush_invalidate` | **Alternative** simple global-lock, flush-on-release/invalidate-on-acquire weak-cache architecture; finite-state checking. This is **not** the MSI lineage used in later versions. |
| `v0.6` | `experiments/06_four_core_sc` | Four-core, two/three-line directory MSI with arbitrary streams of architectural Read/Store/CAS; one in-flight command/core; inductive safety + paper-level SC trace argument. |
| `v0.7` | `experiments/07_speculative_load` | One speculative read/core, private saved value/version, validation at retirement, replay on invalidation; delta SMT checks and bad mutant. |
| `v0.8` | `experiments/08_speculative_stores` | Up to two private speculative stores/core; confirm or squash; issue only the oldest confirmed store into ordinary MSI; checks for premature publication or out-of-order issue. |
| `v0.9` | Documentation | Formal proof-status index, SAT/SMT heuristics, feature-addition workflow, original archives. |
| `v1.0` | `experiments/09_combined_speculative_reads_writes` | **One model with both speculative reads and writes**, forwarding from earlier stores, validation/replay, independent combined-system induction, witnesses and mutants. |
| `v1.1` | `tools/`, `tests/`, `docs/FAST_SOLVER_PLAYBOOK.md` | Faster verification runner, cached exact-query results, shared Z3 sessions, proof layering, localization, UNSAT-core diagnostics and regression tests. |

Important starting files:

- `README.md`: archive overview and Git tags.
- `docs/PROOF_STATUS.md`: verified properties, scope and limitations.
- `docs/ADDING_A_FEATURE.md`: release checklist for changes.
- `docs/FAST_SOLVER_PLAYBOOK.md`: implemented fast-solver workflow.
- `SAT_SMT_HEURISTICS.md`: mathematical, problem-specific heuristics.
- `experiments/09_combined_speculative_reads_writes/README.md`: authoritative current-model semantics and witnesses.
- `experiments/09_combined_speculative_reads_writes/combined_speculative_model.py`: current combined transition system.
- `experiments/09_combined_speculative_reads_writes/sc_msi_4core_verifier.py`: inherited baseline frontend/MSI.
- `experiments/09_combined_speculative_reads_writes/full_regression.py`: full combined-system induction.
- `experiments/09_combined_speculative_reads_writes/mutant_checks.py` and `witnesses.py`: negative and positive tests.
- `tools/fast_verify.py`, `tools/benchmark_solver.py`, `tools/invariant_core_hints.py`: current verification tooling.
- `tests/test_fast_verify.py`: regression tests.

## 4. Baseline transition-system model (v0.6)

The abstract machine comprises four processor frontends, privately cached copies of each modeled line, and an asynchronous directory per line. For each line, caches transition among `I`, `S`, and `M`. Ownership transfers can require recall/invalidation, invalidation acknowledgements, dirty-data writeback, and grants/acknowledgements. Delivery and interleavings are nondeterministic; the directory serializes its own transactions for a given line. Separate lines can have independent in-flight coherence events.

A core may issue an arbitrary architectural `Read(l)`, `Store(l,v)`, or `CAS(l,e,v)` when its old frontend is idle. Only **one architectural request per core** may be in flight at a time, and the next request cannot overtake it. A completed operation observes or updates the per-line reference/coherent value. A CAS compares the actual payload at the atomic point with `expected`; if equal, it updates to the desired payload, otherwise it fails/returns the prior value according to the model's interface.

**Version encoding:** On a write, assign a new version token; symbolic `payload_l` maps versions to arbitrary integers, including repeated values. This makes freshness assertions easier and retains genuine data comparisons for CAS. It is a ghost modeling abstraction, not a proposed cache implementation.

The baseline SMT model checks inductive properties involving coherence ownership, data preservation, value freshness, and reference-value agreement, plus frontend single-command discipline. The global SC story takes architectural completion steps in global transition order and argues they preserve source program order and sequential reference memory behavior. That argument has **not** been encoded as a separate, universally quantified trace-refinement theorem.

## 5. Speculative-load extension (v0.7)

A core may capture a speculative load result while an earlier instruction remains unresolved. The capture is **not yet an architectural read event**. The speculative state remembers source line, actual captured payload, validity, and a version/freshness token. At retirement:

1. Earlier architectural work must have completed.
2. A cached speculative result may retire only if it is still valid and matches the coherence/reference state.
3. Otherwise the speculative result is discarded/replayed through the original read mechanism.

Proof obligation: new speculative steps preserve inherited MSI invariants and speculative well-formedness; the fast-retire step must return the current abstract value. An intentionally broken “retire without validation” variant produces a SAT stale-read counterexample. This checks the abstract validation rule, **not** a hardware implementation of invalidation monitoring.

## 6. Speculative-store extension (v0.8)

Each core may stage **at most two** private speculative stores. These stores have no shared-memory effect until they are confirmed and subsequently issued through the original MSI frontend. A wrong-path suffix is discarded on squash. Confirmed stores issue FIFO, by original program order, one at a time; one store may leave the queue when issued but is not yet globally complete while the old frontend's `busy` flag remains set.

This extension is designed to be a stuttering refinement for most speculative steps, plus ordinary old-machine store issuance at appropriate points. Two mutants demonstrate why coherence safety alone is insufficient:

- **Overtake:** issue/retire the second store before the first, breaking cross-line publication/program order even though per-line MSI remains coherent.
- **Premature publication:** permit an unconfirmed speculative store to reach coherent memory.

This model does **not** allow a speculative write to modify externally visible memory and then roll it back.

## 7. Integrated speculation (v1.0): current reference baseline

The integrated four-core model allows **up to two private speculative stores and one younger speculative load per core**, simultaneously, for two- or three-line configurations. It is **not** merely a conjunction of independently verified read-only and write-only models.

- Queued stores may target the same line or different lines.
- A younger speculative read should forward from the **youngest older** pending speculative store to its address. If none matches and the cache line is valid, it may capture a cached value.
- **No later store can be staged after that outstanding speculative read** in this simplified scheduling discipline.
- Correct-path confirmation is nondeterministic and marks speculation eligible for ordered retirement. Wrong-path squash removes unconfirmed speculative work. Branch prediction and correct-path control-flow semantics are outside the model.
- A confirmed store enters the original MSI frontend only from the FIFO queue head. It is not fully completed until the old frontend finishes.
- A speculative load may retire fast only when its older queued stores are gone **and** the old frontend is idle (`busy=false`). If cached, check retained version/validity; if forwarded, check that the captured value still agrees with the coherent value after all older stores complete. Otherwise replay an ordinary MSI read.
- Read payload and version are explicitly related by an invariant, e.g. `active ∧ from_cache ⇒ speculative_value = payload_l(captured_version)`. Captured version equality **alone** is not sufficient if the SMT inductive hypothesis leaves the payload unconstrained.

**Positive SAT execution witnesses archived in v1.0:**

1. 14-step execution: stage `A=11`, stage `A=22`, speculative read of A forwards `22`, stores commit in order, load retires with `22`.
2. 19-step cross-line execution: stage `A=11`, `B=22`, speculative read A forwards the youngest *matching* write, `11`.
3. 9-step wrong-path squash: private speculative write/read are discarded, another core reads unchanged A.
4. 27-step stale-forward/replay: another core overwrites A; the old forwarded read is rejected and replay returns the newer data.

**Negative controls:** disabled validation produces a SAT stale-read witness (20 steps); prematurely retiring a load while an older store remains pending produces a SAT witness (11 steps). SAT witnesses show **existence of selected executions**; they are not complete proofs. Correct-system safety comes from UNSAT inductive obligations.

## 8. What exactly was checked

For fixed **four-core, two-line** and **four-core, three-line** configurations, the archived results report:

- Original MSI initial-state, step-induction and safety queries: **UNSAT**.
- New speculative-state initialization: **UNSAT** for violations.
- New transitions preserve speculative invariant `J`: **UNSAT** for violations.
- New transitions preserve original MSI invariant `I_MSI`: **UNSAT** for violations.
- New transitions obey the old memory interface/projection: **UNSAT** for violations.
- A fast speculative read returns the current coherent value: **UNSAT** for violations.
- Forwarding chooses the youngest preceding matching store: **UNSAT** for violations.
- A fast read cannot retire before older memory operations finish: **UNSAT** for violations.
- **Independent full combined-transition-system induction:** initial/inductive/safety checks **UNSAT**.
- Deliberately incorrect mutant formulas: **SAT**, detecting intended broken guards.
- Concrete reachable positive witness formulas: **SAT**.

The v1.0 model reports 76 added transition schemas in the two-line configuration and 108 in the three-line configuration. Induction means **unbounded execution length within that fixed-size transition system**. It does **not** mean arbitrarily many cores, arbitrarily many lines, arbitrarily deep queues, unconstrained reorder buffers, or infinite data-plane hardware.

**Fresh recheck made for this handoff:** on 2026-11-05, the v1.1 command with `--no-cache --verify-baseline --full-regression --check-mutants` returned `all_requested_proofs_passed: true` and `mutants.detected: true` for **both 4×2 and 4×3**. The five `tests/test_fast_verify.py` regression tests also passed. Z3 reported version `4.13.3.0` in the verified runner output. These checks replay the same authored formulas; they do **not** constitute an independent audit of the specification.

## 9. Inductive proof decomposition — reuse without unsound shortcuts

Let `s` be old machine state, `q` new feature state, `I_old(s)` a previously proved inductive invariant, `J(s,q)` the new invariant, and `Δ_new((s,q),(s',q'))` added transitions. The core pattern is to ask whether a **violation** is satisfiable:

```text
Initialization:  Init_new(s,q) ∧ ¬(I_old(s) ∧ J(s,q))
New-state step:  I_old(s) ∧ J(s,q) ∧ Δ_new ∧ ¬J(s',q')
Old safety:      I_old(s) ∧ J(s,q) ∧ Δ_new ∧ ¬I_old(s')
Interface:       I_old(s) ∧ J(s,q) ∧ Δ_new ∧ ¬RefinementCondition
```

Each must return **UNSAT**, and inherited transitions must also preserve the combined invariant. Existing proof reuse is justified only when inherited actions remain equivalent or are suitably restricted, **frame all new state**, and satisfy the new interface contract. Any modified inherited action must be rechecked. The predecessor MSI proof does **not** guarantee that speculative operations retire in program order: an explicit architectural interface/refinement obligation is essential.

Typical allowed new visible behaviors:

1. Speculative internal steps that **stutter** on the architectural reference state.
2. Issue the **oldest confirmed** speculative store through the old MSI interface.
3. Replay a speculative read through the original read path.
4. Fast-retire a speculative read, as an abstract read event, only when it returns the current coherent value and all older operations have completed.

A full trace-level simulation relation connecting arbitrary histories of the combined concrete and SC abstract machines would strengthen the overall correctness story. This remains **open**; do not label current checks a fully mechanized SC trace refinement theorem.

## 10. Implemented solver accelerations (v1.1)

**These are implemented and tested:**

- **Shared Z3 context:** one set of declarations, then `push/assert/check-sat/pop` per goal. The logical goal bodies match the archived SMT formulas byte-for-byte.
- **Exact-query cache:** SHA-256 content key for declarations, formula, solver version, timeout and seed; reuse only identical obligations/configurations; clearly mark cached vs solved.
- **Layered verification:** check/reuse original MSI proof, check only delta obligations, then optionally rerun complete combined induction.
- **Failure localization:** if aggregate delta check is SAT, check every relevant added transition schema to identify violations; don't silently assume core symmetry.
- **Mutation sensitivity:** require intentionally broken read validation and premature read retirement to produce SAT.
- **UNSAT-core diagnostics:** mine which named invariant assumptions support a particular query and recheck a reduced query, but **never** promote a local core into a new inductive invariant without proving it.
- **Regression tests and benchmarking:** compare isolated and shared contexts, cold and hot cache, keep exact formulas and solver version recorded.

A small recorded benchmark of seven two-line incremental obligations showed approximately **0.605 s** separate sessions vs **0.371 s** shared context (~1.63×), and about **0.0067 s** on a repeated exact-query cache hit. These are small-sample, machine-dependent verification timing figures; they do not measure hardware speedup.

**Only proposed, not yet implemented/proved:** general symmetry reduction, queue-capacity parameterization, general PDR/IC3, interpolation, solver portfolios, sophisticated invariant discovery, unrestricted reorder buffers. Do not describe these as existing features.

## 11. How to reproduce

Unpack the Git ZIP, enter the top-level repository, and ensure Python 3 and the Z3 shared library (`libz3.so.4`) are available. The current runner invokes the C library, and the documented release flow does not require a separate Python `z3` package.

```bash
# Fresh baseline + delta + full combined induction, 4 cores / 2 lines
python tools/fast_verify.py --cores 4 --lines 2 \
  --verify-baseline --full-regression --check-mutants --no-cache

# Repeat with 3 independent cache lines
python tools/fast_verify.py --cores 4 --lines 3 \
  --verify-baseline --full-regression --check-mutants --no-cache

# Fast delta-only iteration: exact-query cache and shared context
python tools/fast_verify.py --cores 4 --lines 2

# Save a new bundle of the exact SMT-LIB goals for auditing
python tools/fast_verify.py --cores 4 --lines 3 --no-cache \
  --emit-smt .fast_verify_outputs/queries_4_3

# Speed comparison and diagnostic invariant-core hints
python tools/benchmark_solver.py --cores 4 --lines 2 --repeats 3
python tools/invariant_core_hints.py --cores 4 --lines 2

# Tooling regression tests
python -m unittest discover -s tests -v

# Git history and original experimental snapshots
git tag --list
git log --oneline --decorate
```

Interpret runner output carefully: `all_requested_proofs_passed=true` means the requested **UNSAT** checks succeeded; `mutants.detected=true` means intentionally broken variants were **SAT**, which is the desired result. In the runner's mutant object, `passed=false` can describe the *broken mutant* rather than a failure of mutation detection; consult `detected` and individual goal statuses.

Treat Z3 `unknown`, timeout, crash, inconsistent cache key, or unexpectedly UNSAT broken mutants as **failures requiring investigation**.

## 12. Common pitfalls and how to avoid them

- **Coherence ≠ program-order correctness.** A fully coherent MSI model can still publish flag before earlier data writes if store ordering is relaxed incorrectly.
- **Queue slot freed ≠ operation completed.** Wait for the baseline frontend to become idle before retiring younger speculative reads.
- **Read-your-own-write forwarding:** read the youngest *earlier* matching queued store, never the oldest and never an unrelated address.
- **Version ≠ value.** Two write versions may carry the same data; CAS compares real values. Guard against misusing versions to “solve” ABA by assumption.
- **No hidden state changes:** explicitly frame unchanged state fields in each transition. Unconstrained next-state variables can create spurious counterexamples or vacuous proofs.
- **Check old steps against `J`.** Inheritance is valid only with a real frame/assumption argument.
- **Don't reduce to a single core by fiat.** Symmetry reduction needs a proved permutation-invariance condition.
- **Don't infer liveness from safety UNSAT.** A scheduler can keep delaying messages forever; deadlock, starvation, fairness and bounded queues are separate questions.
- **Don't equate cache hit/UNSAT with independent certification.** Record whether a solver ran or a cached result was reused.
- **Don't change the specification during an optimization benchmark.** Compare formula hashes and query semantics.
- **An UNSAT induction check covers arbitrary run length, not arbitrary parameter sizes.**

## 13. Explicit boundaries of present claims

**Checked:** the specified inductive safety and interface/retirement conditions for fixed four-core, two-/three-line abstract combined-speculation models; known intentionally buggy variants admit SAT counterexamples; old MSI proof reuse and full combined induction agree on these particular goals.

**Argued but not separately mechanized:** end-to-end sequential-consistency trace-refinement theorem for every observable history of the combined speculative machine.

**Not checked:** arbitrary cores/lines/queue length; more than one speculative read per core; speculation that publishes unconfirmed writes and rolls them back; realistic superscalar reorder buffer; branch predictor semantics; TSO/ARM/C11 weak ordering; progress/deadlock/starvation-freedom; fairness, eventual message delivery; realistic cache eviction/replacement, TLB, DMA, devices, finite token wraparound; RTL or silicon; PPA/performance gains.

The phrase **“formally correct” must always be qualified by the model, assumptions, configuration, and property**. Avoid claiming that every possible speculative four-core processor has been verified.

## 14. Prioritized next research tasks for Codex

**First task (high value): mechanically check full trace refinement.** Define an explicit abstract sequential memory reference machine with an architectural event log. Extend the combined model's proof obligations to establish a forward simulation or refinement mapping for every old and added transition, including fast speculative reads and CAS results. This closes the most important current verification gap. If a general trace theorem is unwieldy, start with an explicit inductive simulation relation and a bounded sanity witness, but clearly distinguish bounded checks from a full proof.

**Second task:** generalize the two-slot speculative store queue to parameter `B`, initially test `B=3` without assuming correctness, then aim for a parametric FIFO invariant (with correct head, issue, confirmation, squash and program-order relations) for arbitrary finite `B`. Prove queue invariants by induction over queue length rather than enumerating every slot. Do not claim arbitrary `B` from checking `B=2` and `B=3`.

**Third task:** allow two outstanding speculative reads and consider read-after-write, write-after-read and read-after-read dependencies. Preserve the original MSI protocol and localize changed obligations. Keep precise data forwarding/validation semantics.

**Fourth task:** experiment with safe relaxed visibility/retirement rules or a small reorder buffer. State the intended memory model first (SC or weaker), then prove it. Add mutants that demonstrate a concrete bug if ordering constraints are removed.

**Fifth task:** improve solver automation only if new proofs become difficult. Potential approaches: PDR/IC3, automatic invariant suggestions, restricted symmetry reduction with proof, partial-order reduction, assumption slicing, cross-feature proof dependencies, and an SMT solver portfolio. Preserve soundness and benchmarking comparability.

**Do not** start by implementing RTL, gate-level design, GPU acceleration, or physical cache models; these are outside the user's currently chosen scope.

## 15. Protocol for every new feature commit

1. Read `docs/PROOF_STATUS.md`, `docs/FAST_SOLVER_PLAYBOOK.md`, and the latest experiment README.
2. Give the feature a **minimal operational semantics**: new states, guards, transition effects, observables, and speculative correctness/rollback assumptions.
3. Keep `experiments/09_*` immutable as the prior verified baseline. Implement the next feature in a **new directory** or clearly scoped extension, documenting precisely what is inherited.
4. Specify `J`, initialization, old-step preservation, delta-step preservation of `I_old` and `J`, and the architectural interface/retirement contract.
5. Generate exact SMT-LIB formulas. Attempt cheap localized checks first; run a fresh complete induction before declaring success.
6. Produce at least one **reachable positive SAT witness** exercising the new feature and one **intentionally buggy mutant** with a SAT counterexample.
7. Run both 4×2 and 4×3 when the feature is compatible. Include `--no-cache` in the release gate.
8. Report `UNSAT`/`SAT`/`unknown`, solver version, timing, core count, line count, queue capacities and other assumptions. Benchmark isolated vs shared context if useful.
9. Save scripts, emitted SMT formulas, solver outputs, positive witness, mutant trace, proof report, and proof-scope caveats; commit/tag the new milestone.
10. Ask whether the new model actually changes the intended architectural contract. If yes, do not “reuse” a theorem whose assumptions are no longer satisfied.

### First instruction to give Codex

> Read `AGENTS.md`, `CODEX_PROJECT_HANDOFF.md`, `README.md`, `docs/PROOF_STATUS.md`, `docs/FAST_SOLVER_PLAYBOOK.md`, and the v1.0 combined experiment. Reproduce the four-core, two-line and three-line fresh proof runs before modifying anything. Treat v1.1 as an immutable reference. Work at the abstract transition-system / SMT level, prefer incremental delta proofs with an independent full-induction release check, and never claim a broader proof than the checked formulas support. Propose the smallest rigorous next extension and implement it with a positive witness and a SAT-producing mutant.
