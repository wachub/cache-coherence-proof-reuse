> **v2.0 MESI/MOESI extension:** See [MESI_MOESI_EXTENSION_v2_0.md](MESI_MOESI_EXTENSION_v2_0.md) for new abstract coherence variants, verified 4-core safety, progress premises and reproducible scripts. The full global temporal theorem is still open.

# Cache concurrency / coherence formal verification experiments

**A reconstructed, version-controlled research archive** of the incremental models developed in the preceding discussion, from the first explicit-state cache checker to speculative writes with a two-entry per-core queue.

> **Archive history note:** The commits and version tags in this repository were reconstructed **on 2026-11-05** from the available earlier artifacts. They represent a logical sequence of milestones, **not original development timestamps**. Source files and recorded solver outputs are preserved in separate snapshots; they were not retroactively refactored into a single uniform implementation.

## First things to read

- [`SAT_SMT_HEURISTICS.md`](SAT_SMT_HEURISTICS.md): problem-specific solver tactics, proof-reuse patterns, common pitfalls, and a template for future optimizations.
- [`docs/PROOF_STATUS.md`](docs/PROOF_STATUS.md): which claims were checked, which are paper-level arguments, and which remain assumptions.
- [`docs/ADDING_A_FEATURE.md`](docs/ADDING_A_FEATURE.md): practical workflow for each new feature.
- [`manifest.json`](manifest.json): archival source names, SHA-256 hashes, and milestone mapping.

## Versioned milestone snapshots

| Tag | Directory | Content |
|---|---|---|
| `v0.1` | `experiments/01_explicit_state` | Asynchronous single-line protocol; explicit-state reachability and mutants |
| `v0.2` | `experiments/02_single_line_smt` | SMT induction for fixed cache counts; in-flight grants, writebacks, ownership |
| `v0.3` | `experiments/03_two_line_publication` | Two-line release/acquire publication; ordering constrained at the interface |
| `v0.4` | `experiments/04_fifo_publication` | Explicit FIFO buffer; inductive publication check and bad bypass mutant |
| `v0.5` | `experiments/05_flush_invalidate` | Alternative intentionally weak, global-lock model with whole-cache invalidation |
| `v0.6` | `experiments/06_four_core_sc` | 4-core multi-line abstract MSI with strict memory operation order |
| `v0.7` | `experiments/07_speculative_load` | Incremental speculative load with version checking and replay |
| `v0.8` | `experiments/08_speculative_stores` | Two-slot speculative store queue per core; safe FIFO retirement, mutants |
| `v0.9` | Docs / archive | Formal heuristics, proof caveats, original archived zip files and verification helper |

**Important:** `v0.5` is an *alternative* weak-coherence branch, not a strengthening of MSI. Later SC models reuse the directory-based MSI lineage, not the global-lock model.

The `experiments/` directories are deliberately self-contained snapshots. Some common source files appear in multiple snapshots; this preserves the exact runnable context of the corresponding proof rather than introducing an unverified refactor.

## Using the Git history

```bash
git log --oneline --decorate
git tag --list
# Inspect a snapshot without replacing your current checkout:
git show v0.7:experiments/07_speculative_load/speculation_incremental_project/new_proof/INCREMENTAL_SPECULATION_PROOF.md
```

## Requirements

- Python 3.10+ recommended; the original files were generated using Python 3.13.
- A local Z3 shared library (`libz3.so.4`) is required by most SMT scripts, which invoke it via `ctypes`. A normal standalone Z3 executable can run the archived `.smt2` scripts as well.
- No extra Python Z3 package is required for the included SMT helpers, provided `libz3.so.4` is available.

## Quick reproducibility checks

```bash
python tools/verify_representative.py
```

The helper re-runs representative **new** queries in a temporary directory. It does not modify the archived proof artifacts. For the complete configuration matrix and mutation witnesses, follow each experiment's README/report.

Example direct reproduction:

```bash
cd experiments/08_speculative_stores/speculative_stores_project
python speculative_store_delta.py --cores 4 --lines 2 --out-dir /tmp/store_delta_check
```

## Scope and caution

This is **abstract finite-configuration protocol verification**, not signoff of commercial processors or RTL. UNSAT inductive-step checks imply unbounded execution *depth for each checked finite configuration*; they do **not** by themselves prove arbitrary cache counts, all memory programs, liveness, RTL correctness, or any full ISA memory model. Some trace-refinement/SC claims have supporting paper-level arguments rather than separate mechanized end-to-end proofs. See the individual reports and `docs/PROOF_STATUS.md`.

No new hardware verification claim is made merely by packaging these files in Git.


## v1.0 — Combined bounded speculative reads and writes (2026-11-05)

The latest snapshot lives at `experiments/09_combined_speculative_reads_writes/`.
It combines one speculative load with up to two earlier private speculative
stores per core, validates forwarded and cached reads, and recovers by replay.
Four-core configurations with two and three independent cache lines passed
incremental SMT proof obligations **and** independent full-system induction;
concrete positive and negative SAT traces are bundled.

The verified claim concerns abstract safety invariants and local read/ordering
contracts. The global sequential-consistency trace-refinement argument is not
separately mechanized; progress and hardware/RTL behavior are not verified.


## v1.1: Fast incremental SAT/SMT verification toolkit

The previous experimental models and proof tags remain intact. New development utilities:

- [`docs/FAST_SOLVER_PLAYBOOK.md`](docs/FAST_SOLVER_PLAYBOOK.md) — step-by-step incremental formal-verification workflow and problem-specific SAT heuristics.
- [`tools/fast_verify.py`](tools/fast_verify.py) — checks the **exact existing combined-speculation SMT formulas** using one shared Z3 context, an exact-formula cache, predecessor MSI proof reuse, full-induction cross-check, and automatic failing-transition localization.
- [`tools/benchmark_solver.py`](tools/benchmark_solver.py) — compares isolated, shared-context and cached solver sessions.
- [`tools/invariant_core_hints.py`](tools/invariant_core_hints.py) — diagnostic UNSAT-core mining with an independent reduced-formula recheck.
- [`tests/test_fast_verify.py`](tests/test_fast_verify.py) — guards against assertion leakage, unsound cached reuse, missed mutants, and SMT formula changes.

For a full safety recheck of the current 4-core, 2-line configuration:

```bash
python tools/fast_verify.py --cores 4 --lines 2 \
  --verify-baseline --full-regression --check-mutants
python -m unittest discover -s tests -v
```

The cache does not establish new proofs; it reuses prior Z3 answers only for an **identical** SMT obligation and solver configuration. The proof still excludes arbitrary queue bounds, full trace-level SC refinement, and liveness.

## Codex project onboarding (documentation-only v1.2)

To continue this project with a coding agent, first read [`AGENTS.md`](AGENTS.md)
and the detailed [`CODEX_PROJECT_HANDOFF.md`](CODEX_PROJECT_HANDOFF.md).
These two documents describe current verified guarantees, unresolved proof gaps,
reproduction commands, proof-reuse heuristics, and a feature-addition protocol.
No transition-system source or SMT proof obligation changed in v1.2.

## v1.3: compositional contracts, no cache model change

The new [`docs/COMPOSITIONAL_VERIFICATION.md`](docs/COMPOSITIONAL_VERIFICATION.md)
explains the seven typed interface contracts for the *existing* speculative
ordering behavior, automatic SMT-LIB2 `define-fun` layering, dependency-sliced
proof caches, and an incremental proof manifest. The cache protocol and all
historical experiments are unchanged.

```bash
python tools/compositional_verify.py --cores 4 --lines 2 --no-cache \
  --baseline --full-regression --check-mutants \
  --output-dir artifacts/compositional_4c2l
```

There is a separate [quickstart](docs/COMPOSITIONAL_QUICKSTART.md).
The 29 modular contract checks complement—not replace—baseline induction,
full-system induction, or the as-yet-unmechanized SC trace refinement.

## v1.4 — Automatic generation and reuse of speculative-ordering contracts

**No changes to cache models.** `tools/infer_ordering_contracts.py` learns each
speculative transition family's allowed architectural effects from a reusable
four-event vocabulary, emits portable SMT-LIB2 proof queries, checks against
v1.3 manually written contracts, and can prove that newly inferred contracts
preserve previously certified interfaces. For details and examples see
[`docs/AUTOMATIC_ORDERING_CONTRACTS.md`](docs/AUTOMATIC_ORDERING_CONTRACTS.md)
and [`docs/CONTRACT_SYNTHESIS_QUICKSTART.md`](docs/CONTRACT_SYNTHESIS_QUICKSTART.md).
This is template-based contract inference, **not** arbitrary contract discovery,
and it does not close the outstanding trace-level sequential-consistency proof.

## v1.5: protocol progress, deadlock, livelock, and starvation analysis

No cache or speculative-execution transitions were modified. The new `tools/liveness_verify.py` and [`docs/LIVENESS_PROGRESS_ANALYSIS.md`](docs/LIVENESS_PROGRESS_ANALYSIS.md) add four-core local progress checks, a decreasing rank for every active coherence transaction, conditional combined-system enabledness checks, and two machine-checked reachable negative examples: a symbolic-payload store stall and weakly fair starvation of a queued request. **Neither unconditional global liveness nor starvation freedom is claimed.**

```bash
python tools/liveness_verify.py --cores 4 --lines 2 3 --output-dir /tmp/cache_liveness
python -m unittest discover -s tests -v
```

### v1.6 revised fair-progress model

The original v1.5 safety/liveness model and its counterexamples are retained. A new
round-robin directory and mutable symbolic-data model is in
`experiments/10_fair_progress/`. It checks inductive safety, deadlock/progress
obligations, arbitrary-value store execution, starvation negative controls, and
symbolic-`N` rank/arbitration lemmas. Conditional fairness assumptions and proof
limits are documented in [`docs/FAIR_PROGRESS_V1_6.md`](docs/FAIR_PROGRESS_V1_6.md).
Run `python tools/progress_v16_verify.py --cores 4 --lines 2 3`.

### v1.7 experimental temporal-fairness branch

Branch `proof/temporal-fairness-v1.7` adds a proof-only confirmed-load invariant,
290 concrete SMT progress/induction obligations, and an exhaustive fair-lasso
checker for a finite request-progress abstraction. Fair liveness is reasoned
about under explicit weak/strong fairness assumptions; **a native machine-checked
global temporal proof of the original infinite-state model is not yet supplied**.
See [`TEMPORAL_FAIRNESS_v1_7.md`](TEMPORAL_FAIRNESS_v1_7.md).

### v1.9: progress and deadlock audit after directory-invariant minimization

Branch `proof/minimized-invariant-progress-v1.9` verifies 459 concrete SMT
obligations (169 freshly solved; 290 reused by exact SHA-256 matching of prior
UNSAT proof queries), 10 symbolic-N arithmetic lemmas and 15 finite fair-lasso
checks for the v1.8 minimized-invariant model. Three actual transition-trace
witness/mutant checks pass. The entire 41-test regression suite passes.

See `MINIMIZED_TEMPORAL_PROGRESS_v1_9.md` and run:

```bash
python tools/verify_temporal_progress_v19.py --cores 4 --lines 2 3
python -m unittest discover -s tests -q
```

**Limit:** this verifies no-terminal-deadlock enabledness and all local progress
premises, not a native global temporal liveness certificate for the unbounded
concrete state system.
