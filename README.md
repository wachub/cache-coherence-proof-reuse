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

