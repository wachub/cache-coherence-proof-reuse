# v1.0 — Combined speculative loads and writes over four-core asynchronous MSI

## Outcome (2026-11-05)

The **combined** abstract design passed SMT checks for **4 cores × 2 lines** and **4 cores × 3 lines**. Each core can stage **at most two private speculative writes** and **one younger speculative read**. The read can forward from the youngest preceding speculative write to the same line. All committed operations use the unchanged directory MSI model; a speculative read may retire fast only after all its older writes complete and its captured data is still coherent. Otherwise it replays through MSI.

This is genuinely **combined**: the speculative read and stores coexist in the **same transition system**, not merely in two independently verified variants. Z3 found reachable **SAT** witnesses for forwarding, replay, and squashing, and failures in two intentionally broken versions.

## Summary of machine checks

| Check | 4 cores / 2 lines | 4 cores / 3 lines |
|---|---|---|
| Original MSI initial, inductive, safety checks (rerun) | UNSAT ×3 | UNSAT ×3 |
| New initial-state well-formedness | UNSAT | UNSAT |
| New transitions preserve speculative invariant | UNSAT | UNSAT |
| New transitions preserve old MSI invariant | UNSAT | UNSAT |
| New transitions obey old-memory projection / correct abstract reads | UNSAT | UNSAT |
| Fast speculative read always returns current coherent value | UNSAT | UNSAT |
| Forward from youngest earlier matching store | UNSAT | UNSAT |
| Fast read cannot retire before earlier operations complete | UNSAT | UNSAT |
| **Full combined system** initial, inductive, safety checks (independent regression) | **UNSAT ×3** | **UNSAT ×3** |

Proof obligations use SMT-LIB and **Z3** via `libz3.so.4`, with symbolic, unbounded integer payload values and version tokens. `UNSAT` means there is no violating transition under the stated invariant; induction therefore covers any number of steps in the specified **fixed four-core systems**.

## Modeling assumptions and scope

1. Abstract directory-based asynchronous MSI protocol; arbitrary delayed coherence messages, one directory transaction per line, no speculative coherence modification.
2. **One non-speculative architectural memory command per core** may be in flight. That command is always completed before the next architectural command retires. Old R/W/CAS remain supported.
3. Two-entry **private** speculative store queue per core; entries may be staged while an older instruction is pending; only a confirmed FIFO head may be passed into ordinary MSI. The queue entry is removed when issued; `busy` remains true until that store **completes**.
4. One speculative read per core, younger than the queued stores. No new store can be staged *after* that read. The read may execute from a valid cached line, or forward the youngest matching queued store; unresolved reads do not modify shared memory.
5. A nondeterministic confirmation marks all staged writes and the younger read correct-path. A squash drops the unconfirmed suffix and the younger read. **Branch correctness is an environmental assumption**; no branch predictor or actual branch semantics are modeled.
6. A fast read may **retire only when the speculative store queue is empty and `busy=false`**. For cached speculation, the line must still be valid with the captured version. For forwarded speculation, the line must be valid with the forwarded current value. Otherwise, an ordinary MSI read is issued and eventually completes.
7. Symbolic payload arrays describe arbitrary integer values, including repeated values. Cache read version comparisons conservatively reject ABA; forwarded validation compares current data after the earlier stores complete. A real implementation of this abstract validation logic is **not** verified.
8. These are **safety** results; no liveness, starvation freedom, physical implementation, runtime improvement, or parameterized all-core proof.

## Incremental proof technique

Let `I_MSI` be the baseline inductive invariant, `J` the new queue/load well-formedness plus retained cached-value relation, and `Δ_new` the 76 (two-line) or 108 (three-line) new transition schemas.

The key new obligation is:

```smt
(assert (and I_MSI(s) J(s) Delta_new(s,s')
             (not (and I_MSI(s') J(s')))))
(check-sat)       ; UNSAT
```

For all inherited MSI actions, the original proof applies because their guards are only strengthened on new instruction issue, and they **frame every new speculative state field**. Thus the new proof can focus on `Δ_new`. As an extra consistency check, `full_regression.py` also reruns induction for the **whole combined transition relation**, which passed for both configurations.

Crucially, preserving MSI alone is insufficient. We separately check that the new architectural events are either:
- a stuttering step on old MSI state;
- an issue of the **oldest confirmed write** into the previous MSI frontend;
- a replay through the original read interface; or
- a fast read observation equal to the **current** coherent abstract value, after all older instructions finish.

This last case is a new abstract read event rather than an original MSI read transaction. Its return value is checked directly using the reference version `ref_l` and the immutable `payload_l` map. The simulator-style argument placing all architectural completions/fast reads in a single order is **not** a standalone machine-checked trace-refinement theorem; this limits what we claim as fully mechanized SC.

## Concrete SAT witnesses (4 cores, 2 lines)

- **14 steps — latest own-store forwarding:** stage A=11 then A=22; speculative read A forwards 22; stores commit 11 then 22; read returns 22.
- **19 steps — cross-line forwarding:** stage A=11, then B=22; speculative read A forwards 11; stores commit in order; read returns 11.
- **9 steps — squash:** stage A=77 and forward a younger read; squash both; another core reads the unchanged A=0.
- **27 steps — replay:** Core 0 forwards A=11 but Core 1 later writes A=77 and invalidates it; Core 0 replays through MSI and reads 77.
- **20 steps — broken no-validation mutant:** same history, but Core 0 incorrectly retires the obsolete value 11 after A becomes 77. SAT.
- **11 steps — broken premature-read mutant:** an earlier queued store is still pending when a younger load is retired. SAT.

The separate mutant one-step SMT queries also return **SAT**. Their corresponding correct-design obligations are **UNSAT**.

## Reproduction

Linux with Python 3 and `libz3.so.4` (original baseline adapter does not require the Python `z3` package):

```bash
python sc_msi_4core_verifier.py --cores 4 --lines 2 --output-dir base4_2
python sc_msi_4core_verifier.py --cores 4 --lines 3 --output-dir base4_3
python combined_speculative_model.py --cores 4 --lines 2 --output-dir delta4_2
python combined_speculative_model.py --cores 4 --lines 3 --output-dir delta4_3
python full_regression.py 4 2 full4_2
python full_regression.py 4 3 full4_3
python mutant_checks.py
python witnesses.py
```

Files: `combined_speculative_model.py` is the main combined transition system; `mutant_checks.py` and `witnesses.py` supply independent negative/positive SAT evidence; `full_regression.py` verifies full-system induction. `cache_smt_verifier.py`, `sc_msi_4core_verifier.py` and `sc_msi_trace_witness.py` are exact copies of prior foundational scripts. Direct SMT queries and solver logs are included in output folders.

## Next theoretical step

Move from hard-coded 2-slot states to a symbolic bounded FIFO invariant and then a parameterized proof for **any finite queue capacity**. Note that a parameterized capacity result is mathematically distinct from extending to arbitrary core counts. Both remain open for this project.
