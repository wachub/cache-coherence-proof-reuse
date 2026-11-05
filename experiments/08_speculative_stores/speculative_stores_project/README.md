# Incremental verification of TWO speculative writes per core

## Precise scope

This is a **small abstract extension**, not a transistor/RTL design or a complete speculative processor. It extends the existing single-in-flight-instruction 4-core asynchronous MSI and sequential-consistency model with a **two-slot speculative store queue on every core**. Values are symbolic integers. Two or three independent cache lines can be used.

A staged speculative write does NOT modify the coherent cache or architecturally visible memory. It is retained in a private queue until a nondeterministic (correct-branch) confirmation, or squashed on a (wrong-branch) resolution. **The confirmed oldest entry is then issued to the original, verified MSI machine**, which subsequently completes it. Unlike a plain store buffer, an unconfirmed entry can be discarded. This does not model speculation in arithmetic, loads, condition predictions, or the hardware mechanism for deciding correct versus wrong speculation.

The machine allows arbitrary sequences of older operations and speculative stores, but only one *architectural* memory instruction per core may be outstanding, so it is intentionally strongly ordered and not an out-of-order retirement core.

## New state per core

- `qlen` in `{0,1,2}` is the number of queued speculative writes.
- `ready` in `[0, qlen]` is the number of **confirmed prefix** entries.
- Each slot has `address, value` with an address in the modeled cache-line range.

### New transitions

1. `stage_slot0` / `stage_slot1`: enqueue an arbitrary `(line, value)` pair if capacity allows. Speculative execution can overlap an older pending memory instruction.
2. `confirm`: mark the queued prefix as correct-path and eligible for commitment.
3. `squash_unconfirmed`: discard the unconfirmed suffix. The already confirmed prefix remains.
4. `retire_head`: **only if no older architectural instruction is outstanding and `ready>0`**, pass the oldest confirmed write to the original MSI frontend and remove it from the speculative queue. No shared-memory update occurs at this step. All later cache ownership and completed-store transitions are unchanged.

All old operations remain unchanged, except that the frontend cannot issue *new unrelated* architectural instructions while the speculative queue is nonempty. Old MSI message deliveries, recalls, invalidation acknowledgments and ongoing instruction completions remain enabled.

## What exactly was formally checked?

Let `I_old` be the strengthened invariant from the already SMT-verified MSI model. `Q` is the queue bound/confirmed-prefix invariant, and `Delta` the disjunction of the new transition relations.

We used Z3 to check the **UNSAT** of:

1. `Init_new & !Q`: queues are initially well-formed.
2. `I_old & Q & Delta & !Q'`: new transitions cannot break queue well-formedness.
3. `I_old & Q & Delta & !I_old'`: new transitions cannot break MSI's old safety invariant.
4. `I_old & Q & Delta & !LegalRetirement`: new transitions either **stutter** on the old coherent state or start exactly the store at the confirmed queue head, never a younger or unresolved one.

Existing transitions preserve `I_old` by the independently rerun baseline Z3 check. They preserve `Q` because they frame the new queue state and restrict frontend issue without relaxing old transitions. These checks imply an **unbounded-execution-length safety result for the fixed 4-core models**, including arbitrary contents and repeated values, conditional on the abstract old MSI model.

### Machine results

| Instance | Baseline MSI initial/inductive/safety | Queue init/preservation/refinement/old safety | Result |
|---|---|---|---|
| 4 cores, 2 cache lines, 2 spec stores/core | UNSAT / UNSAT / UNSAT | UNSAT / UNSAT / UNSAT / UNSAT | PASS |
| 4 cores, 3 cache lines, 2 spec stores/core | UNSAT / UNSAT / UNSAT | UNSAT / UNSAT / UNSAT / UNSAT | PASS |

The baseline safety invariant includes single-write ownership, modified-data handoff integrity, and latest-value consistency. The old architectural frontend completes stores, reads and CAS indivisibly in a global linearization sequence and permits at most one active instruction per core. This establishes sequential consistency **by a paper-level simulation/trace argument**; the trace-level SC theorem itself is not separately machine-checked. The new SMT proof establishes a FIFO, resolution-respecting refinement into that earlier frontend.

### Positive SAT witnesses (two cores, two lines)

- `good_two_speculative_stores.smt2`: stage X=11 and Y=22, confirm, commit in order; other core later reads 11 and then 22 through asynchronous MSI handoffs.
- `good_squash_no_memory_effect.smt2`: stage X=77, squash it, then another core reads the unchanged X=0.

### Deliberately broken variants

- `BUG_retire_tail_first`: issue younger confirmed Y=22 before older X=11. **SAT 25-step witness**: another core reads Y=22 and then X=0. This is forbidden by SC relative to the *program's* X-then-Y order, even though every individual cache line remains coherent.
- `BUG_retire_unresolved`: let unconfirmed X=77 reach shared memory. **SAT 16-step witness**: another core reads the value 77, which would be a wrong-path side effect if that speculative write is discarded.

SMT additionally gives SAT for the bad transitions in a single-step query against the legal FIFO-retirement relation. This matters: checking the *old MSI invariants alone* would miss the first bug, because MSI correctly serializes whatever writes it receives; the instruction-order obligation is separate.

## Why this is a useful proof-reuse demonstration

The new proof does not build a new global multi-cache memory invariant. The speculative queue is checked as an isolated delta:

- stage/confirm/squash correspond to **zero** old state-machine steps;
- a correct retirement corresponds to **one** previously permitted old frontend issue;
- message handling and eventual store completion rely on the unchanged original MSI proof;
- relative order of correct-path speculative stores is proved by the confirmed FIFO-head condition.

## Limitations and next steps

- Fixed 4 cores and 2 or 3 independent cache lines; **not a parameterized machine proof** for arbitrary cores or cache lines.
- `qlen<=2`; a FIFO abstraction could extend the same *simulation reasoning* to arbitrary finite queue length `B`, but that generalized theorem has **not been machine-checked**.
- No speculative writes becoming visible before they are resolved; such writes would require undo, versioning, or compensation and a different proof.
- No speculative CAS, speculative reads observing queued stores, forwarding, branch predictor, partial store merging, exceptions, interrupts, coherence prefetching or store-buffer reordering.
- Does not prove liveness or useful speedup. No RTL or physical implementation.

## Reproduction

With `libz3.so.4` present (the helper invokes its SMT-LIB interface via `ctypes`), run:

```bash
python sc_msi_4core_verifier.py --cores 4 --lines 2 --output-dir baseline_smt4
python speculative_store_delta.py --cores 4 --lines 2 --out-dir smt4
python speculative_store_delta.py --cores 4 --lines 3 --out-dir smt4_3lines
python mutant_checks.py
python witnesses.py
```

The generated `.smt2` queries can also be checked using a normal SMT-LIB-compatible Z3 executable. All results are saved as JSON.
