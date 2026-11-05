# Verified FIFO-buffer extension of an asynchronous directory-MSI cache model

**Verification date:** 2026-11-05  
**Solver:** Z3 through `libz3.so.4`  
**Claim:** unbounded-execution-length *safety* proof of one concrete message-passing program, for **2 cores**, **3 independent cache lines** (`A`, `B`, flag `F`), a **2-entry FIFO store buffer**, and **one write to each line**. This is *not* a general weak-memory or RTL correctness theorem.

## Behavior

Writer core 0:

```text
store(A,10); store(B,20); release_CAS(F, expected=0, new=1)
```

Reader core 1:

```text
acquire_load(F) == 1; read(A); read(B)
```

The data values are represented in the SMT model by **logical versions** 0 and 1: `A=1` stands for the publication of `A=10`, etc. `A`, `B` and `F` are distinct cache lines. The reader can choose whether to read A or B first.

## What is newly implemented (relative to `cache_memory_order_extension.py`)

The previous model explicitly guarded the release by `done_D`. This new one introduces concrete logical store-buffer registers:

- `pc` = program position (`0..3`)
- `count` = buffered stores (`0..2`)
- `slot0`, `slot1` = FIFO contents (`0=empty`, `1=A`, `2=B`)
- enqueue operations for A and B
- **head-only drain** transitions, each performing the original asynchronous directory-MSI `c0:write` transition on the relevant line
- a release-CAS that updates the coherent flag line only when `count==0`
- an acquire load and completed reads at the observer core, guarded by having a valid S/M cache copy

**Unlike the previous model, release is not guarded by `latest(A)==1`, `latest(B)==1`, or ad-hoc per-line completion flags.** It is guarded only by the *hardware-like FIFO empty condition*. A strengthened inductive invariant connects buffer occupancy to which writes have actually drained. This is the essential small advance.

Each cache line independently instantiates the original `Protocol` model from `cache_smt_verifier.py`, retaining directory requests, grants, invalidations, acknowledgments, dirty writebacks, and asynchronous message delivery. All original `c1:write` and free `c0:write` transitions are removed; stores can modify coherent data only by draining the FIFO or performing the release-CAS.

## Proved safety property

In temporal notation, for any completed read after the acquiring load:

```
G( acquired(F=1) AND completed_read(A) => read_value(A)=1 )
G( acquired(F=1) AND completed_read(B) => read_value(B)=1 )
```

There are no other data writers in this checked program.

The inductive proof is based on the exact logical FIFO inventory:

| Writer `pc` | `count` | Meaning of latest(A),latest(B) |
|---:|---:|---|
| 0 | 0 | 0,0 |
| 1 | 1 | 0,0 (A pending) |
| 1 | 0 | 1,0 (A drained) |
| 2 or 3 | 2 | 0,0 (A and B pending) |
| 2 or 3 | 1 | 1,0 (only B pending) |
| 2 or 3 | 0 | 1,1 (both drained) |

Therefore `release_CAS` enabled only by `pc==3, count==0` entails that **both ordinary stores already entered their coherent lines**, *without needing to list those lines in the CAS guard*. The per-line MSI invariant ensures every valid cache copy contains the latest line version, including across asynchronous invalidation, ownership transfer, and writeback. The reader cannot acquire `F=1` until the flag CAS has executed.

For the full product system `Init`, `T`, and strengthened invariant `Inv`, Z3 checks:

```text
Init(s) AND NOT Inv(s)                     UNSAT
Inv(s) AND T(s,s') AND NOT Inv(s')          UNSAT
Inv(s) AND Bad(s)                          UNSAT
```

This proves the stated safety property at arbitrary transition depth, *for the fixed architecture and program*. It is not a depth-k bounded check.

## Checks performed

`results.json` records the exact solver outputs:

- `correct_init.smt2` → UNSAT
- `correct_step_buffer.smt2` → UNSAT
- `correct_step_full.smt2` → UNSAT
- `correct_safety.smt2` → UNSAT
- `correct_bad_trace.smt2` → UNSAT (the 23-step stale-read schedule is impossible)
- `correct_good_trace.smt2` → SAT (45-step successful publication)
- `correct_stale_copy_good_trace.smt2` → SAT (52-step successful publication with a reader that held a previously cached stale B; invalidation and subsequent recall are exercised)
- `mutant_step_buffer.smt2` → SAT
- `mutant_bad_trace.smt2` → SAT (23-step reachable violation)

The **mutant** removes only the `count==0` guard on the flag release. It keeps the FIFO and MSI rules unchanged. Consequently, the writer can publish F before either buffered store drains, while the reader sees F=1 and still reads an older B=0. This distinguishes the new ordering mechanism from coherence alone.

## Reproduce

Run from a directory containing both Python files:

```bash
python3 cache_memory_order_buffer_proof.py --output-dir ./proof_output
```

Requires Linux with the shared Z3 library (`libz3.so.4`), available on the verification machine. No `z3-solver` Python package is needed.

## Limits — important

- The model has **two cores and three lines**. It handles an unbounded number of **protocol transitions**, not unbounded numbers of stores, threads, or cache lines.
- It verifies a **single writer and single successful release/acquire synchronization**, without CAS contention or failed compare operations.
- The buffer holds only store address tags; the values are fixed abstract versions. It is a logical FIFO machine, not RTL or a gate-level datapath.
- The writer's store buffer is explicit; the reader does not have a load queue or speculative execution. The reader's acquire completes when it has a coherent valid copy of F=1.
- Multi-writer programs, other locks, nonmatching acquire/releases, general ISA consistency (TSO/ARM/C++), speculation, preemption, arbitrary line counts, liveness, fairness, and RTL refinement are **not proved**.
- The model assumes that writes draining from the FIFO are accepted into their coherence points. It does not model every physical timing and arbitration detail of a real store buffer.
- A Z3 inductive proof certifies correctness **of the written model and its trusted solver encoding**, not correctness of actual hardware.

**Next useful step:** model store/load queues for both cores and add two competing releases on different flags. Prove a small *transitive* release/acquire litmus without baking ordering directly into each test.
