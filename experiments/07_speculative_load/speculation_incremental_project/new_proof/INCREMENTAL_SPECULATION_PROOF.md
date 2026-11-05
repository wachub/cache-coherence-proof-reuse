# Incremental speculative-load verification over the four-core MSI baseline

## Result and scope

This experiment adds **one speculative load slot per core** to the existing four-core, two-line MSI + strict architectural memory ordering transition system. The goal is to reuse the earlier proof rather than reconstruct the whole global SMT proof.

The checker (libZ3) returned **UNSAT** for the four new proof obligations for the 4-core x 2-line instance. A deliberately unsafe retirement transition gives a **SAT** counterexample (23 protocol/frontend steps). The corrected protocol **replays** on that same history, and a longer 31-step witness confirms that the read can complete with the newer value. A separate **SAT** witness shows the speculative fast path can retire successfully without interference.

This is not a proof of an actual speculative CPU, pipeline, or RTL implementation. This is a safety theorem for an explicit abstract extension of the earlier MSI model; liveness and performance are outside the result.

## Reused theorem

Let `B(s)` be the previous system state: four processors, two cache lines, asynchronous coherence messages, one outstanding **architectural** memory operation per core, atomic completion of read/store/CAS commands. The previous proof establishes:

```
Init_B(s) => Inv_B(s)
Inv_B(s) && T_B(s,s') => Inv_B(s')
Inv_B(s) => !Bad(s)
```

The important fact inherited from `Inv_B` is:

> If a core has a valid S/M cached copy for line `l`, the cached version equals the abstract latest committed version for `l`.

The previous artifact's `sc_msi_smt4/induction.smt2` and result file are included, not regenerated.

## Very small extension

For each core `c`, add:

- `spec_active[c]`: a speculative load is outstanding;
- `spec_addr[c]`: the target cache line;
- `spec_version[c]`: the version observed from a **valid L1 cache hit**.

The new speculative read may occur while an *older* architectural instruction is still incomplete. It changes **no architectural or shared-memory state** and records a version from an S/M cached line.

Once the older operation completes (`!busy[c]`):

1. **Retire fast** only if the line is still S/M, no coherence request for it is pending, and the current cached version matches `spec_version[c]`. The returned value is the payload of that version.
2. Otherwise, **replay**: discard the speculation and issue the ordinary read through the already verified MSI frontend.

While `spec_active[c]`, a new independent architectural command cannot issue ahead of it. Only one speculative slot is supported. All existing coherence transitions are unchanged.

Using unique **version tokens**, rather than comparing only data bytes, conservatively rejects an intervening write that changed A→B→A (ABA). Token generation is ghost/abstract machinery here; we do **not** yet prove a physical load-queue or version-checking RTL implementation.

## Incremental SMT proof obligation

Let `Delta` be the disjunction of **only the newly added** speculative-transition schemas, and `J` be well-formedness of the three speculative registers (bounded addresses, nonnegative version). Then the new proof is:

```
Inv_B(s) & J(s) & Delta(s,s') & !(Inv_B(s') & J(s'))
```

Z3 result: **UNSAT**.

Additionally, the checker asks whether an allowed speculative retirement could set the sticky read-correctness failure bit:

```
Inv_B(s) & J(s) & Delta_retire(s,s') & Bad(s')
```

Z3 result: **UNSAT**.

Why it is valid to omit the full old transition relation: old transitions preserve `Inv_B` by the previous SMT theorem. Our extension merely restricts some old issue transitions and otherwise leaves their projected updates unchanged; these old transitions preserve `J` because they frame all speculative registers. The new transitions are the only cases requiring new proof work. Thus an induction covering arbitrary execution length follows by cases over old and new transitions, within the fixed-core/line model.

The SMT-LIB artifacts for the delta proof are in `spec_delta_4/`.

## Concrete counterexample and repaired execution

Original `data` line version = 0, `payload[0] = 0`.

1. Core 0 caches data line 1 in S state, then starts an **older**, incomplete read of line 0.
2. Core 0 speculatively reads line 1 and holds version 0.
3. Core 1 requests M ownership of line 1. The directory invalidates Core 0's S copy and acknowledges the invalidation.
4. Core 1 completes a coherent write to line 1, version 1, `payload[1] = 99`.
5. Core 0's older line-0 read completes.
6. **Unsafe mutant:** Core 0 retires the old speculative value 0 without checking current line validity/version. The abstract reference is now version 1. SAT at 23 events, and `Bad=true`.
7. **Corrected design:** Step 6 instead triggers replay, which eventually reads 99 via the original MSI protocol. SAT at 31 events, and `Bad=false`.

There is also a 15-event valid path in which no intervening write occurs and the early read is safely retired without replay.

## Results from libZ3

| Obligation | 2 cores, 2 lines | 4 cores, 2 lines |
|---|---|---|
| Extended initial state implies invariant | UNSAT | UNSAT |
| Old invariant + J preserved by every new transition | UNSAT | UNSAT |
| Safety under invariant | UNSAT | UNSAT |
| Bad speculative retirement possible? | UNSAT | UNSAT |
| Unsafe missing-validation execution | — | SAT (23 events) |
| Safe replay of that execution | — | SAT (23 events) |
| Safe replay completing with value 99 | — | SAT (31 events) |
| Fast speculative retirement | — | SAT (15 events) |

UNSAT means the negation of the required claim is unsatisfiable. It does not mean the underlying transition system is inactive: the SAT witnesses establish actual operations and both useful retirement paths.

## What is and is not established

**Established for this abstract 4-core, 2-line model:** Any number of protocol steps, arbitrary existing memory operation streams and stored data values; old MSI safety and SC for committed operations are preserved when at most one younger load per core is speculated and validated/replayed as specified. Early read results are never architecturally committed ahead of older operations. No load can retire a stale version after invalidation/write if validation is used.

**Not established:** unbounded number of processors/lines, multiple speculative loads per core, speculative stores or CAS, branch prediction, pipeline/retirement queues, realistic reorder buffers, implementation of version tracking, corner cases from memory-mapped I/O or exceptions, genuine RTL refinement, progress, power/performance benefit, or any relaxed-ISA memory model.

A critical dependency is that the MSI baseline *already* establishes correctness of coherent reads and writes. We do not infer physical correctness from this abstract proof.

## Reproduce

From a directory with `cache_smt_verifier.py`, `sc_msi_4core_verifier.py`, `sc_msi_trace_witness.py`:

```bash
python speculative_load_delta_proof.py --cores 4 --lines 2 --output-dir spec_delta_4
python speculative_delta_witness.py
```

The SMT files require Z3. This environment uses `libz3.so.4` through the original project's Python `ctypes` adapter.
