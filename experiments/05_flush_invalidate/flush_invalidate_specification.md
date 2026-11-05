# Flush-on-Release / Invalidate-on-Acquire: a deliberately simple cache-memory protocol

## Goal
Provide a simple, correct-by-design *lock-based* memory system that admits private, independently stale cache copies but gives sequential semantics to accesses protected by **one global mutex**. This is a teaching/baseline protocol, not a new coherence invention and not a full contemporary ISA memory model.

## State
- `L`: a single lock word, initially `unlocked`, operated on at an atomic lock home/arbiter.
- `M[a]`: backing memory's current committed value for each shared address `a`.
- `C[p,a]`: cached value at core `p`, or invalid.
- `D[p,a]`: whether that cached value is modified but not yet committed.
- `mode`: active critical section or flushing, with the owner recorded in `L`.
- `G[a]` (verification-only ghost state): the latest write in the abstract sequential execution of critical sections.

Shared data may only be accessed by the lock owner. Nonowners may retain old clean data but may not use it until they acquire the lock and invalidate. Private thread variables are outside this model. Core migration and store buffers are not modeled in this version.

## Operational rules
1. **Acquire**: a serialized successful `CAS(L, unlocked, p)` grants the mutex to core `p`. Before issuing any protected read/write, `p` invalidates all *its own* shared-data cache lines. The lock's own cache line is handled by the serialized lock mechanism and excluded from wholesale invalidation.
2. **Read**: while active, `p` returns `C[p,a]` on a valid hit; otherwise loads `M[a]` into `C[p,a]` and returns it.
3. **Write**: while active, `p` sets `C[p,a] := v` and `D[p,a] := true`. No other cache needs invalidation yet.
4. **Start release**: stop issuing new protected reads/writes, and finish any previously issued ones.
5. **Drain**: for every `a` with `D[p,a]`, complete `M[a] := C[p,a]` and clear `D[p,a]`, with acknowledgments of completion. These may take multiple independent transitions. If realistic store buffers are added, they must drain before the corresponding dirty data are deemed published.
6. **Unlock**: only after all dirty lines have been committed, atomically set `L := unlocked` with release semantics. A different core can now acquire.

Acquirer self-invalidation is important: old clean lines can remain in other cores for years without damaging correctly synchronized executions, but no core can reuse one without reacquiring and invalidating.

## Safety theorem / proof sketch (general N cores and A addresses)
Subject to all protected data operations being serialized by the **same global lock**, atomic home operations, reliable acknowledged writebacks, and completion of invalidation before reads: the sequence of critical sections implements sequential memory semantics for the shared addresses, independent of N and A.

Induction over completed critical sections:
- Before the first acquire, backing memory `M` is the initialized abstract memory.
- At the beginning of a critical section, previous owner has completely written its dirty set to `M` before unlocking. Acquire invalidates the new owner's stale cache. Every first read thereafter loads the corresponding `M[a]`; every subsequent read after a local write uses the updated local cache. Thus every protected read returns the abstract sequentially most recent write.
- During release, only the owner can read/write protected data, and no other owner can arise. The owner drains its final dirty values, producing `M` equal to the abstract memory after that section; it then unlocks.

This establishes safety for all sequences of well-formed, single-lock-protected critical sections **as a paper argument**. It has NOT been machine-checked for unbounded core/address counts.

## Executable finite-state verification
`flush_invalidate_protocol.py` explores all transitions, arbitrary lock-acquisition choices and protected read/write choices, all write values from the finite value domain, and all orders in which dirty lines are drained. It includes one specification ghost memory for sequential behavior and checks a strengthened inductive invariant for every reachable state.

Successful finite checks:
- 2 cores, 2 addresses, values {0,1}: 2,528 reachable states, 9,952 transitions.
- 3 cores, 2 addresses, values {0,1}: 33,520 reachable states, 135,552 transitions.
- 2 cores, 3 addresses, values {0,1}: 58,240 reachable states, 327,296 transitions.
- 2 cores, 2 addresses, values {0,1,2}: 15,408 reachable states, 76,608 transitions.

Mutant without acquire invalidation: model checker finds a violation, with a trace showing core 0 retaining a clean stale copy after core 1 has committed a newer value.

## Limitations
- This is a **global-mutex, race-free** design; no guarantees for unsynchronized competing data writes, independent locks, or arbitrary racy programs.
- An abstract serialized atomic lock home is an assumed lower-level primitive, not proved against RTL.
- Real L1/L2/L3 caching, TLBs, CPU store buffers, speculation, DMA, preemption, liveness/fairness and physical timing are omitted.
- The finite runs are exhaustive in a finite model, *not* an SMT/PDR theorem for arbitrary values, cache counts, or RTL.
- Progress is conditional on lock service and writebacks making progress. A malicious scheduler can starve any requester.
- In the published literature, self-invalidation on acquire and self-downgrade/writeback on release are well-established lazy release-consistency techniques. The baseline is intentionally not a novelty claim.

## Running
```
python flush_invalidate_protocol.py --cores 3 --addresses 2
python flush_invalidate_protocol.py --cores 2 --addresses 2 --broken
```
