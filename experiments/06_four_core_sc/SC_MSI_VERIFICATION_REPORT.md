# Four-core MSI with strict memory ordering — SMT-checked safety proof

**Status:** proof obligations discharged by libZ3 (UNSAT).  This is a mathematical proof of safety for the **specified finite-core abstract transition system**, *not* of real RTL, an x86/ARM implementation, or liveness.

## Scope and objective

We retained the earlier asynchronous, directory-based, single-line MSI model (`cache_smt_verifier.py`) and instantiated it independently for **two or three cache lines, with four cores**. A front-end now issues arbitrary streams of `Read(line)`, `Store(line,value)`, and `CAS(line, expected, new_value)` requests. Each core can have **at most one outstanding memory operation** and cannot begin the next one until the current operation completes. The front-end and caches are modeled together, but each cache line has its own independent directory transaction state.

Each core has a cache state I/S/M per line. Each directory has one active transaction per line, but accepts multiple queued requests. The asynchronous protocol includes request, recall, invalidate, acknowledge, dirty writeback, grant, and grant-ack events; message deliveries can be arbitrarily interleaved. Cores can perform local operations in M without asking the directory for each write. CAS is performed only with exclusive M permission. Data versions may be unbounded.

**No store buffers, speculative memory operations, write combining, or instruction-level reordering are modeled.** The strict ordering rule is implemented at the CPU interface by allowing just one outstanding request per core. This is intentional: the experiment checks the *strong baseline* before exploring optimizations.

## Why this is more general than a litmus test

There is **no fixed program** in the SMT encoding. Every idle core nondeterministically chooses a line and one of the three commands; stores and CAS accept arbitrary integer operands. This can continue for an unbounded number of protocol steps and completed memory operations. It is still limited to a fixed set of four processors and two (or three) cache lines.

The original coherence model stores strictly increasing **write-version tokens** to reason about freshness. For the new frontend, each line has an immutable symbolic SMT array `payload_l : Int -> Int`, assigning arbitrary integer data to each write version. Two different versions may have the same data (ABA is representable). At issuance, a store/CAS chooses a new value, and successful writing is allowed only when the next write version maps to that value. For every finite execution, an arbitrary sequence of written values can be represented by assigning the fresh version tokens accordingly. This is a symbolic proof abstraction, not a design for how real caches store bytes.

## Strongest proved statement

For any legal run of the transition system, take the **completion/commit steps** of its memory operations in global transition order. This creates a total order which:

1. respects each core's program order (only one memory instruction can be outstanding per core);
2. returns the latest previously committed value at a read;
3. makes a store change its target line in that order;
4. makes CAS return the preceding value and perform its conditional update as a single step.

Consequently, **the observable completed-memory-operation trace is sequentially consistent** for this model. Internal coherence requests, invalidations, and grants are invisible/stuttering steps of the abstract memory. Overlap between different cores' requests is permitted. A matching properly implemented lock acquire/release program on this interface inherits the usual sequential-consistency visibility property across cache lines.

The global total order is an **argument from the proved data/ownership invariants and the frontend structure**, rather than a separate end-to-end SMT trace-inclusion query. In particular, we do not claim a complete machine-checked refinement certificate for arbitrary RTL traces.

## The SMT proof obligations

Let `I(s)` be the initial state, `T(s,s')` the complete two-/three-line MSI plus CPU transition system, and `Inv` the conjunction of:

- the proved single-line MSI invariant from the original model for each line;
- `ref_l = latest_l` for each line, where `ref_l` is the abstract sequential memory's write version;
- read/CAS observations never disagree with the abstract reference at their completion step (a sticky `bad` flag remains false);
- each pending coherence request belongs to the issuing core's one outstanding operation;
- well-formed frontend control state.

The checker asks Z3 to prove:

```
I(s) => Inv(s)                         // init.smt2
Inv(s) & T(s,s') => Inv(s')            // induction.smt2
Inv(s) => not bad(s)                   // safety.smt2
```

All three are **UNSAT** in their negated-counterexample form, establishing the invariant by induction for arbitrarily many protocol transitions and unbounded write versions, for the chosen fixed processor/line counts.

A write is physically represented by permission-held cache data plus a possibly stale directory RAM copy; `ref` is a *verification ghost* and does not grant coherence permissions. The read/CAS observation uses the cache version, and the proof forces that version to equal the abstract memory version when it is served.

## Solver outcomes

| Fixed configuration | Initial bad? | Induction counterexample? | Safety counterexample? | Result |
|---|---|---|---|---|
| 2 cores × 2 lines | UNSAT | UNSAT | UNSAT | PASS |
| **4 cores × 2 lines** | **UNSAT** | **UNSAT** | **UNSAT** | **PASS** |
| 4 cores × 3 lines | UNSAT | UNSAT | UNSAT | PASS |

The four-core two-line system has 88 asynchronous protocol actions (44 per line) and 64 frontend actions, representing distinct transition *schemas*, not a count of reachable states.

### Non-vacuity checks

Additional satisfiable SMT traces independently confirm real activity is possible:

- **15-transition dirty handoff:** Core 0 writes value 42; the protocol recalls its modified line and writes it back; Core 1 subsequently reads 42. SAT.
- **15-transition competing CAS:** Two cores both attempt `CAS(x,0,new)`; Core 0 succeeds with new value 42 and Core 1 later fails, returning 42. SAT.

These witnesses are included as separate SMT-LIB queries, with the explicit transition sequence and concrete final observations.

### Ordering-violation witness

A separate four-event symbolic litmus checker demonstrates that **per-line coherence alone cannot replace per-core ordering**. Writer issues `W(data,42); W(flag,1)`; reader executes `R(flag)->1; R(data)->0`. If the writer's program-order completion constraint `W(data) < W(flag)` is retained, the required inequalities are UNSAT. If the constraint is dropped, the stale-read outcome is SAT. This is a **small abstract counterexample to the missing ordering discipline**, *not* a counterexample running the verified MSI/frontend transition system, which enforces in-order operation completion.

## What is and is not guaranteed

**Within the model:** exclusive M ownership; no simultaneous M and S copies; freshness of valid cached copies; dirty writeback preservation; asynchronous handoff safety; atomic CAS behavior on whole-line integer values; per-core ordered memory-instruction completion; and SC of *completed operations*, even across multiple lines. Four cores and two/three lines were checked.

**Not proved:** any progress or eventual completion (the environment can indefinitely delay messages); arbitrary number of cores in one parameterized proof; real buffer capacity, timeouts, interrupts, cache replacement/associativity or sharing at sub-line granularity; out-of-order CPUs; release/acquire/TSO/ARM-specific weak memory semantics; stores in a real store buffer; physical chip timing; RTL refinement; cross-clock-domain behavior; reset protocols; arbitration fairness; or any performance property.

The protocol **serializes directory transactions per line** and enforces one outstanding CPU memory operation per core. Those are strong simplifications and can reduce throughput. They are part of the verified design rather than facts established about real hardware.

## Reproduction

A local `libz3.so.4` is required, because `cache_smt_verifier.py` uses ctypes to call Z3 directly. No `z3` Python package is necessary. Place the three Python files in one directory, then run:

```bash
python sc_msi_4core_verifier.py --cores 4 --lines 2 --output-dir ./proof4_2
python sc_msi_4core_verifier.py --cores 4 --lines 3 --output-dir ./proof4_3
python sc_msi_trace_witness.py
python sc_msi_ordering_mutant.py
```

The witness/mutant scripts default to `/mnt/data/sc_msi_smt4`; if reproducing outside this environment, call their `witness('./proof4_2')` or `check('./proof4_2')` functions from Python, or adjust their default directories.

`proof4_2/induction.smt2` is a standalone solver query. An independent Z3 executable can check it using `z3 -smt2 induction.smt2` and should return `unsat`.

## Best next extension

Add a **finite, explicit store buffer** while retaining per-core issue order at the architectural interface; permit the stores to become coherent out of issue order and automatically discover the fences or drain constraints necessary for SC. This creates a nontrivial optimization and proof-repair problem, rather than assuming the ordering mechanism is already correct.
