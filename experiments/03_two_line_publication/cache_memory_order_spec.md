# Cache-coherence specification extended with release/acquire memory ordering

**Status:** Executable SMT-based two-core/two-line verification experiment (5 November 2026). This modifies the original `cache_smt_verifier.py` rather than replacing its per-cache-line protocol. See `cache_memory_order_extension.py` for the executable model and `memory_order_results.json` for solver results.

## 1. Base protocol, unchanged

For each cache line `a`, instantiate a separate copy of the **original asynchronous directory MSI-style state machine** `Line(a)`:

- per-core cache state `I/S/M`, value version, and outstanding request flags;
- one directory with `owner`, sharer flags, current transaction and pending invalidation/recall wait set;
- messages `rqR`, `rqW`, `inv`, `recall`, `ack`, `wb`, `grS`, `grM`, and `gack`;
- locally performed writes permitted only in `M`, with exclusive write permission;
- dirty-data transfer through writeback messages before a conflicting grant;
- arbitrarily delayed/interleaved message steps.

The original per-line inductive safety invariant `I_line(a)` proves that a valid cached copy is current in the *per-location write order* and Modified ownership cannot be duplicated. The original model is a **single cache-line abstraction**: values are logical write versions rather than physical bytes.

The multi-line state is the asynchronous product:

`CacheState = Product_{a in Addresses} Line(a)`

No global directory serialization is added. A transition of one line leaves the others unchanged. The physically observable atomics and ordering at the processor interface are given below.

## 2. New processor-side interface and ordering rules

Each processor `p` has an ordered queue of **accepted stores** `SB[p]` (a finite store buffer). For the concrete checked program, the queue holds at most two stores, one to the data line and one to the publication flag line. The executable model encodes the queue by enqueue and drained flags plus guards; it does not model physical byte entries or cycle timing.

- `EnqStore(p,a,v)`: append the store to the processor's pending queue, preserving instruction program order.
- `DrainStore(p,a,v)`: remove the oldest eligible store and perform one original `Line(a)` local write, **only when p has Modified ownership of line a**. The store becomes globally ordered for that line at this point. The old per-line invalidation and writeback protocol supplies/recalls the required permissions.
- `ReleaseCAS(p,L,expected,new)`: atomic compare-and-swap on a flag line `L`, **when p has Modified ownership of L**. The CAS is permitted to publish only after all earlier ordinary stores of p in the release set have drained into their corresponding coherent lines. For this checked program `CAS(flag,0,1)` always succeeds once enabled, as no other writer modifies the flag.
- `AcquireLoad(q,L)`: an atomic read of the coherent `L` line by `q`; if it reads the value written by the corresponding release, the subsequent reads of q must honor the publication ordering.
- `Read(q,a)`: a read by q from a valid (`S` or `M`) line. If the cache is invalid, the processor must request it through the unchanged directory protocol. The machine checks the value returned after acquire.

These rules specify **one implementation of release/acquire** using coherent per-line memory and FIFO ordered visibility of preceding stores. They do not require writing back to DRAM or invalidating all lines when the flag is published. The implementation must not allow the release to become observable before earlier buffered stores have reached their per-line coherence points.

### General abstract contract (not fully proved by this finite test)

For a release `R` to an atomic object `L` and an acquire `A` reading from that release (or an appropriate release sequence), the system must provide:

`W(x)  --sequenced-before-->  R(L)  --synchronizes-with-->  A(L)  --sequenced-before-->  Read(x)`

and therefore `W(x) happens-before Read(x)` for any address x, regardless of which cache line it occupies. For data-race-free programs with no intervening applicable write, the read must not return an older value. A more complete model also needs other atomic orders, RMW failures, loads that can speculate, dependencies, ordinary conflicting writes, and the precise chosen ISA memory model.

## 3. Exact checked instance

Core 0 (writer):

```
EnqStore(data, 1)
EnqReleaseCAS(flag, 0, 1)
# The data and flag writes can drain only while holding Modified permission.
# Correct model: CAS(flag,0,1) is blocked until store(data,1) has drained.
```

Core 1 (reader):

```
# May already have a cached Shared copy of data with version 0.
while AcquireLoad(flag) != 1: ...
observed = Read(data)
assert observed == 1
```

`data` and `flag` are **two independent cache lines**. Each has two cache controllers and one directory, using the full original message-delivery transitions. Both lines' messages may interleave arbitrarily. Each line can be written once (version 0 -> 1), which makes a finite value domain. The proof is not bounded in execution steps.

### Additional inductive properties

With `doneD`, `doneF` representing stores that reached the coherent per-line write points, `seenF` the successful acquire observation, and `readD` a completed post-acquire data read:

1. `latest(data) = 1 <=> doneD`.
2. `latest(flag) = 1 <=> doneF`.
3. `doneF => doneD` (the required cross-line ordering invariant).
4. `seenF => doneF` (coherent reads of the flag see the actual write).
5. `readD => seenF` and `readD => read_value = 1`.
6. Each original per-line inductive invariant holds throughout the execution.

The fifth invariant is the desired publication guarantee in this model. It depends on the per-line data correctness of the original MSI state machine and the new release-order guard.

### Independent solver proof obligations

For the conjunction `Inv = I_line(data) AND I_line(flag) AND I_order` and transition relation `T`:

```
Init(s) AND NOT Inv(s)                        UNSAT
Inv(s) AND T(s,s') AND NOT Inv(s')             UNSAT
Inv(s) AND Bad(s)                             UNSAT
```

These results establish safety at arbitrary execution length for **the fixed two-core, two-line, one-write-per-line instance**. They are not a parameterized theorem for all numbers of cores, cache lines, instructions, or stores.

## 4. Deliberately weakened release

The mutant removes `doneD` from the guard for the flag's release CAS, but retains all original MSI transitions. The checker finds:

- `Inv AND T_mutant AND NOT I_order'` is SAT, identifying a proof-breaking transition.
- A genuine reachable **22-transition** execution ends in `AcquireLoad(flag)==1` followed by `Read(data)==0`: Core 1 first caches version 0 of data, Core 0 acquires and modifies the flag before draining data, and Core 1 obtains the flag from the original directory while its stale Shared data cache line remains valid.

The **same 22-transition schedule is UNSAT in the correct model**, since the flag publication would be blocked until the data store was drained. A separate **37-transition SAT witness** demonstrates a complete, valid execution of the correct protocol in which the receiver acquires the flag and successfully reads the published value, so the safety result is not vacuous.

## 5. Reproduce

Linux with `libz3.so.4` (no Python `z3-solver` package necessary):

```
python cache_memory_order_extension.py --output-dir out
```

The included script imports `Protocol` from the **original** `cache_smt_verifier.py`. It generates standalone SMT-LIB2 files containing complete query encodings and a machine-readable JSON summary.

Expected: all four correct-model proof queries are UNSAT; the mutant's cross-line induction query is SAT; the 22-step mutant trace is SAT; and the same trace in the correct model is UNSAT; a 37-step correct-publication trace is SAT.

## 6. Limits and next step

- **Not yet full memory consistency.** This is a release/acquire publication litmus with one writer and one acquiring reader. It proves neither a general weak ISA model nor sequential consistency.
- **Not yet arbitrary addresses, processors, or unbounded pending stores.** The general contract above is the intended extension, not a completed parameterized proof.
- **No speculation, load queues, cycle accuracy, memory barriers for all instruction types, shared-store-buffer interactions, or concrete thread preemption.**
- **No eviction, reset, arbitration fairness, or deadlock-freedom proof.** The original per-line model is an abstract protocol and is not an RTL implementation.
- **Release ordering is enforced by a guard** rather than derived from a hardware store-buffer datapath. The next useful verification challenge is to introduce explicit buffer slots and arbitration and prove they refine this ordering adapter, including progress under fairness.

The important gain is modularity: the original per-line MSI correctness argument is reused unchanged, while the new cross-line proof has a much smaller program-order and synchronization interface.
