# SMT-backed safety proof of an asynchronous directory-based cache protocol

**Scope and status.** A hand-authored, asynchronous, *single-cache-line* MSI-like directory protocol, with one active directory transaction per line and any number of queued requests. Z3 checked three standard induction proof obligations for 2, 3, 4, 6, 8, 12, and 16 cache controllers. Every reported query returned `unsat`. This proves safety for **arbitrary execution length** and **arbitrarily many local write versions** in each of these fixed-size mathematical models. It does **not** prove an arbitrary number of caches (the solver sees a fixed-size instance per run), real RTL, a CPU instruction set, or multi-location release/acquire memory consistency.

## 1. Precisely specified state

For every cache `c`: `mode[c]` in `{I,S,M}`, `val[c]`, `pending[c]`, and `share[c]`. The latter is the directory's bookkeeping bit, not the same thing as the cache's actual permission. There are distinct Boolean in-flight messages per cache: `rqR`, `rqW`, `inv`, `recall`, `ack`, `wb`, `grS`, `grM`, `gack`, plus payload versions on `wb` and grants.

The directory holds `mem`, `owner`, a current transaction `tx` (or `-1`), `kind`, `phase`, and independent victim `wait[c]` flags. A ghost variable `latest` records the version of the most recent authorized write. The ghost exists **only in the verification specification**, not in a hardware design.

Allowed atomic transition categories (interleaved in any order):

1. Cache emits a read or write request (maximum one pending request *per cache*).
2. Modified cache writes locally, advancing `latest` and its own cached version; it does not contact the directory for each write.
3. An idle directory selects one queued request, issues recalls/invalidations to current conflicting holders, and marks those holders in its wait set.
4. An invalidated sharer relinquishes the line **before** acknowledging. A recalled modified owner relinquishes it **before** sending its dirty version in a writeback message.
5. The directory receives acknowledgments and dirty values; it cannot grant permission while a victim remains in its wait set.
6. After all required acknowledgments, it sends a grant containing the latest memory version. A separate grant acknowledgment prevents a later directory transaction from overtaking a grant still in flight.

Requests can queue and message delivery is unconstrained in timing. A transaction is serialized **per line**, not globally. This is a deliberate, performance-relevant abstraction: different lines could proceed independently, although they are not jointly modeled here.

## 2. The SAT/SMT queries

Let `Init(s)` describe the zeroed caches, `T(s,s')` be the disjunction of all legal guarded protocol transitions, and `Inv(s)` be the strengthened inductive invariant described below. The checker asks Z3 to solve these three formulas:

```
Init(s) AND NOT Inv(s)
Inv(s) AND T(s,s') AND NOT Inv(s')
Inv(s) AND Bad(s)
```

Z3 returns **UNSAT** for all three. Consequently, standard induction proves `Inv` at every reachable point, and `Bad` can never hold, even if execution is arbitrarily long. This is **not** a bounded-depth claim and does not require exploring an exponential list of reachable states.

The invariant includes protocol *control-state* facts, not just desired correctness properties: whenever a directory is waiting for a victim, the associated invalidation/recall/acknowledgment/writeback is actually in flight; pending requests cannot coexist illegally with pending grants; in-flight grant payloads match the current directory value; idle directories cannot have unfinished grant messages; and write ownership cannot be duplicated. Such strengthening was necessary: early attempts to prove just the simple safety property produced spurious **one-step** counterexamples from unreachable, inconsistent protocol states.

## 3. Verified properties

- **SWMR permission exclusion:** At most one cache can hold `M`; no other cache can hold a usable `S` copy when an `M` cache exists.
- **Correct read-source data:** Every cache that is permitted to serve a read (`S` or `M`) holds the ghost `latest` version.
- **Dirty-value preservation:** If there is no exclusive owner, directory `mem` is current. If directory `mem` is stale, the newest version is still held by the owner cache or in a dirty writeback message.
- **Safe permission handoff:** Invalidation and recall responses retire old permissions before the directory grants conflicting ones. An in-flight grant remains protected until acknowledgment.
- **An abstract single-location memory refinement argument:** A local write from the unique `M` owner can be taken as the abstract write's linearization point; every permitted hit-read returns that version. The SMT proof checks the required invariants; a separate formal trace-refinement checker and explicit read-return-state transitions are not implemented.

These are **safety properties only**. If the network never delivers an outstanding message, a requester might wait forever; fairness and liveness have not been verified.

## 4. Results of actual solver execution

| Caches | Steps | Write versions | Init query | Inductive step | Safety implication |
|---:|---|---|---|---|---|
| 2 | Unbounded | Unbounded | UNSAT | UNSAT | UNSAT |
| 3 | Unbounded | Unbounded | UNSAT | UNSAT | UNSAT |
| 4 | Unbounded | Unbounded | UNSAT | UNSAT | UNSAT |
| 6 | Unbounded | Unbounded | UNSAT | UNSAT | UNSAT |
| 8 | Unbounded | Unbounded | UNSAT | UNSAT | UNSAT |
| 12 | Unbounded | Unbounded | UNSAT | UNSAT | UNSAT |
| 16 | Unbounded | Unbounded | UNSAT | UNSAT | UNSAT |

`--unbounded-versions` uses nonnegative mathematical integers for versions and removes the per-version upper bound. Actual hardware values have finite width; verifying their word-level arithmetic would be a separate refinement task. `cache_smt_verifier.py` creates reproducible SMT-LIB2 files. `induction_4core.smt2` is a standalone example of the crucial, unbounded-depth proof obligation.

**Non-vacuity checks:** The correct protocol has a SAT execution where Core 0 modifies a line, the directory recalls its dirty version, and Core 1 eventually gets Modified permission containing the correct value (`cache_positive_transfer.smt2`).

## 5. Real counterexample from a broken protocol

In the mutant, the directory may issue an exclusive grant *before* all victim acknowledgments arrive. With only two caches, bounded SMT checking finds a counterexample to the ownership bookkeeping property at **depth 8**, and to the more concrete property *two caches simultaneously in Modified state* at **depth 9**.

A nine-step counterexample is:

1. Core 1 issues a write request.
2. Core 0 issues a write request.
3. Directory starts Core 1's transaction.
4. Directory grants Modified permission to Core 1.
5. Core 1 receives the grant and enters Modified.
6. Directory receives its grant acknowledgment.
7. Directory starts Core 0's transaction and sends a recall to Core 1.
8. **BUG:** Directory grants Modified permission to Core 0 before receiving Core 1's recall/writeback.
9. Core 0 receives its grant, so **both cores are Modified**.

The finite counterexample is independent evidence that the logical guard being verified does real work. The model checker did not merely establish an invariant by suppressing all useful transitions.

## 6. What this does *not* establish

1. **Not parameterized in the number of caches.** Instances from two to sixteen controllers have individually been proved by SMT induction. A theorem quantified over arbitrary `n` would be a stronger next result.
2. **Not a production MSI/MESI implementation.** It excludes evictions, physical wire arbitration, finite buffer capacities, retry/NACK logic, directory races outside the serialized per-line transaction, dropped/duplicated messages, non-coherent DMA, sub-line bytes, and the physical data path. Messages are eventually *enabled* but not necessarily delivered.
3. **Not memory-model or ISA verification.** Store buffers, speculative loads, release/acquire ordering across **different cache lines**, operating system migration, and instruction semantics are not present in this SMT proof. Abstract CAS operations could use exclusive write permission, but concrete CAS linearization and cross-line synchronization need additional proof obligations.
4. **Not a proof of the Python verifier itself.** We trust the SMT generator to encode the described protocol and trust Z3 to solve its generated obligations. The generated standalone SMT-LIB files help independent review of the encoding.
5. **Not arbitrary data writes.** Data are represented by monotonic logical **write versions**, a common ghost-data abstraction. The proof checks that no cache serves an obsolete version; verifying bitwise data integrity in an RTL pipeline is additional work.

## 7. Reproduction

On Linux with `libz3.so.4` installed (the solver API is used through Python `ctypes`, so the `z3-solver` Python package is not required):

```bash
python cache_smt_verifier.py --cores 4 --unbounded-versions --output-dir .
python cache_smt_verifier.py --cores 16 --unbounded-versions --output-dir .
python cache_smt_verifier.py --cores 2 --early-grant --output-dir .
python cache_bmc.py --double-writer --limit 9 --outfile witness.smt2
pytest -q test_cache_smt_verifier.py
```

Alternatively, the supplied `induction_4core.smt2` can be opened in a standalone SMT-LIB2-capable Z3 installation. Its expected result is `unsat`.

## 8. The next nontrivial step

A useful next milestone is a **two-line release/acquire model with explicit FIFO or non-FIFO store buffers**, rather than assuming stores are issued in the correct program order. We want to check both the desired message-passing guarantee and a counterexample when the release ordering constraint is removed. Only then would the per-line coherence proof connect to the cross-line synchronization concern that motivated this discussion.
