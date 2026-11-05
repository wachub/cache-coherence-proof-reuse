# A Small, Reproducible Cache-Protocol Verification Experiment

**Date:** 2026-11-05  
**Status:** Explicit-state model checking completed for bounded instances. General correctness is supported by the proof argument below, but **not machine-proved for unbounded numbers of cores or lines**.

## 1. The leverage: transient permissions and ghost versions

Instead of constructing an enormous global history of all cache-line interactions, maintain a small *permission ledger* per cache line. The directory stores `owner`, `sharers`, `mem`, and one pending transaction. Individual caches have `I`, `S`, or `M` state plus a value. Every request, invalidation, recall, acknowledgment, grant, and grant acknowledgment is represented as an **independent, arbitrarily reorderable asynchronous message**. Local writes in state `M` do not contact the directory.

For verification only, attach a ghost integer `latest` to each line. It increments whenever a permitted local modified-cache write executes. This is not part of a proposed hardware implementation; it represents the abstract memory specification and lets us check every reachable state against the current logical value.

A write permission can be in a transient stage while a grant or writeback is in flight; therefore a naive invariant such as "directory.owner == current modified cache" *in both directions* is incorrect. The directory can reserve ownership for an in-flight grant, or retain the old owner while its dirty writeback is still in flight.

## 2. Protocol transitions

For each line independently:

1. A cache in `I` may request shared or modified access. A cache in `S` may request an upgrade. One request per cache per line may be outstanding.
2. The directory processes requests one at a time, but multiple requests can be queued and their messages delivered in any order.
3. Before granting exclusive access, the directory sends invalidations to the other sharers and/or recalls the current modified owner. For shared access, it recalls the existing modified owner if any.
4. A cache processes the invalidation/recall and relinquishes rights before sending an acknowledgment. A dirty owner returns its current data value with the acknowledgment.
5. **Only after all relevant acknowledgments have been processed** does the directory issue a grant. The line remains transaction-busy until a grant acknowledgment arrives, guarding in-flight grants against interference.
6. A cache with `M` permission can write locally without asking the directory. A cache in `S` or `M` can read locally.
7. The protocol makes no spontaneous voluntary eviction, does not duplicate or lose messages, and does not bound message latency. Network delivery can be arbitrarily reordered; fairness is not assumed.

## 3. Safety contract

For each cache line `l`, `latest[l]` denotes the current abstract value/version. The properties checked after **every reachable transition** are:

**P1 — Permission exclusion.** No two caches simultaneously hold `M`; no cache can hold `S` while some other cache holds `M`. The directory may reserve an in-flight grant or outstanding writeback, so permission bookkeeping must explicitly allow such transient states.

**P2 — Read freshness.** Every readable cache (state `S` or `M`) holds `latest[l]`. Hence any actual read from an enabled readable cache returns the abstract current value.

**P3 — Dirty-value preservation.** If there is no exclusive owner, the directory memory equals `latest[l]`. While modified permission is held or transferred, the newest value is either in the modified owner, in a dirty writeback message, or already in directory memory; it is not discarded by transfer.

**P4 — Grant safety.** A transaction cannot grant new rights until the invalidation/recall acknowledgment mask is empty. The grant-acknowledgment phase prevents another transaction from overtaking an in-flight grant.

**P5 — CAS uniqueness.** In a separate two-thread CAS test with one shared address initially zero, exactly one strong `CAS(x,0,new)` operation succeeds when both complete. A CAS executes while the cache possesses the sole exclusive permission; its comparison and update form one indivisible modeled transition.

**P6 — Two-location publication.** A writer first stores `data=1`, then executes `CAS_release(flag,0,1)`. A reader may cache the old data, then observe `flag=1` using an acquire load and subsequently reread data. No other thread changes the data. We require the final read to return `1`. At each instruction boundary either thread may resume on any physical core; cores retain their own cache states. The proof of this case relies on preserving these program-order/release-acquire constraints in the microarchitecture.

## 4. Verified bounded instances

| Check | States | Transitions | Result |
|---|---:|---:|---|
| 2 cores, one line, up to 2 writes | 549 | 990 | PASS |
| 3 cores, one line, up to 2 writes | 10,194 | 25,689 | PASS |
| 4 cores, one line, up to 2 writes | 159,897 | 523,956 | PASS |
| 2 cores, two lines, data/flag publication, arbitrary instruction-boundary core migration | 43,135 | 126,582 | PASS |
| 2 cores, concurrent CAS race | 178 | 288 | PASS |
| 3 cores, concurrent CAS race | 1,412 | 2,676 | PASS |

All reachable distinct states were enumerated for the listed finite instances (no state cap reached). `PASS` means the safety checks held for every explored state under the transition system implemented in the accompanying Python source.

## 5. Deliberately broken protocols

These variants help show that the properties are not vacuous.

| Fault deliberately introduced | First failure | Counterexample |
|---|---:|---|
| Grant modified ownership before prior sharers' invalidation acknowledgments | 140 discovered states | Directory reserves new modified ownership while another cache remains a valid sharer |
| Drop dirty value and incorrectly write back zero | 183 discovered states | Owner writes a new version; recall delivers it; directory ignores it and becomes stale |
| Publish the flag before writing ordinary data | 2,567 discovered states | Reader observes `flag=1` and then reads `data=0` |

Complete counterexample traces are in `verification_results.json`.

## 6. Why the proof structure can scale

The intended induction has a **fixed set of transition categories**, rather than a separate case for every global arrangement of all cores:

- **Issue request:** Creates no new permission, so exclusion and freshness remain true.
- **Begin transaction:** Sends recalls/invalidations and records all current competing permission holders in a waiting set. Grants are blocked.
- **Receive recall/invalidation at cache:** Removes the old permission before acknowledging; the dirty data version is carried in the message.
- **Receive acknowledgment at directory:** Removes a previously retired permission and installs the dirty returned value when present.
- **Send grant:** Allowed only after the wait set is empty; blocks new transactions until grant acknowledgment. There cannot be an old active conflicting holder.
- **Receive grant:** Converts a reserved, in-flight permission into an active cache permission, carrying the current data version.
- **Local write:** Only the unique `M` cache changes the value; the ghost latest version advances with it. No other cache has read permission for that line.

Induction over these categories suggests a parameterized proof of single-line read freshness and single-writer safety for any finite number of cores, with the important caveat that a **machine-checked quantified inductive proof has not been supplied**. Exhaustive model checking at 2/3/4 cores provides additional evidence, not a proof of this universal claim.

**Cross-line leverage:** Once each line has the same proven contract, different lines may run their directory protocols independently. The publication theorem adds one small cross-line ordering contract: data writes must occur before a release flag publication, and the acquiring read must happen before subsequent data reads. There need not be an eager broadcast or copy of every modified line to every cache at the synchronization point. Independent lines can be fetched or transferred as needed.

The per-line argument does not automatically prove the cross-line contract on an out-of-order processor. Store buffers, speculative loads, fences, and compiler reorderings must be modeled in a later layer.

## 7. What this does NOT verify

- Not full MSI/MESI or any commercial cache-controller RTL.
- Not realistic network protocols, bounded queues, retry races, message duplication/loss, dirty evictions, concurrent multiple owners of sub-line data, DMA/I/O, or byte tearing.
- Not a complete C++ or ARM/x86 memory model. The publication experiment assumes source-program ordering is implemented with correct release/acquire semantics; store buffers and speculative load retirement are not modeled.
- No liveness guarantee, forward progress, or starvation freedom: messages can be delayed forever.
- No proven parameterized result for arbitrary numbers of cores, lines, addresses, versions, or threads.
- The Python checker is a small custom verification program, not a formally verified model checker. Its implementation and the abstraction themselves could contain bugs. The intentionally broken variants and separate tests provide some assurance, not absolute assurance.

## 8. Reproduction

Requires Python 3.10+; uses only the standard library for the checker. `pytest` is optional for running the six tests.

```bash
python cache_protocol_verifier.py --check coherence --cores 4 --max-writes 2
python cache_protocol_verifier.py --check publication --cores 2
python cache_protocol_verifier.py --check cas --cores 3
python cache_protocol_verifier.py --check coherence --cores 2 --mutant
python cache_protocol_verifier.py --check coherence --cores 2 --drop-writeback
python cache_protocol_verifier.py --check publication --cores 2 --mutant
pytest -q test_cache_protocol_verifier.py
```

## 9. Most valuable next refinement

Introduce per-core store buffers, and represent release/acquire as explicit permission-to-publish and permission-to-consume conditions. Check the classic message-passing litmus test both with and without barriers, without baking the ordering guarantee into the program scheduler. This tests the main **remaining cross-layer interface**. Then move to a known MSI/MESI RTL or public protocol specification, preserving the same permission ledger and ghost-version properties as an independent reference monitor.

## Related work

- *Towards Composable Proofs of Cache Coherence Protocols* (CPP 2026), https://doi.org/10.1145/3779031.3779106 — related but more substantial machine-checked proof decomposition.
- Linux kernel memory-model recipes, https://code.googlesource.com/linux/torvalds/linux/+/dfc53baae3c6a165a35735b789e3e083786271d6/tools/memory-model/Documentation/recipes.txt — canonical release/acquire message-passing litmus test.
