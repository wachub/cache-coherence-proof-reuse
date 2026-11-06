# v2.1 — topology-independent abstract cache hierarchy

**Git branch:** `experiment/hierarchical-cache-width-v2.1` (branched from MESI/MOESI v2.0 `d5563b1`).

## Result and exact scope

This is a **new one-cache-line, atomic service-level abstraction**, implemented alongside—not in place of—the old asynchronous MESI/MOESI protocol. It provides a configurable hierarchy of coherent clean-data caches and directory summaries, with a stable CPU command/reply interface. **It does not yet replace the original v2.0 per-line protocol in the combined speculative frontend**, nor does it prove the old asynchronous message protocol correct when stacked in a hierarchy.

The central checked result is that **changing hierarchy depth or sibling fan-out does not change architectural memory results**, for the compared configurations and matched CPU operations, provided each hierarchy satisfies its invariant. New cores may be added without changing old-core behavior *if the added cores remain quiescent*.

A hierarchy is specified top-down by integer fan-outs:

| Fanouts | Shape | Leaves / cores | Directory nodes |
|---|---|---:|---:|
| `[4]` | shared directory -> 4 L1 cores | 4 | 1 |
| `[2,2]` | LLC -> 2 L2 domains -> 2 L1 cores each | 4 | 3 |
| `[4,2]` | LLC -> 4 L2 domains -> 2 L1 cores each | 8 | 5 |
| `[2,4]` | LLC -> 2 L2 domains -> 4 L1 cores each | 8 | 3 |
| `[2,2,2]` | LLC -> 2 mid-level nodes -> 2 L2 nodes each -> 2 L1 cores each | 8 | 7 |

The generator permits up to four internal directory levels and at most 32 leaves, but **tests and proof results below cover at most eight**. No universal correctness theorem for arbitrary numbers of cores or levels has been established.

## What the intermediate levels actually model

Each internal node holds real symbolic state for:

* `data_valid`, `data_ver`: a **clean** cache copy, if available; its version must equal `latest` and `mem` must be current.
* `present[child]`: whether the child subtree has a cached copy (including intermediate clean copies).
* `leaf_present[child]`: whether any L1 cache in that child subtree has a valid copy.
* `dirty_child`: the immediate child containing the unique modified/owned leaf, or `-1`.
* `dirty_mode`: the mode (M or O) of that dirty owner, or zero.

The directory metadata is dynamically updated by protocol steps and appears in read decisions: searching sibling subtrees uses `leaf_present`; dirty forwarding uses root `dirty_child`/`dirty_mode`; clean-data hits can be served from the nearest valid ancestor cache. This is not merely a collection of unused summary variables.

This does **not** yet implement dirty lines held at intermediate L2/LLC caches, independent eviction policies, interlevel transactions, asynchronous acknowledgments, or capacity limits. It models clean intermediate caches with an abstract directory, while dirty ownership resides at an L1 leaf.

## Architectural interface (unchanged by topology)

`issue_read`, `issue_write`, `issue_cas`, `issue_evict` store a request in each CPU's abstract `pending/op/arg/expected` interface. `serve_*` atomically completes the request, updates the hierarchy and produces `reply_ver/reply_val/reply_ok/reply_source`.

This is a stable request/response interface **for this new abstraction**, not a claim that the original speculative v2.0 frontend has been integrated or reverified with the new hierarchy. `reply_source` is a performance/diagnostic indication (L1/owner/L2/LLC/memory), deliberately excluded from architectural observational equivalence. Read data and version are included.

Protocol variants:

* MSI: I/S/M; no E, no O.
* MESI: E granted when no other leaf holds the line; local E->M; remote M read writes back and downgrades to S.
* MOESI: remote read of dirty M creates dirty O owner plus S reader; memory can remain stale; evicting the last dirty owner writes back.
* Writes and successful CAS serialize atomically in the cache backend; other leaf copies are invalidated in the same abstract step.

This **atomic** serialization is a major modeling assumption, and why progress is much easier than in the original asynchronous protocol.

## Verified invariants

For each explicitly instantiated topology, Z3 checked initialization and every transition's inductive preservation of a combined invariant:

1. M/E exclude all other L1 copies; at most one M/O dirty owner, with MOESI allowing O+S.
2. Every valid L1 and every valid intermediate clean cache has the latest version; if there is no dirty owner, memory is current.
3. Each `present`, `leaf_present`, `dirty_child`, and `dirty_mode` field agrees with the immediately lower-level child summaries.
4. Pending requests have a valid instruction kind; issue and service transitions preserve all other cores' request/reply registers.
5. Serviced reads/CAS-failures return the pre-service latest abstract memory value; stores/CAS-success update the next version in the symbolic payload array.
6. If a read's diagnostic source is an intermediate cache, that cache has valid current data; if memory is named as its source, memory is current; dirty remote forwarding corresponds to a dirty owner.

`Init -> I`, and `I(s) & Step(s,s') -> I(s')`, UNSAT violation queries, prove the above for **all execution lengths of each fixed checked model**.

## Architectural equivalence when topology changes

Define a relation `Rel` equating `latest`, `mem`, the version->value array, and all original core L1 states and CPU request/reply fields. It deliberately hides internal directory/cache state and `reply_source`.

For every paired named CPU action `a` in two configurations of the same size and protocol, Z3 verifies:

```
I_old & I_new & Rel  => (Enabled_old(a) <-> Enabled_new(a))
I_old & I_new & Rel & Step_old(a) & Step_new(a) => Rel'
```

The common initial abstract memory arrays are assumed equal. These are **relational one-step simulation checks**, not reuse of an existing v2.0 SMT proof certificate. An induction over matched actions gives equivalent architectural observations for matched executions.

Comparisons checked for **MSI, MESI, and MOESI**:

* 4 cores: `[4]` vs `[2,2]`: **222/222** paired checks.
* 8 cores: `[4,2]` vs `[2,4]`: **438/438** paired checks.
* 8 cores: `[2,2,2]` vs `[2,4]`: **438/438** paired checks.
* Increasing width from 4 (`[2,2]`) to 8 (`[2,4]`) while the new cores stay Invalid and idle: **222/222** checks.

This is a precise version of "changing lower-level width/depth without modifying what is above" in the atomic model. It does *not* say new active cores have no interference; they can and do affect other cores through coherence.

## Safety and progress check matrix

| Configuration | Protocols | Safety / handshake / response / source routing |
|---|---|---:|
| `[2,2]`, 4 cores | MSI, MESI, MOESI | **411/411** |
| `[2,2,2]`, 8 cores | MSI, MESI, MOESI | **867/867** |
| `[4,2]`, 8 cores | MSI, MESI, MOESI | **819/819** |
| `[2,4]`, 8 cores | MSI, MESI, MOESI | **819/819** |
| **Total** | | **2916/2916** |

Atomic-progress checks:

* 4-core `[2,2]`, all three protocols: **444/444** SMT checks.
* 8-core `[2,2,2]`, MOESI: **584/584** SMT checks.

The progress proof premises show (a) every pending command has an enabled `Service(c)` event, (b) only that service can clear the pending bit, and (c) serving it does clear the bit. Under **weak fairness of each per-core atomic service event**, each issued request eventually completes in this model. This is a simple mathematical fairness argument supported by verified SMT premises, **not an independently produced temporal-model-checking certificate**, and it does **not** transfer to the asynchronous v2.0 protocol.

Anti-vacuity / negative controls: seven expected SAT or UNSAT bounded traces passed. Reachable traces demonstrate MESI E->M, MESI remote M read and writeback, a clean L2 hit, and MOESI dirty O+S with stale memory. Deliberate mutations show that suppressing dirty-owner writeback or corrupting directory presence causes reachable invariant violations.

Full regression suite, including v2.0: **52/52 tests passed**.

## Reproduce

Python 3.13 and system `libz3.so.4` (loaded through ctypes). No pip install needed.

```bash
python tools/verify_hierarchy_v21.py --fanouts 2 2 --variant all
python tools/verify_hierarchy_v21.py --fanouts 2 2 2 --variant all
python tools/verify_hierarchy_v21.py --fanouts 4 2 --variant all
python tools/verify_hierarchy_v21.py --fanouts 2 4 --variant all
python tools/verify_hierarchy_equivalence_v21.py --a 4 --b 2 2 --variant all
python tools/verify_hierarchy_equivalence_v21.py --a 4 2 --b 2 4 --variant all
python tools/verify_hierarchy_equivalence_v21.py --a 2 2 2 --b 2 4 --variant all
python tools/verify_width_extension_v21.py --small 2 2 --large 2 4 --variant all
python tools/verify_hierarchy_progress_v21.py --fanouts 2 2 --variant all
python tools/verify_hierarchy_progress_v21.py --fanouts 2 2 2 --variant MOESI
python experiments/13_hierarchy/witnesses.py
python -m unittest discover -s tests -q
```

All generated SMT-LIB2 queries and JSON summaries are distributed separately in the v2.1 proof archive, while the full Git repository ships the proof tools and reproduction commands.

## Remaining engineering and research

1. **Integrate this hierarchy into the original asynchronous v2.0 MESI/MOESI message machine**, rather than having a separate atomic abstraction. Introduce interlevel forwarding, invalidation and acknowledgment channels and show a sound abstraction/refinement mapping.
2. Support independently dirty intermediate caches, cache eviction/replacement, and multiple lines without global atomic serialization.
3. Obtain a full fairness-aware temporal verification certificate for the resulting asynchronous hierarchy; source-level atomic-progress lemmas are not sufficient.
4. Prove a truly topology-parameterized correctness theorem rather than instantiating and checking individual widths/depths.
5. Only then measure **genuine proof-certificate reuse** across real protocol upgrades; the current paired proofs are freshly discharged, not automatically recycled from v2.0.

**Bottom line:** the modular interface and topology-independent architectural behavior are proven for this bounded-topology atomic abstraction. The harder asynchronous compositional-verification problem remains open.
