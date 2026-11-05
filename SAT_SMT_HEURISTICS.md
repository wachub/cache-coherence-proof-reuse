# SAT/SMT heuristics for incremental cache-coherence and memory-ordering verification

**Purpose.** This is a reusable, problem-specific playbook for adding one concurrent hardware feature at a time to our directory-based MSI + strict-ordering abstract machine, while reusing prior solver results. This is not a generic SAT tutorial. It describes **methods actually used** in the archived experiments, then separately identifies promising techniques **not yet implemented**.

## 0. Precisely define the proof target

Before running a solver, record:

1. **Architectural observation:** returned read/CAS values; committed writes; allowed program order; which events are invisible internal steps.
2. **Implementation state:** cache `I/S/M`, directory owner and sharers, in-flight invalidation/ack/writeback/grant messages, latest-value ghost, and (for refinements) frontend operation state.
3. **Environment:** whether messages may reorder, be dropped, remain delayed indefinitely, or be duplicated; what requests the clients may issue; whether the interface allows only one in-flight instruction per core.
4. **Scope:** cores `N`, cache lines `K`, queue capacity `B`, value domain, program schema, transition count, and explicit assumptions.
5. **Property:** safety invariant versus sequential-consistency *trace refinement* versus progress/liveness. These are different proof obligations.

A solver can faithfully prove the **wrong specification**. A review of the interface contract matters as much as the SAT encoding.

## 1. The main trick: solve the negation of an induction step

Let `Init(s)` be the initial-state predicate, `T(s,s')` the transition relation, `I(s)` the proposed strengthened invariant, and `Bad(s)` the forbidden state.

Construct three queries:

```text
Q0 = Init(s) ∧ ¬I(s)
Q1 = I(s) ∧ T(s,s') ∧ ¬I(s')
Q2 = I(s) ∧ Bad(s)
```

Require **UNSAT** for all three. Then `I` holds in all reachable states, and `Bad` is unreachable for **arbitrary execution length of the modeled finite-core/line machine**. `Q1` is a one-step query, but proves an unbounded-depth result *because it is inductive*. This was used in the single-line MSI, SC frontend, FIFO-order, and speculative extensions. For fixed `N` and `K`, integer data may be unconstrained/symbolic, but that does **not** quantify over arbitrary `N` or `K`.

Distinguish this from bounded model checking:

```text
BMC_k = Init(s0) ∧ T(s0,s1) ∧ ... ∧ T(s{k-1},s{k}) ∧ Bad(s{k})
```

A SAT BMC instance gives a concrete bug trace. An UNSAT BMC instance rules out only the checked depth unless a completeness argument is supplied. In our experiments, BMC is mainly used to find mutant counterexamples and positive witness traces.

## 2. Strong *local* invariants: permission ledger and messages in flight

Do not try to prove only `not(two M caches)` or `each S/M holds latest`. These are often **not inductive** on their own because grants, dirty data, and revoked permissions can be *in transit*.

Include cases such as:

- **Single writer:** if a cache is `M`, no other cache is authorized to modify or keep conflicting readable permission.
- **Ownership consistency:** directory ownership is related to cache `M` or dirty writeback pending, not necessarily identical to cache mode on each step.
- **Pending grants:** a directory grant in flight reserves permission; do not start a conflicting new transaction until its delivery is acknowledged.
- **Ack discipline:** a sharer relinquishes its valid permission **before** the invalidation acknowledgment is accepted.
- **Dirty-data conservation:** if directory memory is older than `latest`, a modified cache or in-flight writeback retains the latest version.
- **Request/message phase typing:** constrain `inv`, `recall`, `ack`, `wb`, `grS`, `grM`, `gack`, `wait`, `phase`, `tx` to compatible states.

These ghost predicates make induction succeed across all asynchronous interleavings without directly enumerating complete runs. See `experiments/02_single_line_smt/cache_smt_report.md` and `cache_smt_verifier.py`.

**Warning:** A directory recording an owner does not mean that owner's local cache has already processed the grant. Always model the handoff state.

## 3. Ghost data versions plus actual payloads

For single-line coherence, a ghost monotonic `latest` version detects stale copies and lost dirty data. This makes the property simpler than reasoning about all possible bit patterns. For SC and CAS, maintain a correspondence between logical versions and **symbolic payload values**, including repeated values: CAS must compare payloads, not write-version numbers.

- A version token may distinguish `A → B → A` (the **ABA** issue) even when payloads match again.
- Version tokens are a verification abstraction. Do **not** assume a real processor has an unbounded version counter.
- If hardware values are finite-width, check bit-vector wraparound or prove the ghost-to-hardware abstraction separately.

## 4. Separate single-line protocol safety from cross-line ordering

MSI constrains one line's permissions; it does **not** impose program order among different lines. Our four-core SC baseline avoids the mismatch by allowing **at most one outstanding architectural memory operation per core**, with in-order completion. That enforces a strong interface discipline, while the MSI proof manages asynchronous per-line messages.

The two-line message-passing and FIFO experiments test a smaller release/acquire condition:

```text
writer: store(data); release_store(flag)
reader: acquire_load(flag); read(data)
```

If the reader observes that release, it must not see the older data under the stated no-intervening-write assumption. To avoid *assuming* the result, represent a store buffer, require earlier stores to drain coherently before the release becomes visible, and make the acquire order later observations.

Do **not** claim this litmus test is a proof of a general C11, ARM, x86, or RISC-V memory model. The stronger four-core SC result relies on a specified in-order frontend and a **paper-level** trace argument, not an independently machine-checked universal trace-refinement theorem.

## 5. Incremental proof reuse for a new feature Δ

Let the old machine have transitions `T_old`, invariant `I_old`, and an already established proof. The new machine adds feature state `q`, a local invariant `J(q,s)`, and new transition schemas `Δ`.

Check **only the additional obligations**, provided the unaffected old transitions are exactly reused (or merely guarded more tightly):

```text
Init_new(s,q) ∧ ¬(I_old(s) ∧ J(s,q))
I_old(s) ∧ J(s,q) ∧ Δ(s,q,s',q') ∧ ¬I_old(s')
I_old(s) ∧ J(s,q) ∧ Δ(s,q,s',q') ∧ ¬J(s',q')
```

Also prove old transitions preserve `J` (usually by *framing*: they leave new state unchanged), and check that any guards restricting old actions do not silently alter required progress assumptions.

**Crucial extra check—refinement:** preserving `I_old` alone is not enough. For each new step, prove either:

- `Stutter`: no architecturally observable old state changes, or
- `OldStep`: the projection is a legal old interface step.

SMT counterexample query:

```text
I_old ∧ J ∧ Δ ∧ ¬(Stutter ∨ OldStep)
```

If UNSAT, old safety can be inherited **assuming** old steps and the refinement relation genuinely cover all projected transitions. A trace-level refinement may require extra history/prophecy variables or several old steps per new step; our examples use the deliberately simpler stutter-or-one-step pattern.

This method was used for **speculative loads** and **two queued speculative stores**.

## 6. Speculative reads: validate at architectural retirement

A speculative load may capture `(address, payload, ghost_version)` while an older operation is outstanding. It must not become an architectural observation until it is safe to retire. On invalidation or a changed version, **replay** it through MSI rather than returning the stale value.

Relevant delta proof: a speculative read changes no coherent state, and its retirement must either (a) return an observation allowed by the abstract memory order, or (b) trigger a replay. Version checks are a modeling convenience; actual invalidation tracking and speculative-load-queue mechanisms are outside the proof.

**Mutant:** remove validation → SAT trace with speculative `0`, remote write/invalidation, then illegal stale retirement.

## 7. Speculative writes: two-entry confirmed-prefix queue

Use per-core variables:

```text
0 <= qlen <= 2
0 <= ready <= qlen
queue entries: (address_0,value_0), (address_1,value_1)
```

`ready` counts the **confirmed prefix** of the speculation queue. Stage, confirm and squash change only private queue state. The only transition issuing an old MSI store is `retire_head`, guarded by `ready > 0` and no older outstanding architectural instruction. Always shift the FIFO head after retirement.

The especially valuable check is **program-order refinement**: even if MSI sees only coherent stores, MSI by itself cannot tell that the second speculative store was originally younger. A second-store-first mutant preserves cache coherence but violates SC relative to the originating program.

**Mutants:**

- `retire_tail_first`: younger confirmed store appears first; another core sees the newer B value before older A is visible.
- `retire_unresolved`: wrong-path store affects shared state before confirmation.

The proof covers capacity 2 in fixed 4-core, 2/3-line models. Arbitrary capacity `B` is only a proposed induction generalization, **not a completed machine proof**. Reads forwarded from pending speculative stores, speculative CAS, early globally visible stores and rollback are not modeled.

## 8. Positive witnesses and mutation testing prevent vacuous claims

Every negative theorem should have nearby **positive SAT checks** demonstrating useful behavior can occur:

- Owner writes, is recalled, dirty data is handed off, and another core reads the new value.
- Two contending CAS operations have exactly one successful claim in the appropriate setup.
- Release/acquire publication completes without stale data.
- A speculative read succeeds quickly when valid and replays when invalid.
- Two confirmed speculative stores retire in order; a squashed store stays invisible.

Create deliberately broken transitions: grant before acknowledgments; discard dirty writeback; bypass release ordering; retire stale load; issue younger or unconfirmed store. A **real reachable SAT witness** is more convincing than SAT in an arbitrary unreachable state that merely violates an overly strong invariant.

Record solver result, model configuration, witness trace length, and expected outcome in JSON next to the `.smt2` file. Inspect witnesses: SAT from inconsistent initial constraints or unconstrained outputs is not meaningful.

## 9. Solver-encoding and performance heuristics

Techniques **actually used in the archived code**:

1. Encode guarded transitions as SMT formulas over *current* and *next* state, with explicit framing of all unchanged fields.
2. Split proof into `Init`, `Induction`, and `Safety` queries; split new-feature checks into `queue invariant`, `old invariant preservation`, and `refinement/program order`.
3. Constrain finite control states (`I/S/M`, directory phases, queue lengths) but keep data as symbolic mathematical integers where justified.
4. Generate stand-alone SMT-LIB2 queries and store them with JSON solver outcomes for reproducibility.
5. Use **small counterexample instances** (often two cores/two lines) even when the correct invariant is checked on four or more cores.
6. Replay an old proof's invariants unchanged; avoid regenerating huge old protocol transition relations for pure frontend extensions.

Potential future optimizations (**not implemented or benchmarked here**):

- Incremental solver contexts (`push`/`pop`) across many related candidate designs.
- IC3/PDR for automatic invariant discovery when hand-written strengthened invariants become unwieldy.
- Symmetry reduction for indistinguishable caches, partial-order reduction for independent line transactions.
- Compositional cutpoints and interpolants for protocol-level environment assumptions.
- Unsat-core-guided invariant minimization and MaxSAT repair suggestions.
- Bit-vector/word-level modeling for realistic integer overflow and width constraints.
- Parameterized proofs for arbitrary `N`, `K`, or speculation-queue bound `B`.

## 10. Feature-addition checklist (copy into each new milestone)

- [ ] Keep a **reference spec** describing architectural observations and program order.
- [ ] List exactly which old transition schemas have changed; prefer adding `Δ` and guarding old actions.
- [ ] State new ghost variables and their meaning (especially whether physically implementable).
- [ ] Specify non-vacuity: at least one successful new feature trace.
- [ ] Prove initialization, old-step framing, delta safety, delta queue/state well-formedness, and delta refinement.
- [ ] Mutate a key guard; obtain and inspect a SAT counterexample.
- [ ] Check no accidental new observables appear under speculation.
- [ ] State what **is not proved** (progress, ISA model, RTL, arbitrary-size parameters).
- [ ] Preserve SMT scripts + solver outputs + model configuration in a new commit.
- [ ] Benchmark proof time and model size, but do not infer hardware speedup without a performance model.

## 11. How to reproduce relevant proofs

From the root of this archive:

```bash
python tools/verify_representative.py
cd experiments/08_speculative_stores/speculative_stores_project
python speculative_store_delta.py --cores 4 --lines 2 --out-dir /tmp/spec_store_check
python mutant_checks.py
```

Other relevant sources: `experiments/02_single_line_smt/cache_smt_verifier.py`, `experiments/04_fifo_publication/cache_memory_order_buffer_proof.py`, `experiments/06_four_core_sc/sc_msi_4core_verifier.py`, and `experiments/07_speculative_load/speculation_incremental_project/new_proof/speculative_load_delta_proof.py`.

### Suggested next proof boundary

An honest next feature is **load forwarding from still-pending speculative stores**, or a *realistic multi-entry reorder buffer* whose speculative writes can be confirmed independently but retire in order. The invariant needs to relate frontend program-order tags and the MSI abstract memory order; preserving coherence alone will not be enough.


## v1.0 addendum: verifying load/store speculation together

**Do not conflate coherence and instruction ordering.** The original MSI
invariant can remain perfectly valid even while a speculative read retires
before an older speculative write. Add a separate interface/refinement contract
that allows only (a) stutters on old state, (b) the oldest confirmed store
entering the old frontend, (c) replay through the original read interface,
and (d) a fast read whose result equals the current abstract reference value.

**Capture a relational ghost invariant.** If a speculative cache read records
`version=v` and `value=x`, carry the invariant
`active ∧ from_cache ⇒ x = payload[v]`. Merely checking that the captured
version remains valid is insufficient when the read payload is unconstrained
in the inductive hypothesis. Prove that every new transition preserves this
relation and that old transitions frame the speculative fields.

**Forward from the youngest older store.** For two pending writes to the same
line, the read must see the second write, even if neither has reached MSI.
At read retirement require the queue to be empty **and** the old `busy` bit
to be false, because the queue entry disappears when issued but the write
becomes coherent only when the old frontend completes it.

**Validate or replay.** If an intervening coherence transaction invalidated
the source cache line or changed its version/value, do not return the captured
result; reissue the read through the old protocol. Two deliberately broken
mutants—unvalidated retirement and premature retirement—must produce SAT
counterexamples; check actual reachable traces too.

The v1.0 source and SMT-LIB queries are in
`experiments/09_combined_speculative_reads_writes/`. All of these arguments
concern a fixed four-core abstract model; full trace-refinement and
parameterized queue-length proofs remain separate tasks.
