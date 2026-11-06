# v1.7 branch: fairness-conditional end-to-end progress reasoning

**Branch:** `proof/temporal-fairness-v1.7` (based on `main` at v1.6, commit `70875d4`).

**Scope and honesty:** This release proves *many concrete SMT obligations* that make a
compositional mathematical fair-progress proof possible, and independently model-checks
fair lassos for a deliberately small finite progress abstraction. It is **not yet an
independently machine-checked global LTL/CTL theorem over the original unbounded
integer-array cache-plus-speculation transition system**. Do not cite it as such.

## What changes in the branch

The v1.6 cache protocol and speculative transitions are unchanged. A **proof-only**
reachability-strengthening invariant is added in `TemporalFairSpec`:

```
for each core c:  load_confirmed[c] => (ready[c] == qlen[c])
```

The v1.6 invariant without this strengthening admits an unreachable SMT state in
which a confirmed read has an unconfirmed younger queue suffix and can be squashed.
The strengthened initialization and complete inductive step are checked for each
configuration, and a SAT negative control documents why the older invariant is
insufficient for this particular proof rule.

## Explicit, reasonable environmental assumptions

The model is a nondeterministic interleaving semantics. It would be false to
claim eventual completion on *every* possible schedule. These are the exact
conditions for a fair-path theorem:

1. **WF(SomeService(line)):** if the disjunction of all currently enabled
   network-delivery/directory-ack/grant actions for a line stays enabled,
   eventually one of them executes. The action choice may change with state.
2. **WF(SomeStart(line)):** if an idle line has queued requests continuously,
   some selected directory-start transition eventually executes. Per-core
   start fairness is not assumed; round-robin protocol arbitration supplies it.
3. **SF(Ask(c,kind,line)) and SF(Complete(c,kind,line)):** for every architectural
   CPU ask/completion action, if its guard is true infinitely many times, it is
   eventually executed. This is **strong fairness**, necessary because cache
   permission can be revoked before the CPU uses it. CPU command *issuance* is
   not assumed fair and is outside the scope of completion of an already-issued
   command.
4. **WF(ResolveUnconfirmedWrites(c)):** `confirm OR squash_suffix` for an
   unconfirmed speculative queue suffix. A weaker assumption `confirm OR
   squash_suffix OR squash_read` does *not* suffice: one could squash an
   unconfirmed younger read repeatedly without resolving the store suffix.
5. **WF(ResolveUnconfirmedRead(c)):** `confirm OR squash_suffix OR squash_read`
   for an unconfirmed speculative read.
6. **WF(IssueConfirmedStore(c)):** disjunction over the per-line FIFO-head
   issue actions for a confirmed queue head.
7. **WF(SettleConfirmedRead(c)):** disjunction of speculative fast retirement
   and replay for a confirmed read when older work is finished.
8. The number of cores and cache lines is positive and finite. There is no
   permanent loss of messages: the model's delivery events remain possible;
   assumption (1) requires they eventually be serviced.

For event `E`, weak fairness means `FG Enabled(E) -> GF E`, and strong fairness
means `GF Enabled(E) -> GF E`. Here `F` means eventually, `G` always.

## Temporal properties and proof structure

The intended properties for a fixed concrete configuration are:

```
G(active_transaction(line) -> F idle(line))
G(queued_request(c,line) -> F transaction_started_for(c,line))
G(pending(c,line) -> F !pending(c,line))
G(busy(c) -> F !busy(c))
G(unconfirmed_write_suffix(c) -> F resolved_write_suffix(c))
G(unconfirmed_read(c) -> F (!load_active(c) or load_confirmed(c)))
G(confirmed_queued_store(c) -> F issued_as_architectural_store(c))
G(confirmed_read(c) -> F (!load_active(c)))
```

These are **per-request, event-indexed** claims: `busy(c)` identifies one
architectural instruction until it completes, so `!busy(c)` witnesses its
completion, and a pending request refers to a particular core/line while the
core is busy. Squashed speculative operations do not promise retirement.

### A. Active directory transaction terminates

For phase 0, use `R=8+3*W+D`; for phase 1, `R=2+G`, and `R=0` when idle.
The v1.6 SMT artifact proves `0<R<=8+4N` while active; every servicing step
strictly decreases `R`; non-servicing steps do not increase it and cannot
change which service actions are enabled while the rank is unchanged. Every
active state has at least one enabled service. Assume an active transaction
never terminates. By WF(SomeService), it then performs infinitely many
servicing transitions, which would give an infinite descending sequence of
natural-number ranks. Contradiction.

### B. A queued request cannot starve

While queued, it remains queued until its own directory start. If another
queued core starts first, the RR pointer strictly decreases the tracked
request's circular distance (`0..N-1`). Every started transaction terminates
by A. When idle with a queued request, SomeStart remains enabled until a
start; WF(SomeStart) eventually selects someone. Thus the tracked request
can be bypassed at most `N-1` times and starts eventually. Its corresponding
transaction terminates, and the grant-delivery step clears its pending bit.

### C. An issued architectural command completes

The checked transition-level lemmas show:

* `busy(c)` stays true until one of that core's completion actions executes.
* If `busy(c)` and there is no pending coherence request, then some CPU ask or
  completion action is enabled (v1.6 lemma).
* A pending request belongs to the issuing busy core and either sits in the
  queue or is the active directory transaction, so by A and B it clears.
* A grant clears pending and supplies a valid cache permission. With suitable
  permission, the corresponding read/store/CAS completion is enabled for all
  integer operands (no immutable-payload representability assumption).

Suppose an issued command stays busy forever. It cannot stay pending forever
by A and B. Therefore states with `!pending` occur infinitely often; a finite
set of ask/completion action guards is enabled infinitely often. Strong CPU
fairness forces either a completion (contradiction) or infinitely many asks.
Each ask creates a pending request, and each such request is eventually
granted, producing infinitely many states where the corresponding completion
is enabled. Strong fairness then forces completion. Contradiction.

### D. Speculative work resolves

The new SMT checks establish that unconfirmed write suffixes and unconfirmed
reads persist until their respective resolving event and that the event is
enabled. WF of each **separate** resolving event class gives eventual resolution.
A confirmed store head persists while the core is idle until an issue action;
ordinary busy instructions finish by C, and FIFO issue fairness forces each
confirmed head to be issued and finish (at most two queued stores).
The strengthened invariant shows a confirmed speculative read has no
unconfirmed writes ahead of it. With finite confirmed stores drained, the
read reaches `qlen=0 && !busy`. The disjunction of fast retirement and replay
is enabled and remains enabled until one fires. WF(SettleConfirmedRead)
settles it. Replayed reads become ordinary commands covered by C.

**Important qualification:** The preceding is a *mathematical composition
argument* based on checked one-step premises and well-founded induction.
It is not currently a proof term accepted by Lean/Coq or a native global
fairness-aware model-checker certificate for the unbounded concrete system.

## Mechanically executed checks

For 4 cores x 2 lines and 4 cores x 3 lines, `tools/temporal_v17_verify.py`
checks all new obligations against the actual v1.6 transition formulas,
including strengthened initialization/induction, ask/grant/start effects,
weak-fairness enabling/stability, completion enabledness, speculative
resolution, and confirmed-read persistence. **290/290 UNSAT**:

| Configuration | Checks | Result |
|---|---:|---|
| 4 cores x 2 lines | 124 | 124 UNSAT |
| 4 cores x 3 lines | 166 | 166 UNSAT |

All queries are regenerated from source; each has an exact SHA-256 digest and
solver result in `artifacts/temporal_fairness_v1_7/summary.json`.

The independent `tools/fair_lasso_v17.py` exhaustively checks all reachable
states in a **finite abstraction** of a tracked request, round-robin directory
and competing cores, with weak servicing/start/ask fairness and strong CPU
completion fairness. It finds **no fair infinite lasso with an incomplete
request** for 2, 3 or 4 cores. It *does* find a fair incomplete-request lasso
if the arbiter is unfair, if CPU completion has only weak fairness, or if
servicing/start fairness is removed. This is 15/15 expected outcomes, not a
substitute for checking the concrete unbounded transition system.

Finally, **33/33 regression tests** pass (29 inherited plus 4 new).

## Reproduction

```bash
python tools/temporal_v17_verify.py --cores 4 --lines 2 3
python tools/fair_lasso_v17.py --max-cores 4
python -m unittest discover -s tests -q
```

Requirements: Python 3, system `libz3.so.4` (loaded through ctypes by the
existing checker). `.smt2` queries generated by the first command can be
replayed with any compatible SMT-LIB2 solver.

## Remaining work to claim an independently *fully* verified result

1. Encode the actual concrete 4-core composition and the exact WF/SF fairness
   predicates in a temporal proof assistant or fairness-aware model checker
   and obtain a native machine-checked global theorem, including D above.
2. Verify the full parameterized invariant and fairness theorem for **all**
   positive core counts, not only symbolic-N rank arithmetic and finitely
   instantiated state machines.
3. Independently machine-check complete trace refinement to the selected
   architectural memory model (sequential consistency in the current design).

The first item is the missing step for **fully machine-checked temporal
liveness** in the present concrete model. The other two are broader research
milestones. Safety and compositional progress evidence is stronger in v1.7
than v1.6, but none of these remaining claims should be silently promoted
to "proved".
