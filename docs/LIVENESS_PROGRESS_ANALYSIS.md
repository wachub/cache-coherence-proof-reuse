# v1.5 — Deadlock, livelock, and progress analysis (unchanged v1.4 model)

## Scope and bottom line

This adds **proof/checker code only** to the existing four-core (two- or three-cache-line) asynchronous MSI + speculative read/write model. No historical cache, transition, or speculation source was changed.

The analysis distinguishes:

- **Terminal deadlock / absence of enabled progress**: in a state with work outstanding, no operation capable of advancing existing work is enabled. This is a *state safety property* and can be discharged inductively.
- **Protocol-internal livelock**: an already-started directory transaction takes infinitely many *servicing* transitions without terminating. We prove a decreasing finite progress rank, excluding this kind of cycle. Arbitrary scheduler activity can still postpone service indefinitely.
- **Starvation freedom**: each pending processor request eventually completes. This is stronger and **is not established**. A concrete weakly fair infinite execution can indefinitely bypass a queued request.

The distinction between **some transition enabled** and **some request eventually completed** is fundamental.

## Verified properties and exact assumptions

Run `python tools/liveness_verify.py --cores 4 --lines 2 3 --output-dir /tmp/liveness_checks`.

The generated SMT-LIB proofs are under the output directory. Results are summarized in `summary.json`. The older safety proofs remain valid and are rerun separately in release testing.

### 1. Single-line protocol transaction progress, four cores

The existing `Protocol` state includes `tx` (active directory transaction), `phase`, per-core `wait`, pending invalidations/recalls, grants, and acknowledgments. We *intercept only the existing constructor for proof generation* to recover transition guards; the transition formulas themselves are unchanged.

Proved by one-step SMT queries under the inherited inductive MSI invariant:

- If `tx != -1`, at least one directory/network **servicing** action is enabled.
- If `tx == -1` and a read/write request is queued, at least one `dir:start_*` action is enabled.
- Each servicing transition of an active transaction strictly decreases the rank below.
- No protocol transition can increase that rank while a transaction is active.
- **Every enabled individual servicing action remains enabled until some servicing action occurs**; unrelated protocol steps cannot silently disable it.
- Active-transaction rank is an integer in `[1, 24]` for four cores.

The rank is

\[
R(s) =
\begin{cases}
0 & \text{directory idle}\\
8 + 3W + D & \text{active, phase 0}\\
2 + G & \text{active, phase 1}
\end{cases}
\]

where `W` is the number of waiting victims, `D` the number of undelivered invalidation/recall messages, and `G` the number of outstanding grants. All components are Boolean counts, so `R <= 8+4*cores = 24` at four cores.

Additional full-system SMT frame checks show that **all foreign-line and architectural/speculative transitions leave the selected line's rank unchanged** for both four-core configurations. Thus the local rank proof transfers compositionally to the combined transition relation.

A service transition strictly lowers `R`. Under **weak fairness of individual directory/network servicing actions**, an active transaction therefore completes in at most 24 *service transitions*. It may take unbounded wall-clock steps because unrelated actions can interleave.

The rank proof is performed on the original independent single-line `Protocol` transitions. The two-/three-line architecture composes these same line protocols, with separately checked frame conditions. This is a **compositional conditional progress result**, not a temporal-model-checking certificate for the entire combined model.

### 2. Speculative frontend progress, four cores, two and three lines

Machine-checked enabledness properties under `I_MSI AND J_spec`:

- An unresolved speculative queue/read always permits confirmation or squashing.
- When an already-confirmed queue head exists and the architectural frontend is idle, it can be issued to MSI.
- A confirmed younger speculative read with no older work in progress can be retired if fresh or replayed otherwise.

Confirmation/squashing is treated as a nondeterministic **environmental resolution**. Nothing currently forces the environment to resolve a branch, so these enabledness checks are not guarantees of eventual resolution.

### 3. Architectural frontend: conditional local and global no-stall

Under the existing MSI invariant and a **write-data representation condition**:

- For each busy architectural command with no pending coherence request, an ask/complete transition is enabled.
- If an architectural command is pending, it corresponds to queued or active protocol work.
- For the combined four-core system, if any existing work is outstanding, **some meaningful progress action** is enabled, excluding the trivial ability to issue fresh commands or stage new speculative writes.

The representation condition requires that a ready-to-complete store (or successful CAS) satisfy `payload_l[latest_l+1] == newval`. It is not automatically guaranteed by the original model's immutable symbolic payload arrays. Thus the global no-stall result is **conditional**.

### 4. Reachable symbolic-payload progress defect (SAT)

The original model uses an immutable symbolic array from version tokens to data values. The core chooses `newval` independently when issuing a store; completion requires `payload[latest+1] == newval`. Those choices can conflict, so a store can get ownership yet be **permanently unable to complete** under that fixed symbolic array. The witness explicitly sets `payload_0[v] = 0` for **all** integer versions and requests `newval = 1`; it cannot complete even after any number of later version increments.

A six-step reachable trace (four cores, two lines) is machine-checked SAT:

1. Core 0 issues a normal store with an arbitrary `newval`.
2. It asks for write ownership of line 0.
3. Directory starts the request and grants M ownership.
4. Grant is delivered and acknowledged.
5. The store is ready to complete, but `payload_0[latest+1] != newval`, so its completion guard is false.

This is a **modeling abstraction problem**, not a claim that an actual MSI controller cannot finish a store. It prevents any honest unconditional per-instruction termination theorem on the present model. Fixing it would require changing the memory-value abstraction or restricting input values; that was **not done** in this version.

### 5. Reachable weak-fair queued-request starvation (SAT), including the combined model

The original **four-core single-line MSI protocol** admits a reachable 13-step prefix followed by a 14-step cycle. More importantly, the full **combined four-core model (two or three lines, ordinary R/W/CAS and speculative state)** admits a reachable **18-step prefix followed by an 18-step cycle**. Core 0 has a queued read. Cores 1 and 2 endlessly alternate M ownership by issuing **failing CAS operations** (the array returns zero, the expected CAS value is one); whenever the directory is briefly idle it chooses one of these instead of Core 0. Both cycle queries restore **every** modeled state variable to its starting value while Core 0's read remains queued.

All three SMT-LIB lasso queries are SAT, including the full combined model. This defeats starvation freedom even under **weak fairness of internal directory/network transitions** (fresh external client requests are not required by fairness): the action `dir:start_rqR_c0` is enabled infinitely often but is repeatedly disabled whenever another transaction starts, so it is not *continuously* enabled. Strong fairness of queued-request arbitration (or explicit fair queueing) is needed to exclude this witness.

Unlike the payload mismatch, this is an authentic scheduling/protocol **starvation behavior** of the model, not merely a data abstraction issue. Importantly, it does **not** violate the single-transaction rank proof: every transaction that actually starts completes.

### 6. Negative controls

Two deliberately faulty *verification variants*, without modifying any model transitions, must be SAT:

- Pretend all directory `grant` actions are unavailable: a live transaction can lose all enabled service actions.
- Use an inadequate rank based only on the count of waiting victims: delivering an invalidation does not lower the rank.

These establish that the proof obligations actually detect essential protocol progress conditions.

## Which liveness claims are and aren't justified?

| Claim | Status |
| --- | --- |
| Every already-active directory transaction has a possible next service step | **SMT-verified**, four cores |
| Every service step strictly decreases a positive rank until the transaction completes | **SMT-verified**, four cores |
| No purely internal service-action livelock within an active transaction | **Follows from rank**, with full-system rank framing checked separately |
| An active transaction completes under weakly fair servicing | **Mathematical consequence** of checked rank, guard stability and enabledness; not a separate temporal proof artifact |
| Combined 4-core model always has some progress action if existing work and required payload compatibility | **SMT-verified conditional enabledness** |
| Every read/write/CAS eventually completes unconditionally | **False**, reachable symbolic payload stall |
| Every queued request eventually starts under weak fairness of internal steps | **False**, reachable full combined-system repeating starvation traces |
| Strong-fair queue arbitration + service fairness guarantees all requests terminate | **Not fully established** for combined speculation + write input model |
| Complete CTL/LTL/justice/fairness model-checking certificate | **Not done** |
| Arbitrary core counts or queue depth | **Not done** |

## Research implications

The next meaningful incremental verification work is **not** adding cache hardware features, but making the progress contract compositional:

1. Model directory arbitration fairness explicitly as a scheduling assumption (weak/strong fairness are different).
2. Repair the input-value representation *in a separate abstraction refinement* (and recheck all affected proofs).
3. Synthesize local assume-guarantee progress certificates (`enabled`, `decreases rank`, `eventually selected`) and compose them across independent lines and speculation.
4. Compare against PDR or a Büchi/CTL model checker on representative closed finite abstractions. Full liveness verification requires fair-path semantics, not simply an UNSAT one-step query.

The existing SC trace-refinement theorem is also not fully machine-checked, independently of liveness.
