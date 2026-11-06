# Scope and status of the archived proofs

This index is deliberately conservative. Each entry describes **what the accompanying recorded proof or checker establishes under the model assumptions**. A result stated as "inductive" refers to a proof of arbitrarily long executions for *fixed* numbers of cores/lines, not a proof for arbitrary sizes.

| Milestone | Checked method | Scope | Important limits |
|---|---|---|---|
| Explicit-state MSI | All reachable states in finite graph | 2–4 cores; single cache line; finite writes | Does not imply generalized parameters or RTL |
| Single-line SMT | Init/step/safety UNSAT induction | Multiple fixed core counts (reported 2–16); symbolic write versions | One line; transaction serialization; no full trace theorem |
| Two-line publication | SMT induction for message passing and mutant | 2 cores; 2 lines; fixed publication pattern | Release-order constraint partly at frontend interface |
| FIFO publication | SMT induction for concrete two-slot store-buffer behavior | 2 cores; three lines including flag; fixed program | Not arbitrary instruction streams or queue size |
| Flush/invalidate | Finite-state exhaustive checking | 2–3 cores; 2–3 addresses; small value sets | Alternative single global lock model, not MESI/MSI proof |
| Four-core MSI+SC | SMT induction of safety and frontend atomic completions; paper-level trace argument for SC | 4 cores; 2/3 lines; one active op/core | Trace-level SC claim not separately mechanized; no liveness |
| Speculative load delta | SMT induction + bad mutant/witnesses | 4 cores; 2 lines; 1 speculative load/core | Abstract version token; no real load queue, no RTL |
| Speculative store delta | SMT induction + two mutants/witnesses | 4 cores; 2/3 lines; 2 queued stores/core | Private writes only until confirmed, strict FIFO retirement, no forwarding |

**Major omitted obligations across the archive**: parameterized cache/line counts; formal complete trace refinement from a real ISA; realistic RTL and physical implementation; progress (deadlock/livelock/starvation); cache replacement, TLBs, coherence bypasses, DMA/GPU traffic, interrupts, power failures, finite-width token wraparound. The model is intended as an incremental proof experiment rather than a validated production hardware specification.

**Recorded results vs newly rerun checks.** The stage-specific JSON files are archived outputs from previous work. `tools/verify_representative.py` reruns a small selection against the locally available Z3 library and reports fresh results. A successful replay does not independently audit the correctness of all modeling assumptions.

## v1.5 progress / deadlock / livelock / starvation analysis

No model transitions changed. `tools/liveness_verify.py` and
`docs/LIVENESS_PROGRESS_ANALYSIS.md` machine-check local transaction-enabledness, persistence of enabled servicing guards,
well-founded rank descent, speculative frontend enabledness, conditional combined
system enabledness, and whole-model rank framing for four cores and two/three
lines. The 4-core rank is positive and at most 24 while a transaction is active.

**Do not claim full starvation freedom or unconditional liveness.** Z3 found
reachable repeating 18-step cycles in **both full combined models** where a
queued request is bypassed indefinitely under weak fairness of *internal*
protocol scheduling. A distinct reachable write-completion stall follows from
the inherited immutable payload-version representation. See the proof report
for assumptions and separate results. The full safety regression and 24 unit
tests passed without modifying historical models.

## v2.0 MESI/MOESI selectable extension

See `../MESI_MOESI_EXTENSION_v2_0.md` for the formal scope, new variants, SMT proofs, witnesses, negative controls, and commands. Safety induction for 4 cores × 2/3 lines passed for MESI and MOESI. 4×2 local progress obligations passed, but no global temporal-liveness certificate or full SC refinement theorem has been produced. **Do not reuse v1.9 MSI proof hashes as proofs of these changed systems.**
