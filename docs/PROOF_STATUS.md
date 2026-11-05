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
