# Focused research roadmap: compositional proof reuse for evolving cache architectures

## Candidate paper hypothesis

A previously verified concurrent architecture can undergo a local protocol upgrade or topology change while retaining **machine-checkable proof obligations** for unaffected clients, even when the implementation state encoding changes. A sound algorithm can discover/recheck the impacted interfaces and transfer appropriate certificates at lower verification cost than re-proving everything.

## Algorithmic questions

1. **Stable external interface:** Which memory/coherence observations must be preserved by a module replacement (permissions, values, ordering, progress)? Explicitly define observation hiding and trace relation.
2. **Sound certificate transfer:** Under what mechanically checked relation may a certificate for module `A` be reused with replacement `B`? Mere textual equality or SAT formula cache reuse is insufficient.
3. **Automatic dependency analysis:** Find the minimal sound re-verification closure when interface contracts, state variables, or transition families change.
4. **Incremental solver integration:** Compare assumption-based incremental SMT, PDR/IC3 clause reuse, and verified module-contract reuse. In particular distinguish proof *transfer* across state spaces from solver context reuse.
5. **Progress and memory ordering:** Account for fairness and genuine temporal properties; do not conflate local enabledness with eventual completion or per-line coherence with SC/TSO refinement.

## First experiment

- Base: directory MSI at fixed 4-core × 2-line and 3-line configurations.
- Change: MESI addition (E state and local write), with matched external interface.
- Prove: a reusable client-level theorem; compatibility of both module implementations with the client contract; no unproved model change.
- Compare: full fresh Z3 induction, old exact-query caching, incremental PDR if available, and semantic contract approach.
- Add: positive reachable E-state witness and negative grant/ownership mutations.
- Report: formal obligations, solver times and peak RSS, amount of soundly reused proof, and any manual proof burden.

## Second experiment

Replace a flat module with the v2.1 hierarchy while preserving a common interface. Before attributing speedups to true concurrency verification, model and prove asynchronous messages between levels. The current v2.1 atomic model is only a reference abstraction.

## Scope and novelty caveats

Earlier work already covers parameterized cache verification, hierarchical MSI/MESI, assume-guarantee proofs, and incremental IC3. A publishable claim must identify a novel proof-transfer rule, automation result, or experimentally compelling algorithm beyond these baselines. Agents are **untrusted proposers**, not a substitute for theorem checking.

## Submission evidence checklist

- Soundness statement and proof, explicit environmental assumptions.
- External and internal benchmark corpus with well-defined modifications and wrong mutants.
- Fully reproducible scripts with exact SMT queries and solver configurations.
- Distinction between proof-state reuse, generated lemmas, and fresh re-verification.
- Honest incomplete/global-property status and limitations.
