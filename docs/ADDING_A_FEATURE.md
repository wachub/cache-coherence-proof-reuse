# Protocol for adding a new speculative / coherence feature

1. **State the optimization:** e.g. second speculative load, merged stores, extra directory transaction, out-of-order drain.
2. **Keep the architectural contract unchanged** unless the intended memory model changes explicitly.
3. **Identify the delta:** old steps restricted? old steps modified? added steps? New state variables?
4. **Prove old-step frame conditions**: old behavior still maintains new invariants, and any changed old steps must be rechecked.
5. **Prove local well-formedness and noninterference** with old coherence invariants, using UNSAT of the negated inductive obligations.
6. **Prove observable refinement:** internal speculative steps stutter; retirement matches the reference machine's permitted next action, preserving source program order.
7. **Generate one positive witness and one deliberately buggy variant** to check sensitivity.
8. **Record configuration and proof status:** fixed core count, cache lines, queue depth, data type, message assumptions, liveness exclusions.
9. **Commit a new self-contained experiment** (or extension directory) and tag it; record the previous proof version reused.
10. **Only afterwards optimize:** use SAT/SMT to localize broken obligations and consider legal repairs that retain the performance benefit.

Suggested naming for new proof files:

```text
initial_new_feature.smt2
old_steps_preserve_extension.smt2
new_steps_preserve_old_invariant.smt2
new_steps_preserve_extension.smt2
new_steps_refine_reference.smt2
positive_witness.smt2
broken_variant_counterexample.smt2
results.json
```

A valid proof of a restricted frontend does not automatically imply progress or fairness. If a performance optimization changes the interface or the set of enabled transactions, treat the old proof assumptions as suspect until re-established.
