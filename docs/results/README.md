# v1.4 contract-inference evidence

`auto_contracts_4cores_2lines.json` and `auto_contracts_4cores_3lines.json`
record the **fresh Z3** inference runs for the existing combined-speculation model.
All 7 transition families have SAT one-step feasibility, UNSAT vocabulary
coverage, and UNSAT final inferred-contract coverage, plus equivalence to the
v1.3 handwritten contracts under the existing invariant assumptions.

The generated full SMT-LIB2 proof scripts are intentionally omitted from Git
because they are regenerable; use the documented `--output-dir` command to
recreate them and independently check `UNSAT` with Z3. See
`docs/AUTOMATIC_ORDERING_CONTRACTS.md`.

The v1.3 compositional suite, original MSI baseline and independent combined
induction were also rerun for 4c2l and 4c3l and all passed, including the three
existing negative controls. The new test file checks three additional broken
model variations and a family-localized proof-reuse scenario.

**Scope:** These are one-step inductive safety/interface checks, not a separately
mechanized end-to-end sequential-consistency trace-refinement theorem.
