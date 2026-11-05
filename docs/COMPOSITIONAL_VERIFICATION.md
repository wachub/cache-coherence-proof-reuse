# Compositional SAT/SMT contracts for speculative MSI (v1.3)

**Scope:** A verification *wrapper* around the unchanged `experiments/09_combined_speculative_reads_writes/` abstract transition system. The cache model, transition semantics, number of speculative operations, and previous proofs have **not** been modified. This release adds no processor feature or performance claim.

## 1. What is the reusable unit of proof?

A compressed CNF file alone is **not** a reusable correctness argument. A useful reusable object is a theorem with an explicit **assumption / guarantee contract**, a dependency list, and the exact formula and solver settings used to check it.

For the existing transition system, write:

- `I(s)`: the old four-core MSI + frontend invariant;
- `J(s)`: the combined speculation invariant, including forwarding's captured-value relation;
- `T_old(s,s')`: inherited MSI/network/front-end transitions (some guards strengthened; speculative fields frozen);
- `D_f(s,s')`: a disjunction of the new transition schemas in family `f`;
- `C_f(s,s')`: the **typed architectural effect** permitted for family `f`.

The important proof obligations are:

```text
Init_new(s)                            => I(s) and J(s)
I(s) and J(s) and T_old(s,s')         => I(s') and J(s')
I(s) and J(s) and D_f(s,s')           => I(s') and J(s') and C_f(s,s')  for each f
OR_f D_f(s,s')                        == all new transitions (coverage)
OR_f C_f(s,s')                        == original architecture-interface contract
```

For each implication, check the **negation** with Z3: `UNSAT` establishes the implication for all symbolic states satisfying the antecedent. The MSI baseline induction is still a prerequisite; this code does not silently assume `I` is established.

The composition theorem is algebraic: since every new transition is in exactly one family, all per-family obligations imply the aggregate new-transition obligation. Combined with the inherited-step checks and initial-state checks, the conjunction `I ∧ J` is inductive. This is a safety theorem for the **fixed abstract configuration**, not a trace-refinement theorem and not a proof of progress.

## 2. Seven contracts extracted from EXISTING transitions

| Family (`D_f`) | Which actions | Architectural effect (`C_f`) |
|---|---|---|
| `store_stage` | stage write in slot 0 or 1 | **Stutter:** no change in old MSI/front-end state |
| `resolve_speculation` | confirm, squash suffix/read | **Stutter** |
| `store_issue` | issue confirmed FIFO head to MSI | **Exact oldest-head store issue** into existing old frontend |
| `load_forward` | speculate from youngest matching prior store | **Stutter** |
| `load_cache_capture` | speculate from an existing cached line | **Stutter** |
| `load_retire` | fast retirement of validated speculative read | **Exact correct-value read observation**, once older writes have completed |
| `load_replay` | restart stale read through MSI | **Exact old frontend read-issue** |

The typed contracts deliberately exclude forbidden behavior. For instance, `store_issue` is NOT allowed to stutter. The original *generic* interface is a union of all event kinds, so on its own it is too permissive for some families. The new per-family contracts close this gap **without changing the transition system**.

Two special ordering properties are retained as independent obligations:

1. A forwarded load takes the value of the **youngest earlier same-line write** (and not the older cache value).
2. A fast speculative read cannot retire while the earlier queue is nonempty, an older old-frontend command is busy, or confirmation is absent; the resulting observed value must equal the current coherent abstract value.

`tools/compositional_verify.py` checks these existing semantics-specific formulas directly rather than replacing them with coherence alone.

## 3. Standardized representation and actual sharing

We now export standard **SMT-LIB 2** instead of inventing a new serialization of a Boolean formula:

```smt
; simplified fragment — actual generated definitions contain the real formulas
(define-fun msi_inv () Bool ...)
(define-fun spec_inv () Bool ...)
(define-fun delta_store_issue () Bool ...)
(define-fun contract_store_issue () Bool ...)
(push 1)
(assert (and msi_inv spec_inv delta_store_issue
             (not contract_store_issue)))
(check-sat)  ; expected UNSAT
(pop 1)
```

`define-fun` gives **named, reusable formula DAG nodes** within a solver session. `push`/`pop` scopes obligations without losing shared declarations; `check-sat-assuming` with selector literals is another standard way to gate modules and obtain unsat assumptions. Neither is a magical proof of arbitrary plug-in compatibility.

Output under `artifacts/compositional_4c2l/` or `...4c3l/`:

- `shared_contracts.smt2`: declarations and reusable named definitions for all layers;
- `goals/*.smt2frag`: small incremental `push`/`assert`/`check-sat`/`pop` fragments;
- `all_contract_queries.smt2`: one **self-contained** SMT-LIB script checking all contract obligations in a single context;
- `sliced_queries/*.smt2`: standalone, dependency-minimal queries; each can be checked independently;
- `contract_manifest.json`: configuration, exact SHA-256 of original model sources, action counts and names, exact formula/context hashes, assumptions and solver results.

SMT-LIB does **not** define a universally portable `include` statement. The fragments are for the Python runner or concatenation with `shared_contracts.smt2`. The standalone queries repeat declarations because that is the portable format.

**Important:** A recorded `UNSAT` status plus the query is an auditable solver run, **not an independently checked proof certificate**. We do not yet produce Alethe proofs or other externally checked certificates.

## 4. Sliced proof dependencies for future changes

The default runner (`--execution sliced`) creates a **small solver context per contract family**, rather than letting every formula depend syntactically on every other family's transitions:

```text
shared declarations + I + J
       |
       +-- family store_issue: D_store_issue + C_store_issue -> 3 obligations
       +-- family load_retire: D_load_retire + C_load_retire -> 3 obligations
       +-- family load_forward: D_load_forward + C_load_forward -> 3 obligations
       +-- ... 4 other families
       +-- full partition / full interface union / inherited steps
```

**If only the `load_retire` transitions change while declarations and invariants remain identical**, the exact SMT formula and cache key for `store_issue` remain unchanged. That is *actual* contract-level caching, not merely saving the output of one monolithic formula. Hashes contain the complete relevant SMT context and solver options, so changed assumptions correctly invalidate proofs.

If a new feature changes shared state, `I`, `J`, the meaning of an architectural event, or an old transition, dependencies must be recalculated. Cache reuse across changed invariants is **not** automatically sound. New action names not classified into a family raise an error and refuse to report a complete proof.

The independent full-system induction (`--full-regression`) should continue to be run before each release; the compositional split is not permission to skip it forever.

## 5. Running it

From the Git repository root (Linux; Python 3 and `libz3.so.4`):

```bash
# Fastest development question: did the old store-issue contract survive?
python tools/compositional_verify.py --cores 4 --lines 2 --only store_issue

# Full modular suite, fresh checks, negative controls, inherited baseline,
# and independent full combined-system induction
python tools/compositional_verify.py --cores 4 --lines 2 --no-cache \
  --baseline --full-regression --check-mutants \
  --output-dir artifacts/compositional_4c2l
python tools/compositional_verify.py --cores 4 --lines 3 --no-cache \
  --baseline --full-regression --check-mutants \
  --output-dir artifacts/compositional_4c3l

# Re-run with caching enabled (exact formula/content + solver-version matching)
python tools/compositional_verify.py --cores 4 --lines 2 --baseline --full-regression

# Compare one-context DAG sharing against sliced, dependency-localized proofs
python tools/compositional_verify.py --cores 4 --lines 2 --execution shared --no-cache

# Regression checks
python -m unittest discover -s tests -v
```

**What the full suite checks:** initialization of `J`; inherited-step preservation of `I` and `J`; 3 checks per 7 new transition families; exact interface/partition equivalence; current read value, store forwarding and in-order retirement. That is **29 contract obligations** per configuration, in addition to optional baseline, full induction and mutants.

An illustrative single cold run on the four-core/two-line model took **1.76 s** in sliced mode and **1.80 s** in shared mode; these are not meaningful benchmark speedups. A warm exact-formula cache check took **0.028 s** because no SAT solving was necessary. The intended benefit of sliced mode is *avoiding recomputation of unchanged modules after a localized future edit*, not guaranteed faster cold solving.

Negative controls must return `SAT`:

- `unvalidated_read`: stale speculative read may retire;
- `premature_read`: load retires despite an older queued/busy store;
- `stuttering_store_issue`: a *synthetic harness mutation* pretends to issue a store but changes only speculative state. It satisfies the original generic interface's stuttering alternative, but violates the stricter `store_issue` contract. This mutant is **not** added to the actual cache model.

For the existing model, the seven families partition **76 transition schemas** for 4 cores × 2 lines, or **108** for 4 cores × 3 lines. The runner explicitly considers all four cores; it does **not** assume permutation symmetry without a proof.

## 6. Which alternatives are actually standard?

| Method | Problem it addresses | When to use it here | Implemented? |
|---|---|---|---|
| **SMT-LIB 2**, `define-fun`, incremental solving, named assertions | Portable formula representation and reuse | **Now:** contracts over integer data, arrays, guards and transitions | **Yes**, generated `.smt2` files |
| **Assume/guarantee contracts** | Composing independently checked transitions/subsystems | **Now:** speculative pipeline ↔ MSI architectural interface | **Yes**, under fixed assumptions |
| **Assumption literals / `check-sat-assuming`** | Toggle proof hypotheses, extract unsat assumptions | Future: many alternative ordering constraints | No, current runner uses `push/pop` |
| **Constrained Horn Clauses (CHCs)** / SPACER | Inductive reachability, synthesizing invariants, recursive modules | Future: parameterized reorder buffers or queues | No |
| **PDR / IC3** | Automatic strengthening of invariants | Future: stronger optimizations that break current `J` | No |
| **Craig interpolation** | Derive intermediate module assertions when split fails | Future: learn a contract between cache and speculation | No |
| **AIGER** | Compact bit-level sequential transition systems | Only if we move to a bit-vector/finite-state backend | No |
| **DIMACS CNF** | Plain Boolean SAT formula exchange | Poor match for symbolic `Int` + `Array` model without bit-blasting | No |
| **LRAT / FRAT** | Checkable **SAT** unsatisfiability proof traces | If independently certifying a Boolean backend | No |
| **Alethe / Carcara** | Portable-ish **SMT** proofs and an external checker | Future independent SMT proof validation | No |

### References (methodology, not project-specific proof results)

- [SMT-LIB language standard](https://smt-lib.org/language.shtml) — formal syntax, `define-fun`, incremental checking and assumptions.
- [Z3 Guide: fixedpoints and CHCs](https://microsoft.github.io/z3guide/docs/fixedpoints/intro/) — muZ / SPACER techniques.
- [FRAT and SAT proof elaboration](https://doi.org/10.46298/lmcs-18(2:3)2022) — checkable SAT proof artifacts.
- [Carcara/Alethe proof checking](https://link.springer.com/chapter/10.1007/978-3-031-30823-9_19) — SMT proof-format methodology.

## 7. An actionable future **speculative ordering** extension (not implemented)

Example: Allow **several speculative reads**, each tagged with a program-order index, while retaining the current MSI mechanism.

Create a **new** speculation module, don't touch the cached MSI proof:

1. Introduce program-order tags, a read dependency relation and a retirement pointer into the *new* speculative state.
2. Export a contract to MSI requiring that only confirmed **oldest not-yet-retired** memory operations may change architectural state. New speculative captures are stutters.
3. Express read-forwarding as a *nearest-prior matching store* contract, not a fixed slot-index assumption. This is crucial for a general reorder buffer.
4. Prove `I ∧ J_new ∧ D_new => I' ∧ J_new' ∧ C_new` for each changed transition family; recheck inherited-step framing.
5. Check a per-core retirement-order invariant and separately correct architectural read values. A coherent per-line history is not sufficient to infer cross-line sequential consistency.
6. Add **SAT negative controls** for early retirement, wrong-store forwarding, unvalidated reads and wrong-path stores escaping to coherence.
7. Only then consider `B`-entry queue induction (arbitrary `B`) or an entire sequential-consistency trace-refinement construction. Those results are *not* implied by our current 2-entry checks.

The design target is to be able to modify just the speculative-ordering module while **reusing the earlier MSI invariant and unrelated transition-family contracts**, subject to unchanged assumptions and explicit dependency rechecks.

## 8. Current proof boundary

**Established by SMT checking:** fixed four-core systems (two and three lines), existing bounded speculative reads/stores, inductive safety and the individual checked assumptions/interface properties, including stricter typed contracts added in this release.

**Not established:** a mechanically checked end-to-end SC trace refinement, all core counts, arbitrary queue capacities, deadlock freedom, liveness, hardware-level speculative execution semantics, or physical CPU correctness.

This release creates formal proof **interfaces** without changing the architecture. It does not claim that reducing a formula's file size makes verification faster; the valuable result is **local recomputation when only one verified contract changes**.
