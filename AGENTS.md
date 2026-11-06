# Codex agent instructions — cache concurrency formal verification

Read `CODEX_PROJECT_HANDOFF.md` first, then `docs/PROOF_STATUS.md`, `docs/FAST_SOLVER_PLAYBOOK.md`, `SAT_SMT_HEURISTICS.md`, and `experiments/09_combined_speculative_reads_writes/README.md`.

## Project scope
- Maintain and extend an **abstract asynchronous directory-based MSI model** and its SAT/SMT proof obligations. Do not switch to RTL, hardware synthesis, device implementations, or physical PPA work without being asked.
- Current baseline: four cores, two or three cache lines, ordinary Read/Store/atomic CAS, **two private speculative stores plus one younger speculative read per core**.
- Preserve historical experiments and Git tags. Add new features in their own experiment directories or in clearly delimited extensions.

## Verification rules
- Distinguish **machine-checked inductive safety** from an **unmechanized sequential-consistency trace argument**. Never assert a full SC refinement theorem until actually mechanized.
- Inherit old invariants only after checking old-step framing, new-step preservation and the architectural interface. New or modified transitions require new obligations.
- Unconfirmed speculative stores must remain private in the current model. Confirmed stores issue FIFO. A load must forward from the youngest earlier matching queued store, and cannot retire while an older operation is still pending (`busy=true`). Validate captured values or replay.
- CAS compares data values; symbolic version tokens track freshness and permit equal payloads/ABA. Explicitly frame unrelated state on every transition.
- For each feature, require a reachable successful SAT witness and a mutant that yields a SAT violation. `UNSAT` means no violating inductive step under the model's assumptions; `unknown` or timeout is not a proof.
- Report exact cores, lines, queue depths, solver version, relevant assumptions, proof obligation results, and what is **not** proved (liveness, RTL, arbitrary-size systems).

## Commands (from repository root)
```bash
python tools/fast_verify.py --cores 4 --lines 2 --verify-baseline --full-regression --check-mutants --no-cache
python tools/fast_verify.py --cores 4 --lines 3 --verify-baseline --full-regression --check-mutants --no-cache
python -m unittest discover -s tests -v
```

Use `tools/fast_verify.py` with shared sessions/caching for iteration; fresh `--no-cache` baseline + full-induction checks for a release. Cache entries may only be reused for identical SMT formulas and solver settings. Inspect `mutants.detected`, not just the `passed` field for deliberately broken mutants.

## Work approach
1. Inspect the exact source, proof formula, and previous proof logs before edits.
2. State the *smallest* semantics change and the invariant/interface delta.
3. Write and check isolated new obligations; localize any SAT transition.
4. Rerun full regression; record positive witnesses, broken mutants and measurements.
5. Commit only after successful fresh checks; document unresolved proof gaps explicitly.

Priority research direction: complete the missing machine-checked SC trace refinement; then queue-size generalization and more speculative reads. Do not falsely describe proposed solver heuristics as already implemented.

## v1.3 compositional verification (current priority)

**Current instruction: do not add cache-model features unless explicitly asked.**
Use `docs/COMPOSITIONAL_VERIFICATION.md`, `docs/COMPOSITIONAL_QUICKSTART.md`,
and `tools/compositional_verify.py` to improve proof reuse around the **unchanged**
combined model. The contract layer groups existing actions into seven typed
architectural effects; unfamiliar action names must cause a hard failure,
not silent omission. Separate *typed* `store_issue` / `load_retire` / `load_replay`
contracts from the older interface's broad union: the latter is too weak to
rule out every event misclassification. Verify the abstract interface and
retirement order independently of per-line MSI safety.

When optimizing proof code, prefer dependency-sliced SMT-LIB contexts over
adding new processor behaviors. If modifying a shared invariant, state layout
or contract, invalidate affected proof caches. Emit standalone SMT-LIB queries,
source SHA-256 manifest, regression output, and negative controls. Always
recheck both 4-core / 2-line and 4-core / 3-line models with `--no-cache
--baseline --full-regression --check-mutants` before release. Neither `UNSAT`
nor formula sharing by itself proves an end-to-end SC trace refinement.

## v1.4 — inferred ordering contracts, no cache implementation changes

- First read `docs/AUTOMATIC_ORDERING_CONTRACTS.md` and `docs/CONTRACT_SYNTHESIS_QUICKSTART.md`.
- Use `tools/infer_ordering_contracts.py` to **infer** the transition-family-to-architectural-event classification from the actual unchanged transition formulas. Never guess it from family names alone.
- The four architectural-effect templates are an explicit specification and are not synthesized from nothing. An inferred contract is a solver-checked one-step **overapproximation** of actual architectural effects within the supplied effect vocabulary only under the inherited invariants; it does not by itself establish sequential consistency.
- Always use `--previous-contracts` for extension compatibility; don't silently broaden a previously certified contract. A changed shared abstraction requires rebuilding/revalidating the reference contracts.
- An exact old proof may be reused only when its local SMT context, obligation and solver settings remain unchanged. New/changed deltas always require fresh Z3 checks and the full combined induction as a release gate.
- Continue to run the deliberately broken load-retirement and store-issue tests. Do not modify any historical files under `experiments/` to improve contract synthesis.

## v1.5 — progress and fairness analysis (unchanged cache model)

Read `docs/LIVENESS_PROGRESS_ANALYSIS.md`. Run `python tools/liveness_verify.py --cores 4 --lines 2 3 --output-dir /tmp/liveness_checks`. The new verifier checks enabledness and a decreasing transaction rank; it does NOT prove unconditional eventual request completion. Keep these distinctions explicit:

- Deadlock freedom / enabled progress requires excluding fresh client issues so the property is nonvacuous.
- Internal transaction rank descent proves no infinite *servicing-only* livelock, but scheduler fairness is needed for temporal progress.
- There is a **reachable symbolic-payload completion stall** in the inherited immutable `payload(version)` abstraction. Do not claim full read/write/CAS termination.
- There is a **reachable weak-fair starvation lasso** for a queued read while two other cores alternate ownership. Do not claim starvation freedom under weak fairness; strong fairness of arbitration or a fair directory algorithm is needed.
- Use generated SMT-LIB proofs, negative controls, and exact 4-core/2-line and 4-core/3-line configurations. Historical source files under `experiments/` must not be changed as part of this verification-only task.

## Fair-progress experimental branch (v1.7)

The `proof/temporal-fairness-v1.7` branch retains all previous commits and
keeps the v1.6 transition semantics unchanged. Read `TEMPORAL_FAIRNESS_v1_7.md`
before extending liveness. Reproduce with:

```bash
python tools/temporal_v17_verify.py --cores 4 --lines 2 3
python tools/fair_lasso_v17.py --max-cores 4
python -m unittest discover -s tests -q
```

The checked SMT queries are concrete one-step liveness premises, not an
independent global temporal model-checker certificate. The separate finite
abstract lasso checker is not a machine-checked refinement of the full model.
Do not claim that the original concrete infinite-state temporal theorem has
already been independently machine checked.
