# Automatic speculative-ordering contract inference (v1.4)

From the repository root (`libz3.so.4` required):

```bash
python tools/infer_ordering_contracts.py --cores 4 --lines 2 --no-cache \
  --output-dir /tmp/contracts4x2
python tools/infer_ordering_contracts.py --cores 4 --lines 3 --no-cache \
  --output-dir /tmp/contracts4x3
python tools/infer_ordering_contracts.py --cores 4 --lines 2 \
  --previous-contracts /tmp/contracts4x2/inferred_contracts_manifest.json
python -m unittest discover -s tests -v
```

The learner selects contract effect types from a small human-specified architectural vocabulary (no invisible behavior is invented). Each family's actual MSI/speculation transition disjunction is queried independently. Failed grammar completeness stops synthesis; a change which weakens a previously certified contract stops the compatibility check. The 7 `*_coverage.smt2` scripts can be rerun with any SMT-LIB2-compatible solver supporting the modeled theories, e.g. `z3 file.smt2`.

**For release verification, also run:**

```bash
python tools/compositional_verify.py --cores 4 --lines 2 --no-cache \
  --baseline --full-regression --check-mutants
python tools/compositional_verify.py --cores 4 --lines 3 --no-cache \
  --baseline --full-regression --check-mutants
```

See [`AUTOMATIC_ORDERING_CONTRACTS.md`](AUTOMATIC_ORDERING_CONTRACTS.md) for proof semantics, trust boundaries and research limitations.
