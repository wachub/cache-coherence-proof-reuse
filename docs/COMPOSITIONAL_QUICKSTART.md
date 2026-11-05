# Compositional verification quickstart

Use `tools/compositional_verify.py` for an **external**, transition-preserving
verification layer around the unchanged combined speculative MSI model.

```bash
# Only the store-issue contract and its foundations (partial check)
python tools/compositional_verify.py --cores 4 --lines 2 --only store_issue

# Full contract proof plus previous MSI, full induction, and faulty mutants
python tools/compositional_verify.py --cores 4 --lines 2 --no-cache \
  --baseline --full-regression --check-mutants \
  --output-dir artifacts/compositional_4c2l
python tools/compositional_verify.py --cores 4 --lines 3 --no-cache \
  --baseline --full-regression --check-mutants \
  --output-dir artifacts/compositional_4c3l

python -m unittest discover -s tests -v
```

See [COMPOSITIONAL_VERIFICATION.md](COMPOSITIONAL_VERIFICATION.md) for the
assumption/guarantee theorem, seven exact architectural contracts, SMT-LIB
layers and query artifacts, caching safety, standard alternatives (CHCs,
PDR/IC3, Alethe, LRAT/FRAT), and future speculative-ordering extension.

**Do not modify the historical cache model to improve proof modularity.**
The 29 family/foundation obligations are additional checks; they do not
replace the baseline proof, independent combined induction, or the outstanding
full trace-level SC refinement task.
