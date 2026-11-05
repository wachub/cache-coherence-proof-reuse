#!/bin/sh
set -eu
cd "$(dirname "$0")"
python sc_msi_4core_verifier.py --cores 4 --lines 2 --output-dir base4_2
python sc_msi_4core_verifier.py --cores 4 --lines 3 --output-dir base4_3
python combined_speculative_model.py --cores 4 --lines 2 --output-dir delta4_2
python combined_speculative_model.py --cores 4 --lines 3 --output-dir delta4_3
python full_regression.py 4 2 full4_2
python full_regression.py 4 3 full4_3
python mutant_checks.py
python witnesses.py
