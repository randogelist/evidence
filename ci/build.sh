#!/usr/bin/env bash
set -euo pipefail
mkdir -p logs
lean --version | tee logs/version.log
lake env lean --version
for module in ZetaBetaHankel.ExactModel ZetaBetaHankel.USPDCore ZetaBetaHankel.AdjustedBlueprint ZetaBetaHankel.Zeta357CandidateN0 ZetaBetaHankel.Zeta357Chain ZetaBetaHankel.Audit; do
  lake build "$module" 2>&1 | tee "logs/${module}.log"
done
python3 ci/audit.py
