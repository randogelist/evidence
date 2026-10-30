#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
mkdir -p logs
stage=preflight
trap 'rc=$?; printf "FULL_CHAIN_BUILD=FAIL\nFAILURE_STAGE=%s\nEXIT_CODE=%s\n" "$stage" "$rc" > logs/ci-status.txt; exit "$rc"' ERR

lean --version > logs/version.log 2>&1
lake env lean --version > logs/lake-lean-version.log 2>&1
cat logs/version.log
python3 ci/audit.py --preflight

stage=build
python3 ci/compile.py 2>&1 | tee logs/full-build.log

# A fresh direct Lean invocation emits exactly this audit file's reports;
# cached Lake output is never accepted as the final theorem audit.
stage=independent-audit
timeout 1200 lake env lean -j2 ZetaBetaHankel/EvidenceAudit.lean > logs/final-audit.log 2>&1
cat logs/final-audit.log

stage=validate-audit
python3 ci/audit.py 2>&1 | tee logs/audit-validation.log
printf 'FULL_CHAIN_BUILD=PASS\nAXIOM_AUDIT=PASS_STANDARD_ONLY\nSCOPE=THEOREM_STATEMENTS_WITH_EXPLICIT_PREMISES\n' | tee logs/ci-status.txt
