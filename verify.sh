#!/usr/bin/env bash
# Build, audit every theorem's axioms, scan for admitted proofs, and check ledger citations.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p verification
lake build 2>&1 | tee verification/build.log
lake env lean scripts/AxiomAudit.lean 2>&1 | tee verification/axiom_audit.log
grep -q "Entropic: .* theorems; 0 with nonstandard axioms" verification/axiom_audit.log
grep -q "Entropic.EFT: .* theorems; 0 with nonstandard axioms" verification/axiom_audit.log
python3 tools/scan_sources.py
lake env lean scripts/CiteCheck.lean 2>&1 | tail -1 | tee verification/citecheck.log
grep -q "unresolved 0" verification/citecheck.log
echo "verify.sh: all checks passed"
