#!/usr/bin/env bash
# Invoke only after authors freeze all proof/config sources and independent
# semantic reviewers accept the exact inventory. Never clean shared packages.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$PWD/.toolchain/lean-4.24.0-linux/bin:$PATH"
python scripts/snapshot.py --verify | tee logs/release-prefreeze-validation.json
python scripts/check_project.py --release | tee logs/release-source-preflight.json
python - <<'PY'
import json,hashlib
from pathlib import Path
p=Path('docs/release-candidate/semantic-certificate.json')
if not p.exists():raise SystemExit('BLOCKED: independent semantic certificate absent')
c=json.loads(p.read_text())
if c.get('all_paper_results_accepted') is not True:raise SystemExit('BLOCKED: full semantic acceptance absent')
h=hashlib.sha256(Path('docs/release-candidate/source-inventory.json').read_bytes()).hexdigest()
if c.get('source_inventory_sha256')!=h:raise SystemExit('BLOCKED: semantic review inventory differs')
PY
lake clean combinatorial-contracts
lake build CombinatorialContracts 2>&1 | tee logs/release-clean-build.log
lake env lean scripts/AxiomAudit.lean 2>&1 | tee logs/release-origin-axioms.log
lake env lean --trust=0 scripts/ReleaseChecks.lean 2>&1 | tee logs/release-trust-zero-allimports.log
python scripts/semantic_checks.py | tee logs/release-semantic-regression.json
sha256sum -c originals/SHA256SUMS | tee logs/release-original-validation.log
sha256sum -c originals/dependencies/dfgr26/SHA256SUMS | tee -a logs/release-original-validation.log
python scripts/snapshot.py --verify | tee logs/release-final-source-validation.json
printf '%s\n' 'All mechanical release gates passed for frozen inventory.'
