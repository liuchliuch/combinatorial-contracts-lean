#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$PWD/.toolchain/lean-4.24.0-linux/bin:$PATH"
python scripts/check_project.py --release | tee logs/source-preflight.json
sha256sum -c originals/SHA256SUMS | tee logs/original-validation.log
lake build CombinatorialContracts 2>&1 | tee logs/all-module-build.log
lake env lean scripts/AxiomAudit.lean 2>&1 | tee logs/transitive-axiom-audit.log
lake env lean --trust=0 scripts/AxiomAudit.lean 2>&1 | tee logs/trust-zero-all-imports.log
sha256sum CombinatorialContracts.lean CombinatorialContracts/*.lean lakefile.toml lake-manifest.json lean-toolchain > logs/verified-source-hashes.txt
