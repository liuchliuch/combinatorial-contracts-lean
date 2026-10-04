#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
stamp="${1:-$(date -u +%Y%m%dT%H%M%SZ)}"
out="$(dirname "$root")/combinatorial-contracts-source-${stamp}.tar.gz"
tar -czf "$out" --exclude='.lake' --exclude='.toolchain' --exclude='.git' -C "$(dirname "$root")" "$(basename "$root")"
sha256sum "$out"
printf '%s\n' "$out"
