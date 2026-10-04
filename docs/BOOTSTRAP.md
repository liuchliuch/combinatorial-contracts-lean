# Reproduce from a source-only archive

No sibling project, local cache path, or bundled symlink is required. The archive contains the sources, original papers, pins, scripts, ledger and certificates. Toolchain/dependency/build caches are deliberately omitted.

## Fresh Linux x86-64 installation

Use Bash with `curl`, `git`, Python 3, `tar`, and `zstd` available. Start inside the extracted `combinatorial-contracts-lean` directory. These commands fetch the official pinned Lean release and materialize the exact package revisions already recorded in `lake-manifest.json`:

```bash
set -euo pipefail
# Fresh-install route only: never extract through an existing shared symlink.
test ! -e .toolchain && test ! -L .toolchain
mkdir -p .toolchain
archive="$(mktemp --suffix=.tar.zst)"
curl -fL \
  https://github.com/leanprover/lean4/releases/download/v4.24.0/lean-4.24.0-linux.tar.zst \
  -o "$archive"
printf '%s  %s\n' \
  b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec \
  "$archive" | sha256sum -c -
tar --zstd -xf "$archive" -C .toolchain
export PATH="$PWD/.toolchain/lean-4.24.0-linux/bin:$PATH"
lean --version
lean --githash
lake exe cache get
lake build CombinatorialContracts
python scripts/snapshot.py --verify
```

The SHA-256 above matches both the archive used for this release and the checksum published in the [official Lean v4.24.0 release assets](https://github.com/leanprover/lean4/releases/expanded_assets/v4.24.0). The toolchain commit must be `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. Mathlib must be `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

Lake reads the existing lockfile and fetches missing packages at their locked revisions. Do not run `lake update`: it is unnecessary for this reproduction and can change pins. `lake exe cache get` downloads matching compiled mathlib dependencies; it does not establish proof trust. The subsequent trust-zero replay rechecks imported proofs.

To repeat the complete certified validation pipeline:

```bash
scripts/release_verify.sh
```

That script cleans only this project's outputs, rebuilds all modules, runs the origin-complete transitive axiom audit and trust-zero all-import replay, checks regressions and validates frozen hashes and package pins. Existing `release-*` logs are overwritten by your new run. Preserve a copy first if you want the original logs as well. Original source and certificates are unchanged.

## Reuse an existing verified installation

Instead of fetching another toolchain, create `.toolchain/lean-4.24.0-linux` as a symlink to any already installed **official Linux x86-64 Lean 4.24.0** directory containing `bin/lean`. For example, with an existing elan installation and this project's `lean-toolchain` file:

```bash
elan toolchain install leanprover/lean4:v4.24.0
mkdir -p .toolchain
ln -s "$(dirname "$(dirname "$(elan which lean)")")" \
  .toolchain/lean-4.24.0-linux
export PATH="$PWD/.toolchain/lean-4.24.0-linux/bin:$PATH"
lake exe cache get
python scripts/snapshot.py --verify
```

For optional package-cache reuse, `.lake/packages` may point to an existing directory with the same nine locked package revisions and clean tracked worktrees. `snapshot.py --verify` checks every revision/tree and the compiler binary hash. Never run an unqualified `lake clean` against shared caches. The supplied script uses `lake clean combinatorial-contracts` only.

## Other operating systems

The Lean sources and Lake pins are portable. Install Lean 4.24.0 for your platform and run `lake exe cache get` followed by `lake build CombinatorialContracts`. However, the recorded compiler **binary** checksum belongs to Linux x86-64; another platform's executable will correctly fail that exact binary-identity check. Use Linux x86-64 to reproduce the original certificate without changing the inventory. A cross-platform revalidation should produce its own inventory/certificate rather than silently overwrite the original one.

## Recovery

The source archive is the durable artifact. Runtime symlinks, `.lake` and `.toolchain` directories are excluded. `RECOVERY.json` records the latest confirmed external checkpoint when it was last updated; the archive itself remains immutable after its published checksum is assigned.
