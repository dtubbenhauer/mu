#!/bin/sh
# Reproduce the pinned Lean build and its logical dependency audit.
set -eu
cd "$(dirname "$0")"
webmu_toolchain=$(cat lean-toolchain)
webmu_toolchain_dir=${ELAN_HOME:-$HOME/.elan}/toolchains/$(printf '%s' "$webmu_toolchain" | sed 's/:/---/; s,/,--,g')
if [ -x "$webmu_toolchain_dir/bin/lake" ]; then
  PATH="$webmu_toolchain_dir/bin:$PATH"
  export PATH
fi
lean --version
lake build
lake env lean AuditIndependentMain.lean
