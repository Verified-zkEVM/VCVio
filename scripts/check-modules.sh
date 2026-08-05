#!/usr/bin/env bash

# Check module-scope invariants for active Lean libraries and tests.

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

source_roots=(
  ToMathlib VCVio LatticeCrypto HashSig Extern Examples VCVioWidgets
  VCVioTest LatticeCryptoTest HashSigTest
)
root_modules=(
  ToMathlib.lean VCVio.lean LatticeCrypto.lean HashSig.lean Extern.lean
  Examples.lean VCVioWidgets.lean VCVioTest.lean LatticeCryptoTest.lean
)

status=0

while IFS= read -r file; do
  if ! rg -q '^module([[:space:]]|$)' "$file"; then
    echo "ERROR: $file does not enable module mode with a 'module' command." >&2
    status=1
  fi

  if ! rg -q '^(@\[expose\][[:space:]]+)?public([[:space:]]+meta)?[[:space:]]+section([[:space:]]|$)' "$file"; then
    case "$file" in
      VCVio/CryptoFoundations/Fischlin.lean)
        # Deliberate import-only internal umbrella.
        ;;
      *)
        echo "ERROR: $file does not place declarations in a public or public-meta section." >&2
        status=1
        ;;
    esac
  fi
done < <(rg --files "${source_roots[@]}" --glob '*.lean')

for file in "${root_modules[@]}"; do
  if ! rg -q '^module([[:space:]]|$)' "$file"; then
    echo "ERROR: $file does not enable module mode." >&2
    status=1
  fi
  if rg -n '^(meta[[:space:]]+)?import[[:space:]]' "$file"; then
    echo "ERROR: $file contains a non-public umbrella import." >&2
    status=1
  fi
done

if rg -n 'backward\.(privateInPublic|proofsInPublic)' \
    "${source_roots[@]}" "${root_modules[@]}" --glob '*.lean'; then
  echo "ERROR: transitional module-system backward-compatibility options are forbidden." >&2
  status=1
fi

if (( status != 0 )); then
  exit "$status"
fi

echo "✓ Active Lean sources use explicit module scopes."
