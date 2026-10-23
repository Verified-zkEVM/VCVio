#!/usr/bin/env bash
# scripts/check-foxglove-isolation.sh
#
# Keep Foxglove (and the iris-lean it brings) out of every library but the bridge.
# `VCVioFoxglove` is the only library that may import `Foxglove.…`, `Iris.…` or
# `VCVioFoxglove.…`; core VCVio and its peers stay buildable without either.
#
# Usage:
#   scripts/check-foxglove-isolation.sh
#   scripts/check-foxglove-isolation.sh PATH [...]
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

if command -v rg >/dev/null 2>&1; then
  SEARCH=(rg --no-heading --line-number --color=never --glob '*.lean')
else
  SEARCH=(grep -RHn -E --include='*.lean')
fi

if (( $# > 0 )); then
  TARGETS=("$@")
else
  LIBS=(
    VCVio VCVioCslib ToMathlib LatticeCrypto HashSig Examples Extern VCVioWidgets
    VCVioTest LatticeCryptoTest HashSigTest Interop
  )
  TARGETS=()
  for lib in "${LIBS[@]}"; do
    TARGETS+=("$lib" "$lib.lean")
  done
fi

import_re='^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+(all[[:space:]]+)?(Foxglove|Iris|VCVioFoxglove)(\.|[[:space:]]|$)'
violations=0

for target in "${TARGETS[@]}"; do
  if [[ ! -e "$target" ]]; then
    continue
  fi
  matches="$({ "${SEARCH[@]}" "$import_re" "$target" 2>/dev/null || true; })"
  if [[ -n "$matches" ]]; then
    echo "ERROR: Foxglove leaked into '$target':" >&2
    echo "$matches" >&2
    echo >&2
    violations=$((violations + 1))
  fi
done

if (( violations > 0 )); then
  echo "Foxglove isolation check: ${violations} violation(s) found." >&2
  echo "Keep Foxglove-backed code under VCVioFoxglove/." >&2
  exit 1
fi

echo "Foxglove isolation check: OK."
