#!/usr/bin/env bash
# scripts/check-complexity-backend-isolation.sh
#
# Keep the optional concrete complexity backend below PolyFun and core VCVio.
# Generic proof libraries must not import `Complexitylib.…` or
# `VCVioComplexity.…`, and the root Lake package must not acquire a direct
# complexitylib requirement. Concrete instantiations belong to the isolated
# `VCVioComplexity/` package.
#
# Usage:
#   scripts/check-complexity-backend-isolation.sh
#   scripts/check-complexity-backend-isolation.sh PATH [...]
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
    VCVio ToMathlib LatticeCrypto HashSig Examples Extern VCVioWidgets
    VCVioTest LatticeCryptoTest HashSigTest Interop
  )
  TARGETS=(lakefile.lean)
  for lib in "${LIBS[@]}"; do
    TARGETS+=("$lib" "$lib.lean")
  done
fi

backend_import_re='^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+(all[[:space:]]+)?(Complexitylib|VCVioComplexity)(\.|[[:space:]]|$)'
backend_require_re='^[[:space:]]*require[[:space:]]+(complexitylib|VCVioComplexity)([[:space:]]|$)'
violations=0

for target in "${TARGETS[@]}"; do
  if [[ ! -e "$target" ]]; then
    continue
  fi
  matches="$({ "${SEARCH[@]}" "$backend_import_re" "$target" 2>/dev/null || true; } ; \
    { "${SEARCH[@]}" "$backend_require_re" "$target" 2>/dev/null || true; })"
  if [[ -n "$matches" ]]; then
    echo "ERROR: optional complexity backend leaked into '$target':" >&2
    echo "$matches" >&2
    echo >&2
    violations=$((violations + 1))
  fi
done

if (( violations > 0 )); then
  echo "Complexity backend isolation check: ${violations} violation(s) found." >&2
  echo "Keep concrete instances under VCVioComplexity/ and expose only PolyFun/VCVio interfaces." >&2
  exit 1
fi

echo "Complexity backend isolation check: OK."
