#!/usr/bin/env bash
# scripts/check-polyfun-boundary.sh
#
# Enforce the public package boundary between VCVio and PolyFun. A downstream
# package must never use `import all PolyFun.…`: doing so makes VCVio depend on
# declarations that PolyFun intentionally kept private and turns a module
# migration into an accidental API expansion.
#
# Exit code:
#   0 — no violations.
#   1 — at least one violation; offending lines are printed to stderr.
#
# Usage:
#   scripts/check-polyfun-boundary.sh              # check repository libraries
#   scripts/check-polyfun-boundary.sh PATH [...]   # check explicit fixtures/paths
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

if command -v rg >/dev/null 2>&1; then
  SEARCH=(rg --no-heading --line-number --color=never --glob '*.lean')
else
  SEARCH=(grep -RHn -E --include='*.lean')
fi

LIBS=(
  VCVio ToMathlib LatticeCrypto HashSig Examples Extern VCVioWidgets
  VCVioTest LatticeCryptoTest HashSigTest Interop
)

if (( $# > 0 )); then
  TARGETS=("$@")
else
  TARGETS=()
  for lib in "${LIBS[@]}"; do
    TARGETS+=("$lib" "$lib.lean")
  done
fi

forbidden_re='^[[:space:]]*(meta[[:space:]]+)?import[[:space:]]+all[[:space:]]+PolyFun(\.|[[:space:]]|$)'
violations=0

for target in "${TARGETS[@]}"; do
  if [[ ! -e "$target" ]]; then
    continue
  fi
  matches="$("${SEARCH[@]}" "$forbidden_re" "$target" 2>/dev/null || true)"
  if [[ -n "$matches" ]]; then
    echo "ERROR: '$target' reaches through PolyFun's public module boundary:" >&2
    echo "$matches" >&2
    echo >&2
    violations=$((violations + 1))
  fi
done

if (( violations > 0 )); then
  echo "PolyFun boundary check: ${violations} violation(s) found." >&2
  echo "Add a public PolyFun law or API declaration, then use a plain/public import." >&2
  exit 1
fi

echo "PolyFun boundary check: OK."
