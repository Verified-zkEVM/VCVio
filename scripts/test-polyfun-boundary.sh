#!/usr/bin/env bash
# scripts/test-polyfun-boundary.sh
#
# Exercise the positive and negative cases for check-polyfun-boundary.sh.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CHECKER="$REPO_ROOT/scripts/check-polyfun-boundary.sh"
FIXTURE_DIR="$(mktemp -d)"
trap 'rm -rf "$FIXTURE_DIR"' EXIT

printf '%s\n' \
  'module' \
  'public import PolyFun.PFunctor.Basic' \
  'import all VCVio.OracleComp.Basic' \
  > "$FIXTURE_DIR/Allowed.lean"

printf '%s\n' \
  'module' \
  'import all PolyFun.PFunctor.Basic' \
  > "$FIXTURE_DIR/PlainViolation.lean"

printf '%s\n' \
  'module' \
  'meta import all PolyFun.PFunctor.Basic' \
  > "$FIXTURE_DIR/MetaViolation.lean"

"$CHECKER" "$FIXTURE_DIR/Allowed.lean"

if "$CHECKER" "$FIXTURE_DIR/PlainViolation.lean" >/dev/null 2>&1; then
  echo 'ERROR: plain `import all PolyFun` fixture was not rejected.' >&2
  exit 1
fi

if "$CHECKER" "$FIXTURE_DIR/MetaViolation.lean" >/dev/null 2>&1; then
  echo 'ERROR: `meta import all PolyFun` fixture was not rejected.' >&2
  exit 1
fi

echo 'PolyFun boundary fixtures: OK.'
