#!/usr/bin/env bash
# Exercise positive and negative cases for check-complexity-backend-isolation.sh.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CHECKER="$REPO_ROOT/scripts/check-complexity-backend-isolation.sh"
FIXTURE_DIR="$(mktemp -d)"
trap 'rm -rf "$FIXTURE_DIR"' EXIT

printf '%s\n' \
  'module' \
  'public import PolyFun.Realizability.Quantitative' \
  > "$FIXTURE_DIR/Allowed.lean"

printf '%s\n' \
  'module' \
  'import Complexitylib.Models.TuringMachine' \
  > "$FIXTURE_DIR/ComplexitylibViolation.lean"

printf '%s\n' \
  'module' \
  'public meta import VCVioComplexity.Backend.TuringMachine' \
  > "$FIXTURE_DIR/AdapterViolation.lean"

printf '%s\n' \
  'module' \
  'import all Complexitylib.Models.TuringMachine' \
  > "$FIXTURE_DIR/ComplexitylibAllViolation.lean"

printf '%s\n' \
  'module' \
  'public import all VCVioComplexity.Backend.TuringMachine' \
  > "$FIXTURE_DIR/AdapterAllViolation.lean"

printf '%s\n' \
  'import Lake' \
  'require complexitylib from git "https://example.invalid/complexitylib" @ "deadbeef"' \
  > "$FIXTURE_DIR/lakefile.lean"

printf '%s\n' \
  'import Lake' \
  'require VCVioComplexity from "VCVioComplexity"' \
  > "$FIXTURE_DIR/adapter-lakefile.lean"

"$CHECKER" "$FIXTURE_DIR/Allowed.lean"

for fixture in ComplexitylibViolation.lean AdapterViolation.lean \
    ComplexitylibAllViolation.lean AdapterAllViolation.lean lakefile.lean \
    adapter-lakefile.lean; do
  if "$CHECKER" "$FIXTURE_DIR/$fixture" >/dev/null 2>&1; then
    echo "ERROR: $fixture was not rejected." >&2
    exit 1
  fi
done

echo "Complexity backend isolation fixtures: OK."
