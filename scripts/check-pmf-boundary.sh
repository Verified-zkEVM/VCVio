#!/usr/bin/env bash
# scripts/check-pmf-boundary.sh
#
# Keep direct PMF coupling from growing while VCVio moves its denotational boundary to
# Mathlib measures. The baseline is a per-file lexical ceiling for bare `PMF` occurrences;
# `SPMF` and `FinRatPMF` do not count. A file absent from the baseline has a ceiling of zero.
#
# This is intentionally a migration guard, not a claim that every baseline occurrence is bad.
# Compatibility adapters, executable finite distributions, and the existing discrete proof
# facade still use PMF. Lower counts are always accepted.
#
# Usage:
#   scripts/check-pmf-boundary.sh
#   scripts/check-pmf-boundary.sh --update-baseline
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

BASELINE="scripts/pmf_boundary_baseline.tsv"
LIBS=(VCVio ToMathlib LatticeCrypto HashSig Examples VCVioWidgets)
PATTERN='(?<![[:alpha:]])PMF(?![[:alpha:]])'
CURRENT="$(mktemp "${TMPDIR:-/tmp}/vcvio-pmf-boundary.XXXXXX")"
trap 'rm -f "$CURRENT"' EXIT

rg --pcre2 --count-matches --glob '*.lean' "$PATTERN" "${LIBS[@]}" \
  | sort | sed $'s/:/\t/' > "$CURRENT"

if [[ "${1:-}" == "--update-baseline" ]]; then
  cp "$CURRENT" "$BASELINE"
  echo "PMF boundary: updated $BASELINE."
  exit 0
fi

if (( $# > 0 )); then
  echo "PMF boundary: unknown argument '$1'." >&2
  exit 2
fi

if [[ ! -f "$BASELINE" ]]; then
  echo "PMF boundary: missing $BASELINE; run with --update-baseline." >&2
  exit 2
fi

declare -A allowed
while IFS=$'\t' read -r file count; do
  [[ -z "$file" ]] && continue
  allowed["$file"]="$count"
done < "$BASELINE"

violations=0
while IFS=$'\t' read -r file count; do
  [[ -z "$file" ]] && continue
  limit="${allowed[$file]:-0}"
  if (( count > limit )); then
    echo "ERROR: $file has $count bare PMF occurrence(s); baseline ceiling is $limit." >&2
    violations=$((violations + 1))
  fi
done < "$CURRENT"

if (( violations > 0 )); then
  echo "PMF boundary: $violations file(s) increased direct PMF coupling." >&2
  echo "Use Measure/Kernel for new semantics, or update the baseline with explicit review." >&2
  exit 1
fi

echo "PMF boundary: OK."
