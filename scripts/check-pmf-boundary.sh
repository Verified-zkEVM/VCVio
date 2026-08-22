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

if command -v rg >/dev/null 2>&1; then
  rg --pcre2 --count-matches --glob '*.lean' "$PATTERN" "${LIBS[@]}" \
    | sort | sed $'s/:/\t/' > "$CURRENT"
else
  # GitHub's lean-action image does not guarantee ripgrep. Keep a dependency-free fallback whose
  # token boundary agrees with the PCRE expression above: only alphabetic neighbours suppress a
  # match, so `_PMF`, `PMF.` and similar standalone uses still count.
  while IFS= read -r -d '' file; do
    count="$(awk '
      {
        original = $0
        offset = 0
        rest = original
        while ((position = index(rest, "PMF")) != 0) {
          absolute = offset + position
          before = absolute == 1 ? "" : substr(original, absolute - 1, 1)
          after = substr(original, absolute + 3, 1)
          if (before !~ /[[:alpha:]]/ && after !~ /[[:alpha:]]/) {
            total++
          }
          offset = absolute + 2
          rest = substr(original, offset + 1)
        }
      }
      END { print total + 0 }
    ' "$file")"
    if (( count > 0 )); then
      printf '%s\t%s\n' "$file" "$count"
    fi
  done < <(find "${LIBS[@]}" -type f -name '*.lean' -print0) | sort > "$CURRENT"
fi

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
