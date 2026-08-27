#!/usr/bin/env bash
# scripts/test-pmf-boundary.sh
#
# Exercise check-pmf-boundary.sh against fixtures: the token boundary (including the `SPMF`
# versus `PMF` overlap and compound names such as `FinRatPMF`), comment/string exclusion, an empty
# migration surface, the ceiling, actual-base reporting, and the ratchet.
#
# The checker resolves its repo root from its own location, so the fixtures live in a throwaway
# git repository with the script copied into it. That exercises the real `git diff` path rather
# than a stub.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CHECKER_SRC="$REPO_ROOT/scripts/check-pmf-boundary.sh"
FIXTURE_REPO="$(mktemp -d)"
trap 'rm -rf "$FIXTURE_REPO"' EXIT

mkdir -p "$FIXTURE_REPO/scripts" "$FIXTURE_REPO/Lib"
cp "$CHECKER_SRC" "$FIXTURE_REPO/scripts/check-pmf-boundary.sh"
CHECKER="$FIXTURE_REPO/scripts/check-pmf-boundary.sh"

export PMF_BOUNDARY_LIBS="Lib"

cd "$FIXTURE_REPO"
git init -q .
git config user.email fixture@example.com
git config user.name Fixture

# Counted: standalone `PMF`, standalone `SPMF` (once, not twice).
# Not counted: `FinRatPMF`, comments/docstrings, nested comments, or string literals.
printf '%s\n' \
  'def a : PMF Nat := pure 0' \
  'def b : SPMF Nat := pure 0' \
  'def c : FinRatPMF Nat := pure 0' \
  '-- PMF and SPMF in a line comment' \
  '/-! PMF and SPMF in a module docstring -/' \
  '/- outer PMF /- nested SPMF -/ comment -/' \
  'def message := "PMF and SPMF in a string"' \
  > Lib/Counted.lean
printf '%s\n' 'def d : Nat := 0' > Lib/Clean.lean

"$CHECKER" --update-baseline >/dev/null
actual="$(awk -F'\t' '$1 == "Lib/Counted.lean" { print $2 }' scripts/pmf_boundary_baseline.tsv)"
if [[ "$actual" != "2" ]]; then
  echo "ERROR: expected 2 standalone occurrences in Lib/Counted.lean (PMF + SPMF), got '${actual:-0}'." >&2
  echo "       A count of 3 means the PMF inside SPMF was double-counted;" >&2
  echo "       a count of 4 means FinRatPMF was counted." >&2
  exit 1
fi

# Preserve a historical ceiling of two while the actual base tree has already fallen to one.
# This is the case that report/ratchet must compare correctly rather than treating the ceiling as
# the old source count.
awk '!/def b : SPMF/' Lib/Counted.lean > Lib/Counted.next
mv Lib/Counted.next Lib/Counted.lean
git add Lib/Counted.lean Lib/Clean.lean scripts/check-pmf-boundary.sh scripts/pmf_boundary_baseline.tsv
git commit -qm 'fixture: base with stale ceiling'
BASE="$(git rev-parse HEAD)"

"$CHECKER" >/dev/null

# A file absent from the baseline has a ceiling of zero.
printf '%s\n' 'def e : PMF Nat := pure 0' > Lib/New.lean
if "$CHECKER" >/dev/null 2>&1; then
  echo 'ERROR: a new file introducing PMF coupling was not rejected by the ceiling.' >&2
  exit 1
fi
rm Lib/New.lean

# Report must use the actual base tree (one), not its historical ceiling (two). Ratchet must reject
# a touched file whose actual source count did not decrease.
printf '%s\n' '-- touched, count unchanged' >> Lib/Counted.lean
git add Lib/Counted.lean
git commit -qm 'fixture: touch without reducing'
unchanged_report="$("$CHECKER" --report "$BASE" 2>&1)"
if ! grep -q 'this change does not move the retiring surface' <<< "$unchanged_report"; then
  echo 'ERROR: report mode compared against the ceiling instead of the actual base tree.' >&2
  echo "$unchanged_report" >&2
  exit 1
fi
if "$CHECKER" --ratchet "$BASE" >/dev/null 2>&1; then
  echo 'ERROR: ratchet accepted a touched file whose actual count did not decrease.' >&2
  exit 1
fi

# A recorded hold exempts it from the ratchet.
printf 'Lib/Counted.lean\tfixture hold\n' > scripts/pmf_boundary_holds.tsv
"$CHECKER" --ratchet "$BASE" >/dev/null
: > scripts/pmf_boundary_holds.tsv

# Actually reducing the coupling passes.
printf '%s\n' \
  'def c : FinRatPMF Nat := pure 0' \
  > Lib/Counted.lean
git add Lib/Counted.lean
git commit -qm 'fixture: reduce'
"$CHECKER" --ratchet "$BASE" >/dev/null

# An untouched coupled file is not required to shrink.
printf '%s\n' 'def f : Nat := 1' > Lib/Unrelated.lean
git add Lib/Unrelated.lean
git commit -qm 'fixture: unrelated change'
"$CHECKER" --ratchet "$BASE" >/dev/null

# Report mode is advisory: it must succeed even when the surface grew, and must name the delta.
printf '%s\n' \
  'def g : SPMF Nat := pure 0' \
  'def h : PMF Nat := pure 0' \
  > Lib/Grew.lean
git add Lib/Grew.lean
git commit -qm 'fixture: grow, with a reviewed baseline update'
"$CHECKER" --update-baseline >/dev/null
report="$("$CHECKER" --report "$BASE" 2>&1)"
if ! grep -q 'grows the retiring surface' <<< "$report"; then
  echo 'ERROR: report mode did not flag a growing surface.' >&2
  echo "$report" >&2
  exit 1
fi
if ! grep -q 'standalone occurrence(s) vs' <<< "$report"; then
  echo 'ERROR: report mode did not print an aggregate delta.' >&2
  exit 1
fi

# Reaching zero is success, including on systems with ripgrep installed.
mkdir -p CleanLib
printf '%s\n' 'def clean : Nat := 0' > CleanLib/Clean.lean
PMF_BOUNDARY_LIBS=CleanLib \
  PMF_BOUNDARY_BASELINE=scripts/empty_pmf_boundary_baseline.tsv \
  "$CHECKER" --update-baseline >/dev/null
PMF_BOUNDARY_LIBS=CleanLib \
  PMF_BOUNDARY_BASELINE=scripts/empty_pmf_boundary_baseline.tsv \
  "$CHECKER" >/dev/null

echo 'PMF/SPMF boundary fixtures: OK.'
