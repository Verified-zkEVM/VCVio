#!/usr/bin/env bash
# scripts/test-pmf-boundary.sh
#
# Exercise check-pmf-boundary.sh against fixtures: the token boundary (including the `SPMF`
# versus `PMF` overlap and compound names such as `FinRatPMF`), the ceiling, and the ratchet.
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

# Counted: standalone `PMF`, standalone `SPMF` (once, not twice). Not counted: `FinRatPMF`.
printf '%s\n' \
  'def a : PMF Nat := pure 0' \
  'def b : SPMF Nat := pure 0' \
  'def c : FinRatPMF Nat := pure 0' \
  > Lib/Counted.lean
printf '%s\n' 'def d : Nat := 0' > Lib/Clean.lean

git add -A
git commit -qm 'fixture: base'
BASE="$(git rev-parse HEAD)"

"$CHECKER" --update-baseline >/dev/null
actual="$(awk -F'\t' '$1 == "Lib/Counted.lean" { print $2 }' scripts/pmf_boundary_baseline.tsv)"
if [[ "$actual" != "2" ]]; then
  echo "ERROR: expected 2 standalone occurrences in Lib/Counted.lean (PMF + SPMF), got '${actual:-0}'." >&2
  echo "       A count of 3 means the PMF inside SPMF was double-counted;" >&2
  echo "       a count of 4 means FinRatPMF was counted." >&2
  exit 1
fi

"$CHECKER" >/dev/null

# A file absent from the baseline has a ceiling of zero.
printf '%s\n' 'def e : PMF Nat := pure 0' > Lib/New.lean
if "$CHECKER" >/dev/null 2>&1; then
  echo 'ERROR: a new file introducing PMF coupling was not rejected by the ceiling.' >&2
  exit 1
fi
rm Lib/New.lean

# Ratchet: touching a coupled file without reducing it fails.
printf '%s\n' '-- touched, nothing removed' >> Lib/Counted.lean
git add -A
git commit -qm 'fixture: touch without reducing'
if "$CHECKER" --ratchet "$BASE" >/dev/null 2>&1; then
  echo 'ERROR: ratchet accepted a touched file that did not reduce its coupling.' >&2
  exit 1
fi

# A recorded hold exempts it from the ratchet.
printf 'Lib/Counted.lean\tfixture hold\n' > scripts/pmf_boundary_holds.tsv
"$CHECKER" --ratchet "$BASE" >/dev/null
: > scripts/pmf_boundary_holds.tsv

# Actually reducing the coupling passes.
printf '%s\n' \
  'def a : PMF Nat := pure 0' \
  'def c : FinRatPMF Nat := pure 0' \
  > Lib/Counted.lean
git add -A
git commit -qm 'fixture: reduce'
"$CHECKER" --ratchet "$BASE" >/dev/null

# An untouched coupled file is not required to shrink.
printf '%s\n' 'def f : Nat := 1' > Lib/Unrelated.lean
git add -A
git commit -qm 'fixture: unrelated change'
"$CHECKER" --ratchet "$BASE" >/dev/null

# Report mode is advisory: it must succeed even when the surface grew, and must name the delta.
printf '%s\n' 'def g : SPMF Nat := pure 0' > Lib/Grew.lean
git add -A
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

echo 'PMF/SPMF boundary fixtures: OK.'
