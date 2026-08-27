#!/usr/bin/env bash
# scripts/check-pmf-boundary.sh
#
# Keep finite-distribution coupling from growing while VCVio moves its denotational boundary to
# Mathlib measures. The baseline is a per-file lexical ceiling for standalone `PMF` and `SPMF`
# occurrences; compound names such as `FinRatPMF` do not count. A file absent from the baseline
# has a ceiling of zero.
#
# `SPMF` counts because `SPMF := OptionT PMF`, so every use is a transitive PMF dependency.
# Counting only bare `PMF` measured well under half of the real exposure.
#
# Upstream is retiring `PMF`: the pinned Mathlib already deprecates `PMF.bernoulli` and
# `PMF.binomial` in favour of measure-valued replacements in `ProbabilityTheory`. This guard exists
# to make that retirement visible and monotone. It has three modes:
#
#   * ceiling (default) -- hard gate. No file may exceed its baseline count, and a file absent from
#                          the baseline has an allowance of zero, so new coupling cannot appear
#                          without an explicit, reviewable baseline change.
#   * report            -- advisory. Prints the aggregate and per-file delta against a base ref.
#                          Non-blocking by design: restructuring work legitimately moves counts
#                          between files, and a PR that merely touches a coupled file for an
#                          unrelated reason should not be forced to reduce it.
#   * ratchet           -- opt-in hard gate for a deliberate reduction pass: every touched file
#                          that still carries coupling must decrease, unless
#                          scripts/pmf_boundary_holds.tsv records a reason. Not wired into CI.
#
# The ceiling is not a claim that every baseline occurrence is bad: compatibility adapters,
# executable finite distributions, and the existing discrete proof facade still use PMF/SPMF.
# Lower counts are always accepted.
#
# Usage:
#   scripts/check-pmf-boundary.sh                 # ceiling check
#   scripts/check-pmf-boundary.sh --report [REF]  # ceiling + advisory delta vs REF (default origin/main)
#   scripts/check-pmf-boundary.sh --ratchet [REF] # ceiling + require touched files to decrease
#   scripts/check-pmf-boundary.sh --update-baseline
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

BASELINE="${PMF_BOUNDARY_BASELINE:-scripts/pmf_boundary_baseline.tsv}"
HOLDS="${PMF_BOUNDARY_HOLDS:-scripts/pmf_boundary_holds.tsv}"
# Overridable so scripts/test-pmf-boundary.sh can exercise this against fixtures.
if [[ -n "${PMF_BOUNDARY_LIBS:-}" ]]; then
  read -r -a LIBS <<< "$PMF_BOUNDARY_LIBS"
else
  LIBS=(VCVio ToMathlib LatticeCrypto HashSig Examples VCVioWidgets)
fi
PATTERN='(?<![[:alpha:]])(?:SPMF|PMF)(?![[:alpha:]])'
CURRENT="$(mktemp "${TMPDIR:-/tmp}/vcvio-pmf-boundary.XXXXXX")"
trap 'rm -f "$CURRENT"' EXIT

if command -v rg >/dev/null 2>&1; then
  rg --pcre2 --count-matches --glob '*.lean' "$PATTERN" "${LIBS[@]}" \
    | sort | sed $'s/:/\t/' > "$CURRENT"
else
  # GitHub's lean-action image does not guarantee ripgrep. Keep a dependency-free fallback whose
  # token boundary agrees with the PCRE expression above: only alphabetic neighbours suppress a
  # match, so `_PMF`, `PMF.` and similar standalone uses still count. `SPMF` is scanned before
  # `PMF` and the alphabetic lookbehind stops the `PMF` inside it from counting twice.
  while IFS= read -r -d '' file; do
    count="$(awk '
      {
        original = $0
        tokens[1] = "SPMF"
        tokens[2] = "PMF"
        for (tokenIndex = 1; tokenIndex <= 2; tokenIndex++) {
          token = tokens[tokenIndex]
          offset = 0
          rest = original
          while ((position = index(rest, token)) != 0) {
            absolute = offset + position
            before = absolute == 1 ? "" : substr(original, absolute - 1, 1)
            after = substr(original, absolute + length(token), 1)
            if (before !~ /[[:alpha:]]/ && after !~ /[[:alpha:]]/) {
              total++
            }
            offset = absolute + length(token) - 1
            rest = substr(original, offset + 1)
          }
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
  echo "PMF/SPMF boundary: updated $BASELINE."
  exit 0
fi

MODE="ceiling"
COMPARE_BASE="origin/main"
if [[ "${1:-}" == "--ratchet" || "${1:-}" == "--report" ]]; then
  MODE="${1#--}"
  if [[ -n "${2:-}" ]]; then
    COMPARE_BASE="$2"
    shift
  fi
  shift
fi

if (( $# > 0 )); then
  echo "PMF/SPMF boundary: unknown argument '$1'." >&2
  exit 2
fi

if [[ ! -f "$BASELINE" ]]; then
  echo "PMF/SPMF boundary: missing $BASELINE; run with --update-baseline." >&2
  exit 2
fi

CHANGED="$(mktemp "${TMPDIR:-/tmp}/vcvio-pmf-changed.XXXXXX")"
trap 'rm -f "$CURRENT" "$CHANGED"' EXIT

BASE_COUNTS="$(mktemp "${TMPDIR:-/tmp}/vcvio-pmf-basecounts.XXXXXX")"
trap 'rm -f "$CURRENT" "$CHANGED" "$BASE_COUNTS"' EXIT

if [[ "$MODE" != "ceiling" ]]; then
  if git rev-parse --verify --quiet "$COMPARE_BASE" >/dev/null; then
    git diff --name-only "$COMPARE_BASE"...HEAD -- "${LIBS[@]}" > "$CHANGED"
    # The base ref's own recorded counts, so the report compares against what was actually
    # committed there rather than against the working baseline.
    git show "$COMPARE_BASE:$BASELINE" > "$BASE_COUNTS" 2>/dev/null || : > "$BASE_COUNTS"
  else
    echo "PMF/SPMF boundary: base ref '$COMPARE_BASE' not found; ceiling only." >&2
    MODE="ceiling"
  fi
fi

[[ -f "$HOLDS" ]] || : > "$HOLDS"

# The comparison lives in awk rather than bash: associative arrays are native there, and the
# macOS system bash is 3.2, which has none. Keeping it portable means a maintainer can run this
# locally instead of discovering a boundary regression only in CI.
awk -F'\t' \
  -v baseFile="$BASELINE" -v holdsFile="$HOLDS" -v curFile="$CURRENT" \
  -v changedFile="$CHANGED" -v baseCountsFile="$BASE_COUNTS" \
  -v mode="$MODE" -v compareBase="$COMPARE_BASE" '
function err(msg) { print msg > "/dev/stderr" }
FILENAME == baseFile { if ($1 != "") base[$1] = $2 + 0; next }
FILENAME == holdsFile {
  if ($0 ~ /^#/ || $1 == "") next
  hold[$1] = ($2 == "" ? "(no reason recorded)" : $2)
  next
}
FILENAME == curFile { if ($1 != "") cur[$1] = $2 + 0; next }
FILENAME == changedFile { if ($0 != "") changed[$0] = 1; next }
FILENAME == baseCountsFile { if ($1 != "") were[$1] = $2 + 0; next }
END {
  violations = 0
  for (f in cur) {
    limit = (f in base) ? base[f] : 0
    if (cur[f] > limit) {
      err("ERROR: " f " has " cur[f] " standalone PMF/SPMF occurrence(s); baseline ceiling is " limit ".")
      violations++
    }
  }
  if (violations > 0) {
    err("PMF/SPMF boundary: " violations " file(s) increased direct finite-distribution coupling.")
    err("Use Measure/Kernel for new semantics, or update the baseline with explicit review.")
    exit 1
  }

  if (mode == "ceiling") { print "PMF/SPMF boundary: OK."; exit 0 }

  if (mode == "report") {
    # Advisory only. Reports what this change did to the retiring surface, against the counts
    # recorded on the base ref, so the trend is visible on every pull request without turning
    # unrelated work into a boundary failure.
    nowTotal = 0; for (f in cur) nowTotal += cur[f]
    wasTotal = 0; for (f in were) wasTotal += were[f]

    n = 0
    for (f in cur) { seen[f] = 1 }
    for (f in were) { seen[f] = 1 }
    for (f in seen) {
      c = (f in cur) ? cur[f] : 0
      w = (f in were) ? were[f] : 0
      if (c == w) continue
      n++; name[n] = f; from[n] = w; to[n] = c
      mag[n] = (c > w) ? c - w : w - c
    }

    # Selection sort by magnitude: at most a few dozen entries, and it keeps the biggest movers
    # at the top of a CI log that is otherwise unreadable.
    for (i = 1; i <= n; i++) {
      best = i
      for (j = i + 1; j <= n; j++) if (mag[j] > mag[best]) best = j
      if (best != i) {
        t = name[i]; name[i] = name[best]; name[best] = t
        t = from[i]; from[i] = from[best]; from[best] = t
        t = to[i];   to[i]   = to[best];   to[best]   = t
        t = mag[i];  mag[i]  = mag[best];  mag[best]  = t
      }
    }

    limitShown = 12
    for (i = 1; i <= n && i <= limitShown; i++) {
      dir = (to[i] > from[i]) ? "grew   " : "shrank "
      print "  " dir name[i] "  " from[i] " -> " to[i]
    }
    if (n > limitShown) print "  ... and " (n - limitShown) " more file(s) changed"

    delta = nowTotal - wasTotal
    sign = (delta > 0) ? "+" : ""
    print "PMF/SPMF boundary: " nowTotal " standalone occurrence(s) vs " wasTotal \
          " on " compareBase " (" sign delta ")."
    if (n == 0) {
      print "PMF/SPMF boundary: this change does not move the retiring surface."
    } else if (delta > 0) {
      print "PMF/SPMF boundary: this change grows the retiring surface. Allowed when the baseline"
      print "                   change is deliberate and reviewed -- but prefer Measure/Kernel."
    } else if (delta < 0) {
      print "PMF/SPMF boundary: this change shrinks the retiring surface by " (-delta) "."
    }
    exit 0
  }

  stalled = 0
  for (f in changed) {
    if (f !~ /\.lean$/) continue
    if (!(f in base) || base[f] == 0) continue
    c = (f in cur) ? cur[f] : 0
    if (c < base[f]) continue
    if (f in hold) { print "PMF/SPMF boundary: hold on " f " (" c ") -- " hold[f]; continue }
    err("ERROR: " f " is touched by this change and still has " c " standalone PMF/SPMF")
    err("       occurrence(s) (baseline " base[f] ").")
    stalled++
  }
  if (stalled > 0) {
    err("PMF/SPMF boundary: " stalled " touched file(s) did not reduce their coupling.")
    err("PMF is being retired upstream; a deliberate reduction pass should shrink what it touches.")
    err("If a file genuinely must hold, add it to " holdsFile " with a reason.")
    exit 1
  }
  print "PMF/SPMF boundary: OK (ceiling + ratchet vs " compareBase ")."
}
' "$BASELINE" "$HOLDS" "$CURRENT" "$CHANGED" "$BASE_COUNTS"
