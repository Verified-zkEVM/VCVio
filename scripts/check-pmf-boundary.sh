#!/usr/bin/env bash
# scripts/check-pmf-boundary.sh
#
# Keep finite-distribution coupling from growing while VCVio moves its denotational boundary to
# Mathlib measures. The baseline is a per-file syntactic ceiling for standalone `PMF` and `SPMF`
# identifiers in Lean source, excluding comments and string literals; compound names such as
# `FinRatPMF` do not count. A file absent from the baseline has a ceiling of zero. This is a
# migration proxy for explicit source coupling, not a semantic dependency analysis.
#
# `SPMF` counts because `SPMF := OptionT PMF`, so every explicit use is a transitive PMF
# dependency. Counting only bare `PMF` missed much of the explicit migration surface.
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
  LIBS=(VCVio VCVioCslib ToMathlib LatticeCrypto HashSig Examples VCVioWidgets)
fi
CURRENT="$(mktemp "${TMPDIR:-/tmp}/vcvio-pmf-boundary.XXXXXX")"
trap 'rm -f "$CURRENT"' EXIT

count_tree() {
  local tree_root="$1"
  local output="$2"
  (
    cd "$tree_root"
    # A small Lean-aware lexical pass keeps comments and documentation from consuming the budget.
    # It also gives every platform the same behavior and naturally accepts a tree with no matches.
    while IFS= read -r -d '' file; do
      count="$(LC_ALL=C awk '
        function isAlpha(c) { return c ~ /[[:alpha:]]/ }
        {
          line = $0
          i = 1
          while (i <= length(line)) {
            if (blockDepth > 0) {
              if (substr(line, i, 2) == "/-") { blockDepth++; i += 2; continue }
              if (substr(line, i, 2) == "-/") { blockDepth--; i += 2; continue }
              i++
              continue
            }

            ch = substr(line, i, 1)
            if (inString) {
              if (escaped) { escaped = 0; i++; continue }
              if (ch == "\\") { escaped = 1; i++; continue }
              if (ch == "\"") inString = 0
              i++
              continue
            }

            if (substr(line, i, 2) == "--") break
            if (substr(line, i, 2) == "/-") { blockDepth = 1; i += 2; continue }
            if (ch == "\"") { inString = 1; i++; continue }

            token = ""
            if (substr(line, i, 4) == "SPMF") token = "SPMF"
            else if (substr(line, i, 3) == "PMF") token = "PMF"
            if (token != "") {
              before = (i == 1) ? "" : substr(line, i - 1, 1)
              after = substr(line, i + length(token), 1)
              if (!isAlpha(before) && !isAlpha(after)) total++
              i += length(token)
              continue
            }
            i++
          }
          escaped = 0
        }
        END { print total + 0 }
      ' "$file")"
      if (( count > 0 )); then
        printf '%s\t%s\n' "$file" "$count"
      fi
    done < <(find "${LIBS[@]}" -type f -name '*.lean' -print0)
  ) | sort > "$output"
}

count_tree "$REPO_ROOT" "$CURRENT"

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
BASE_COUNTS="$(mktemp "${TMPDIR:-/tmp}/vcvio-pmf-basecounts.XXXXXX")"
BASE_TREE=""
cleanup() {
  rm -f "$CURRENT" "$CHANGED" "$BASE_COUNTS"
  if [[ -n "$BASE_TREE" && -d "$BASE_TREE" ]]; then
    rm -rf -- "$BASE_TREE"
  fi
}
trap cleanup EXIT

if [[ "$MODE" != "ceiling" ]]; then
  if git rev-parse --verify --quiet "$COMPARE_BASE" >/dev/null; then
    git diff --name-only "$COMPARE_BASE"...HEAD -- "${LIBS[@]}" > "$CHANGED"
    BASE_TREE="$(mktemp -d "${TMPDIR:-/tmp}/vcvio-pmf-base-tree.XXXXXX")"
    if ! git archive "$COMPARE_BASE" -- "${LIBS[@]}" | tar -x -C "$BASE_TREE"; then
      echo "PMF/SPMF boundary: could not materialize base ref '$COMPARE_BASE'." >&2
      exit 2
    fi
    count_tree "$BASE_TREE" "$BASE_COUNTS"
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
    # Advisory only. Reports what this change did to the retiring surface, against the actual
    # source counts on the base ref, so the trend is visible on every pull request without turning
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
    c = (f in cur) ? cur[f] : 0
    w = (f in were) ? were[f] : 0
    if (c == 0 || c < w) continue
    if (f in hold) { print "PMF/SPMF boundary: hold on " f " (" c ") -- " hold[f]; continue }
    err("ERROR: " f " is touched by this change and still has " c " standalone PMF/SPMF")
    err("       occurrence(s) (actual base count " w ").")
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
