#!/usr/bin/env bash
# scripts/test-comment-fences.sh
#
# Exercise check-comment-fences.py against fixtures: the declaration hidden after a
# reflowed docstring that motivated the gate, the same shape for a comment that merely
# starts its line, the inline annotations that must stay legal, the literal forms that
# could confuse a lexical scanner, and the file selection.
#
# The checker takes its default file list from git, so the fixtures live in a throwaway
# repository with the script copied into it.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CHECKER_SRC="$REPO_ROOT/scripts/check-comment-fences.py"
FIXTURE_REPO="$(mktemp -d "${TMPDIR:-/tmp}/vcvio-comment-fences.XXXXXX")"
trap 'rm -rf "$FIXTURE_REPO"' EXIT

mkdir -p "$FIXTURE_REPO/scripts" "$FIXTURE_REPO/Lib" "$FIXTURE_REPO/third_party/vendor"
cp "$CHECKER_SRC" "$FIXTURE_REPO/scripts/check-comment-fences.py"
CHECKER="$FIXTURE_REPO/scripts/check-comment-fences.py"

cd "$FIXTURE_REPO"
git init -q .
git config user.email fixture@example.com
git config user.name Fixture

expect_status() {
  local expected="$1"
  local label="$2"
  shift 2
  local log="$FIXTURE_REPO/${label}.log"
  local actual=0
  "$@" >"$log" 2>&1 || actual=$?
  if [[ "$actual" -ne "$expected" ]]; then
    echo "ERROR: $label returned $actual; expected $expected" >&2
    sed -n '1,80p' "$log" >&2
    exit 1
  fi
}

# --- what must be accepted --------------------------------------------------------------

# Inline annotations, and every literal form whose contents could be read as a fence: a
# string, a raw string with a backslash in it, a character literal holding a quote, an
# identifier ending in a prime, and nested comments.
cat > Lib/Accepted.lean <<'LEAN'
/-
Copyright header.
-/

/-! # Module doc -/

/-- Inline annotations hide nothing: the code around them is on the line being read. -/
def f (x : Nat) : Nat := (x /- the seed -/) + 1

/-- A string literal below contains a fence. -/
def g : String := "a -/ inside a string"

/-- Raw strings honour no escapes. -/
def h : String := r"backslash \ and -/ inside"

/-- A character literal holding a quote, and a primed name. -/
def i' : Char := '"'

/-- Nested /- comments -/ still work. -/
def j : Nat := 0
LEAN
git add -A
git commit -qm 'fixture: accepted shapes'
expect_status 0 accepted "$CHECKER"
grep -q "Comment fences: OK" "$FIXTURE_REPO/accepted.log"

# --- the defect this gate exists for -----------------------------------------------------

# A docstring reflowed until its terminator shares a line with the declaration it
# documents. This parses, builds and runs; `linter.style.whitespace` accepts it, because
# the command it would measure starts at the `/--`, at the beginning of a line.
cat > Lib/Swallowed.lean <<'LEAN'
/-- A docstring long enough that a reflow moved its terminator, and with it the
declaration that follows. -/ def swallowed : Nat := 1
LEAN
expect_status 1 swallowed "$CHECKER"
grep -q "Lib/Swallowed.lean:2: a block comment that spans lines" "$FIXTURE_REPO/swallowed.log"
grep -q "def swallowed" "$FIXTURE_REPO/swallowed.log"
rm Lib/Swallowed.lean

# The same hiding, from a comment that fits on one line but starts at the margin: the
# declaration no longer begins its own line either.
cat > Lib/Pushed.lean <<'LEAN'
/-- Short. -/ def pushed : Nat := 1
LEAN
expect_status 1 pushed "$CHECKER"
grep -q "Lib/Pushed.lean:1: a block comment that starts its line" "$FIXTURE_REPO/pushed.log"
rm Lib/Pushed.lean

# --- line numbers survive the shapes that shift a naive scanner --------------------------

# A gap escape is a backslash followed by a newline inside a string literal. Skipping the
# escape without counting that newline is how a scanner drifts, and the reported line
# would then name innocent code.
cat > Lib/Gap.lean <<'LEAN'
def gap : String := "a gap escape \
  continues here \
  and here"

/-- Reported on the right line. -/ def after : Nat := 1
LEAN
expect_status 1 gap "$CHECKER"
grep -q "Lib/Gap.lean:5:" "$FIXTURE_REPO/gap.log"
rm Lib/Gap.lean

# --- file selection -----------------------------------------------------------------------

# Untracked sources are checked: a defect must fail before it is committed, not after.
cat > Lib/Untracked.lean <<'LEAN'
/-- Untracked and hiding something. -/ def hidden : Nat := 1
LEAN
expect_status 1 untracked "$CHECKER"
grep -q "Lib/Untracked.lean" "$FIXTURE_REPO/untracked.log"

# Ignored sources are not: they are build output or scratch work, not repository sources.
printf 'Lib/Untracked.lean\n' > .gitignore
expect_status 0 ignored "$CHECKER"
rm .gitignore Lib/Untracked.lean

# Vendored trees are excluded: their style is upstream's business.
cat > third_party/vendor/Vendored.lean <<'LEAN'
/-- Vendored and hiding something. -/ def vendored : Nat := 1
LEAN
git add -A
git commit -qm 'fixture: vendored source'
expect_status 0 vendored "$CHECKER"

# Named paths override the git listing, so the vendored file can still be checked on
# purpose, and a directory expands to the Lean sources under it.
expect_status 1 explicit-path "$CHECKER" third_party/vendor/Vendored.lean
expect_status 1 explicit-directory "$CHECKER" third_party
rm third_party/vendor/Vendored.lean
git add -A
git commit -qm 'fixture: drop vendored source'

# --- infrastructure failures must never read as a clean verdict ---------------------------

# An empty file list means the selection is broken, not that the repository is clean.
expect_status 2 no-sources "$CHECKER" "$FIXTURE_REPO/scripts"
expect_status 2 missing-file "$CHECKER" Lib/NoSuchFile.lean

echo "✓ Comment fence fixture matrix passed."
