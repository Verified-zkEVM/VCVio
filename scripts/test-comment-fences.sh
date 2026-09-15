#!/usr/bin/env bash
# scripts/test-comment-fences.sh
#
# Exercise check-comment-fences.py against fixtures: the declaration hidden after a
# reflowed docstring that motivated the gate, the same shape for a single-line comment at
# the margin, the indented multi-line annotations that must stay legal (a wrapped
# structure-field docstring is a common documentation shape in this repository and the rule
# must not reach it), the literal forms that could confuse a lexical scanner, the line
# numbering that a raw string or a gap escape would drift, the column-0 shapes the
# positional rule rejects although they are clean Lean, the shapes the rule knowingly does
# not cover, and the file selection.
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

# A block comment that opens part-way into a line is an annotation inside some larger piece
# of syntax, and must stay accepted however many lines it spans; and a comment at the margin
# followed only by more comments hides nothing either. All nine shapes below are Lean that
# elaborates with the package's own options and Mathlib's standard linter set on, with no
# error and no warning (measured with `Mathlib.Init` imported, so the `weak.` option is
# actually registered). The rule fired on 1-7 while it also keyed on "spans more than one
# line", and on 8-9 until it learned to skip what cannot hide anything; shape 2 is the
# common one — most of this repository's multi-line off-margin comments are that shape.
cat > Lib/Innocent.lean <<'LEAN'
/-- 1. A multi-line inline annotation inside an expression. -/
def one (x y : Nat) : Nat :=
  x +
  /- this argument is
     the seed -/ y

/-- 2. A wrapped structure-field docstring. -/
structure Two where
  /-- The first field, with a docstring long enough
  that it wraps. -/ a : Nat

/-- 3. A wrapped inductive-constructor docstring. -/
inductive Three where
  /-- A constructor docstring long enough
  that it wraps. -/ | mk : Nat → Three

/-- 4. A wrapped annotation in a `where` block. -/
def four : Nat := k
where
  /- helper, described over
     two lines -/ k : Nat := 1

/-- 5. A wrapped annotation between list elements. -/
def five : List Nat :=
  [1, /- the first
     element -/ 2,
   3]

/-- 6. A wrapped annotation before a closing bracket. -/
def six : List Nat :=
  [1, 2, 3 /- the last
     element -/ ]

/-- 7. A wrapped annotation in a tactic block. -/
theorem seven : True := by
  /- explain the step
     over two lines -/ trivial

/- 8. A second block comment after the first hides nothing. -/ /- and neither does this -/
/- 9. Nor does a line comment. -/ -- a trailing note
LEAN
git add -A
git commit -qm 'fixture: indented multi-line annotations'
expect_status 0 innocent "$CHECKER"
grep -q "Comment fences: OK" "$FIXTURE_REPO/innocent.log"

# --- the defect this gate exists for -----------------------------------------------------

# A docstring reflowed until its terminator shares a line with the declaration it
# documents. This parses, builds and runs; `linter.style.whitespace` accepts it, because
# the command it would measure starts at the `/--`, at the beginning of a line.
cat > Lib/Swallowed.lean <<'LEAN'
/-- A docstring long enough that a reflow moved its terminator, and with it the
declaration that follows. -/ def swallowed : Nat := 1
LEAN
expect_status 1 swallowed "$CHECKER"
grep -q "Lib/Swallowed.lean:2: a block comment that starts its line" "$FIXTURE_REPO/swallowed.log"
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

# The message quotes what follows the `-/`, and a line comment the author wrote after that
# is left out of the quotation: it is not part of what was hidden. Only the quotation is
# trimmed — the decision to report is unchanged.
cat > Lib/Trailing.lean <<'LEAN'
/-- Short. -/ def quoted : Nat := 1 -- a note the author wrote after it
LEAN
expect_status 1 trailing "$CHECKER"
grep -q "followed by 'def quoted : Nat := 1' on the line" "$FIXTURE_REPO/trailing.log"
rm Lib/Trailing.lean

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

# A raw string honours no escapes, so only its closing quote ends it — but the newlines
# inside it still have to be counted. Not counting them drifts every line number reported
# after the string, permanently, by the number of newlines it holds.
cat > Lib/RawDrift.lean <<'LEAN'
def banner : String := r"line one
line two
line three"

/-- A docstring whose terminator swallowed the
declaration. -/ def swallowed : Nat := 1
LEAN
expect_status 1 raw-drift "$CHECKER"
grep -q "Lib/RawDrift.lean:6:" "$FIXTURE_REPO/raw-drift.log"
rm Lib/RawDrift.lean

# --- the shapes the positional rule rejects, although they hide nothing -------------------

# The test is where the comment opens, not what follows it, and Lean lets a term, a
# structure field, a tactic and a list element begin at column 0 where the enclosing
# command's indentation has run out. A comment in front of one of those is rejected like a
# top-level one. The fifth shape is rejected for a different reason: the line ends inside a
# second, still-open comment, and the rule reports rather than guessing about the next line.
# All five elaborate with no error and no warning (measured), so these are rejections of
# clean Lean, asserted here so the boundary is written down rather than rediscovered — the
# absence of exactly this fixture is what let an earlier, wider version of the rule reach
# seven such shapes unnoticed.
cat > Lib/ColumnZero.lean <<'LEAN'
def term : Nat :=
/- the seed -/ 1

structure Field where
/-- doc -/ a : Nat

theorem tactic : True := by
/- explain -/ trivial

def element : List Nat :=
  [1,
/- two -/ 2,
   3]

/- a -/ /- b
   more -/
def after : Nat := 1
LEAN
expect_status 1 column-zero "$CHECKER"
grep -q "Lib/ColumnZero.lean:2: .* followed by '1'" "$FIXTURE_REPO/column-zero.log"
grep -q "Lib/ColumnZero.lean:5: .* followed by 'a : Nat'" "$FIXTURE_REPO/column-zero.log"
grep -q "Lib/ColumnZero.lean:8: .* followed by 'trivial'" "$FIXTURE_REPO/column-zero.log"
grep -q "Lib/ColumnZero.lean:12: .* followed by '2,'" "$FIXTURE_REPO/column-zero.log"
grep -q "Lib/ColumnZero.lean:15: .* followed by '/- b'" "$FIXTURE_REPO/column-zero.log"
rm Lib/ColumnZero.lean

# --- the shapes the rule knowingly does not reach -----------------------------------------

# Asserted so the documented gap cannot change without this test saying so. Each of these
# puts a declaration somewhere other than the left margin of its own line, and none of them
# has code after the `-/` of a comment at column 0 — the first because its comment ends its
# own line, the next three because their comments are not at column 0 or there is no comment
# at all, and the last because its delimiter is a string quote and not a comment. The first
# is uncovered everywhere, including the libraries that elaborate: `linter.style.whitespace`
# measures the command from its doc comment, which is at column 0, so it draws no warning
# either (measured). The other four the linter does report, so they fail CI in the seven
# proof and three test libraries — but not in `lakefile.lean`, `VCVioComplexity/lakefile.lean`
# or `Interop/`, which nothing elaborates; not in `scripts/`, which per-PR CI builds but
# whose sources import no Mathlib, so the `weak.` option is dropped and the linter is never
# registered; and not effectively in `VCVioComplexity/`, where the linter does run and warn
# but no step turns that warning into a failure.
cat > Lib/Uncovered.lean <<'LEAN'
/-- A docstring at the margin, its declaration indented on the next line. -/
  def hiddenOne : Nat := 1

  /-- Indented, and on the target's line. -/ def hiddenTwo : Nat := 1

def a : Nat := 1 /- note -/ def hiddenThree : Nat := 2

def b : Nat := 1
  def hiddenFour : Nat := 1

def gapped : String := "first half \
second half" def hiddenFive : Nat := 2
LEAN
expect_status 0 uncovered "$CHECKER"
rm Lib/Uncovered.lean

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
