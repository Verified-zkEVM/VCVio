#!/usr/bin/env bash

# Falsifiable fixtures for the documentation name checker (`scripts/check-doc-names.py` and
# `lake exe docnames`): a document whose names all resolve (a declaration, a namespace, a module,
# an option, a simp set, a suffix, a field, a tactic keyword and a sort), one citing a
# retired name, one citing a dead declaration, the allowlist accepting that dead name, and an
# obsolete allowlist entry. Needs the proof libraries' oleans (run after `lake build`).

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

FIXTURE_TMP="$(mktemp -d "${TMPDIR:-/tmp}/vcvio-docnames.XXXXXX")"
trap 'rm -rf -- "$FIXTURE_TMP"' EXIT

expect_status() {
  local expected="$1"
  local label="$2"
  shift 2
  local log="$FIXTURE_TMP/${label}.log"
  local actual=0
  "$@" >"$log" 2>&1 || actual=$?
  if [[ "$actual" -ne "$expected" ]]; then
    echo "ERROR: $label returned $actual; expected $expected" >&2
    sed -n '1,60p' "$log" >&2
    return 1
  fi
}

expect_line() {
  local label="$1"
  local pattern="$2"
  if ! grep -q -- "$pattern" "$FIXTURE_TMP/${label}.log"; then
    echo "ERROR: $label did not report '$pattern'" >&2
    sed -n '1,60p' "$FIXTURE_TMP/${label}.log" >&2
    return 1
  fi
}

CHECK=(python3 scripts/check-doc-names.py)
EMPTY_ALLOWLIST="$FIXTURE_TMP/empty.txt"
: > "$EMPTY_ALLOWLIST"

cat > "$FIXTURE_TMP/good.md" <<'DOC'
`OracleComp.prEvent_bind_eq_tsum` is a declaration, `OracleComp.Lower` a namespace,
`VCVio.ProgramLogic.Tactics` a module, `linter.style.whitespace` and `weak.linter.style.longFile`
options, `expect_norm` a simp set, `gcongr` an attribute, `Spec.uniformSample` a suffix,
`Tracing.Core` a module segment, `spec.toPFunctor` a field access, `.run'` a field, `by_dist` a
tactic keyword, `Dispatch` a namespace suffix and `Prop` a sort; `lake build`, `extern_lib` and
`Pr{let x ← oa}[p x]` are not checked.
DOC

cat > "$FIXTURE_TMP/retired.md" <<'DOC'
`IsUniformMeasureSpec` was renamed; `OracleComp.support` is current.
DOC

cat > "$FIXTURE_TMP/dead.md" <<'DOC'
`OracleComp.Lower.Spec.noSuchRule` is not a declaration.
DOC

printf 'OracleComp.Lower.Spec.noSuchRule # fixture\n' > "$FIXTURE_TMP/allow.txt"
printf 'OracleComp.Lower.Spec.noSuchRule\nOracleComp.prEvent_bind_eq_tsum\nOracleComp.gone\n' \
  > "$FIXTURE_TMP/stale.txt"

expect_status 1 retired "${CHECK[@]}" --allowlist "$EMPTY_ALLOWLIST" "$FIXTURE_TMP/retired.md"
expect_line retired 'retired name `IsUniformMeasureSpec`'
expect_status 0 retired-clean "${CHECK[@]}" --allowlist "$EMPTY_ALLOWLIST" "$FIXTURE_TMP/dead.md"

cat > "$FIXTURE_TMP/living.md" <<'DOC'
> Status: living ledger.

`IsUniformMeasureSpec` appears in a document that describes the present.
The structural reading of `oa` describes the present too.
PolyFun's angelic reading is PolyFun's own name.
DOC

cat > "$FIXTURE_TMP/historical.md" <<'DOC'
> Status: historical record, 2026-08-21.

`IsUniformMeasureSpec` and the structural reading were current when this was written.
DOC

cat > "$FIXTURE_TMP/Prose.lean" <<'DOC'
/-- The angelic reading of a computation. -/
def fixtureAngelic : Nat := 1

-- `IsUniformMeasureSpec` in a comment.
/-- PolyFun's demonic weakest precondition, and `structural reading` inside a code span. -/
def fixtureClean : Nat := "-- structural reading in a string is not prose".length
DOC

expect_status 1 living "${CHECK[@]}" --allowlist "$EMPTY_ALLOWLIST" "$FIXTURE_TMP/living.md"
expect_line living 'living.md:3: retired name `IsUniformMeasureSpec`'
expect_line living 'living.md:4: retired reading label "structural reading"'
if grep -q 'living.md:5:' "$FIXTURE_TMP/living.log"; then
  echo "ERROR: living flagged a line that names PolyFun's own reading" >&2
  exit 1
fi
expect_status 0 historical "${CHECK[@]}" --allowlist "$EMPTY_ALLOWLIST" \
  "$FIXTURE_TMP/historical.md"
expect_status 1 prose "${CHECK[@]}" --allowlist "$EMPTY_ALLOWLIST" "$FIXTURE_TMP/Prose.lean"
expect_line prose 'Prose.lean:1: retired reading label "angelic reading"'
expect_line prose 'Prose.lean:4: retired name `IsUniformMeasureSpec`'
if grep -q 'Prose.lean:[56]:' "$FIXTURE_TMP/prose.log"; then
  echo "ERROR: prose flagged a PolyFun label, a code span or a string" >&2
  exit 1
fi

expect_status 0 good "${CHECK[@]}" --resolve --allowlist "$EMPTY_ALLOWLIST" "$FIXTURE_TMP/good.md"
expect_line good 'Documentation names: OK'
expect_status 1 dead "${CHECK[@]}" --resolve --allowlist "$EMPTY_ALLOWLIST" \
  "$FIXTURE_TMP/dead.md" "$FIXTURE_TMP/retired.md"
expect_line dead 'dead.md:1: `OracleComp.Lower.Spec.noSuchRule` does not resolve'
expect_line dead 'retired name `IsUniformMeasureSpec`'
expect_status 0 allowlisted "${CHECK[@]}" --resolve --allowlist "$FIXTURE_TMP/allow.txt" \
  "$FIXTURE_TMP/dead.md"
expect_status 1 stale "${CHECK[@]}" --resolve --allowlist "$FIXTURE_TMP/stale.txt" \
  "$FIXTURE_TMP/dead.md" "$FIXTURE_TMP/good.md"
expect_line stale 'obsolete allowlist entry `OracleComp.prEvent_bind_eq_tsum` (resolves)'
expect_line stale 'obsolete allowlist entry `OracleComp.gone` (no longer cited)'

echo "docnames fixtures: OK"
