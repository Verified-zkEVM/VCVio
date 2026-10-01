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
