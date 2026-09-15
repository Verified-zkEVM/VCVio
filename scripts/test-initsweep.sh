#!/usr/bin/env bash

# Execute falsifiable fixtures for the eager-initialisation ratchet.
#
# The gate's baseline is zero everywhere, so its zero is worth nothing unless the fixtures
# can make it non-zero. `VCVioInitSweepTestFixtures.Hazard` carries the three routes by
# which loading a module can build an enumeration of a type, and
# `VCVioInitSweepTestFixtures.Clean` carries one negative control per clause of the
# predicate — each asserted here by name, not by count.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

FIXTURE_TMP="$(mktemp -d "${TMPDIR:-/tmp}/vcvio-initsweep.XXXXXX")"
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
    sed -n '1,160p' "$log" >&2
    return 1
  fi
}

ZERO_BASELINE="$FIXTURE_TMP/zero.tsv"
EXACT_BASELINE="$FIXTURE_TMP/exact.tsv"
TIGHT_BASELINE="$FIXTURE_TMP/tight.tsv"
HIGH_BASELINE="$FIXTURE_TMP/high-clean.tsv"
INVALID_BASELINE="$FIXTURE_TMP/invalid.tsv"
EMPTY_BASELINE="$FIXTURE_TMP/empty.tsv"
MISSING_BASELINE="$FIXTURE_TMP/missing.tsv"
CLEAN_REPORT="$FIXTURE_TMP/clean.json"
HAZARD_REPORT="$FIXTURE_TMP/hazard.json"
HAZARD_REPORT_2="$FIXTURE_TMP/hazard-2.json"

ROOTS=(VCVioInitSweepTestFixtures.Clean VCVioInitSweepTestFixtures.Hazard
  VCVioInitSweepTestFixtures.Standalone)
printf '%s\t0\n' "${ROOTS[@]}" >"$ZERO_BASELINE"
printf 'VCVioInitSweepTestFixtures.Hazard\t3\n' >"$EXACT_BASELINE"
printf 'VCVioInitSweepTestFixtures.Hazard\t2\n' >"$TIGHT_BASELINE"
printf 'VCVioInitSweepTestFixtures.Clean\t3\n' >"$HIGH_BASELINE"
printf 'VCVioInitSweepTestFixtures.Hazard 0\n' >"$INVALID_BASELINE"
: >"$EMPTY_BASELINE"

lake build VCVioInitSweepTestFixtures
lake exe initsweep --root VCVioInitSweepTestFixtures.Clean --out "$CLEAN_REPORT"
lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard --out "$HAZARD_REPORT"
lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard --out "$HAZARD_REPORT_2"

# The sweep must be deterministic: same build, byte-identical report.
cmp "$HAZARD_REPORT" "$HAZARD_REPORT_2"

python3 - "$CLEAN_REPORT" "$HAZARD_REPORT" <<'PY'
import json
import sys

clean_path, hazard_path = sys.argv[1:]

with open(clean_path, encoding="utf-8") as stream:
    clean = json.load(stream)
with open(hazard_path, encoding="utf-8") as stream:
    hazard = json.load(stream)

clean_entries = {entry["name"]: entry for entry in clean["loadTime"]}
hazard_entries = {entry["name"]: entry for entry in hazard["loadTime"]}
flagged = {name: entry for name, entry in hazard_entries.items() if entry["entryPoints"]}

# Every value the module initialiser evaluates must be readable. A constant the sweep
# cannot read is one the name test accepts without looking at anything, so this number is
# the gate's blind spot and both fixture roots must hold it at zero.
assert clean["opaqueValueCount"] == 0, clean["opaqueValueCount"]
assert hazard["opaqueValueCount"] == 0, hazard["opaqueValueCount"]

# --- the hazard, by each route ------------------------------------------------------

# The plain spelling and the `noncomputable` one differ in source and not in effect: the
# instance itself loses its compiled code, the auxiliary that carries the enumeration does
# not, and the gate flags the same constant in both.
for module in ("Plain", "Noncomputable"):
    name = (f"VCVioInitSweepTestFixtures.Hazard.{module}"
            ".instFintypeYBundle._aux_1")
    assert name in flagged, sorted(flagged)
    assert flagged[name]["via"] == "value", flagged[name]
    assert flagged[name]["source"] == name, flagged[name]
    assert "Finset.univ" in flagged[name]["entryPoints"], flagged[name]

# The instance of the `noncomputable` spelling carries no compiled code at all, so it is
# not even in the load-time population: only its auxiliary is.
noncomputable_instance = (
    "VCVioInitSweepTestFixtures.Hazard.Noncomputable.instFintypeYBundle")
assert noncomputable_instance not in hazard_entries, hazard_entries[noncomputable_instance]

# `initialize x : T ← e` leaves `x` valueless; the gate has to follow the registered
# initialiser to see anything at all.
initialized = "VCVioInitSweepTestFixtures.Hazard.Initialize.enumeration"
assert initialized in flagged, sorted(flagged)
assert flagged[initialized]["via"] == "initialize", flagged[initialized]
assert flagged[initialized]["source"] != initialized, flagged[initialized]
assert flagged[initialized]["entryPoints"] == ["Finset.univ"], flagged[initialized]

assert len(flagged) == 3, sorted(flagged)

# --- one negative control per clause, each witnessed by name -------------------------

clean_prefix = "VCVioInitSweepTestFixtures.Clean."

# Parameter clause: names `Finset.univ`, compiles, takes a parameter, so it is called
# rather than initialised and never enters the load-time population.
assert clean_prefix + "Negatives.enumerate" not in clean_entries

# Compiled-code clause: a theorem names `Fintype.card` and carries no code.
assert clean_prefix + "Negatives.card_pos" not in clean_entries

# Compiled-code clause again, and the reason this gate exists: the shipped spelling names
# `Fintype.ofFinite`, which is in the entry-point list, and is still not flagged because
# routing through the `Prop`-valued argument leaves nothing compiled.
assert clean_prefix + "Good.instFintypeYBundle" not in clean_entries
assert not any(name.startswith(clean_prefix + "Good.instFintypeYBundle.")
               for name in clean_entries), sorted(clean_entries)

# Entry-point clause: these three are evaluated at load time and are accepted.
for name in ("Negatives.table", "Negatives.small", "Negatives.counter"):
    entry = clean_entries[clean_prefix + name]
    assert entry["entryPoints"] == [], entry

# ... and the `initialize` control is read through its initialiser, like the hazard is.
assert clean_entries[clean_prefix + "Negatives.counter"]["via"] == "initialize"

assert not any(entry["entryPoints"] for entry in clean_entries.values()), sorted(
    name for name, entry in clean_entries.items() if entry["entryPoints"])
PY

# --- gate directions -------------------------------------------------------------------

expect_status 0 clean-check \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --baseline "$ZERO_BASELINE"
expect_status 1 hazard-over-ceiling \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$ZERO_BASELINE"
grep -q "instFintypeYBundle._aux_1" "$FIXTURE_TMP/hazard-over-ceiling.log"
grep -q "Fintype.ofFinite" "$FIXTURE_TMP/hazard-over-ceiling.log"

# A library the baseline does not mention has a ceiling of zero, so a hazard cannot be
# greened by deleting its row.
printf 'VCVio\t0\n' >"$FIXTURE_TMP/other.tsv"
expect_status 1 hazard-other-library-only \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$FIXTURE_TMP/other.tsv"

# The ceiling is exact: it accepts the measured count and nothing above it.
expect_status 0 hazard-at-ceiling \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$EXACT_BASELINE"
expect_status 1 hazard-just-under-ceiling \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$TIGHT_BASELINE"

# Shrinking is reported rather than failed, and points at the update command.
expect_status 0 clean-below-ceiling \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --baseline "$HIGH_BASELINE"
grep -q "update-baseline" "$FIXTURE_TMP/clean-below-ceiling.log"

# --- infrastructure failures must never read as a ratchet verdict ----------------------

# A root that does not reach Mathlib cannot match any entry point. Reporting that as a
# clean tree would be the worst failure this gate can have, so it is an exit-2 instead.
expect_status 2 entry-points-absent \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Standalone \
    --check --baseline "$ZERO_BASELINE"
grep -q "not present in the swept environment" "$FIXTURE_TMP/entry-points-absent.log"

expect_status 2 missing-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --baseline "$MISSING_BASELINE"
expect_status 2 invalid-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --baseline "$INVALID_BASELINE"
expect_status 2 empty-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --baseline "$EMPTY_BASELINE"
expect_status 2 conflicting-flags \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --update-baseline --baseline "$ZERO_BASELINE"
expect_status 2 unknown-flag \
  lake exe initsweep --bogus
expect_status 2 bad-root \
  lake exe initsweep --root NoSuchModule --check --baseline "$ZERO_BASELINE"
expect_status 2 unwritable-out \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --out "$FIXTURE_TMP/no-such-dir/report.json"

# --- baseline writing -------------------------------------------------------------------

# The escape hatch is one reviewable line per library, and what it writes is what `--check`
# then accepts.
cp "$ZERO_BASELINE" "$FIXTURE_TMP/written.tsv"
expect_status 0 write-hazard-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --update-baseline --baseline "$FIXTURE_TMP/written.tsv"
grep -qx "VCVioInitSweepTestFixtures.Hazard	3" "$FIXTURE_TMP/written.tsv"
expect_status 0 check-against-written \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$FIXTURE_TMP/written.tsv"

# Shrinking back to zero is what a fix looks like.
expect_status 0 shrink-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --update-baseline --baseline "$FIXTURE_TMP/written.tsv"
grep -qx "VCVioInitSweepTestFixtures.Clean	0" "$FIXTURE_TMP/written.tsv"

echo "✓ Init sweep executable fixture matrix passed."
