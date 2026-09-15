#!/usr/bin/env bash

# Execute falsifiable fixtures for the eager-initialisation ratchet.
#
# The gate accepts a flagged constant only when the committed baseline names it, so the
# fixtures have to falsify both halves: `VCVioInitSweepTestFixtures.Hazard` carries the five
# routes by which loading a module can build an enumeration of a type — including the
# respelling that a pure name test accepts, the route that writes no instance at all, and
# the value the kernel hides — and `VCVioInitSweepTestFixtures.Clean` carries one negative
# control per clause of the predicate. Each is asserted here by name, not by count. The
# baseline's own behaviour (accept by name, reject a widened entry-point set, reject a row
# scoped to another library, preserve rows outside the swept roots) is exercised below it.

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

EMPTY_BASELINE="$FIXTURE_TMP/empty.json"
STALE_BASELINE="$FIXTURE_TMP/stale.json"
INVALID_BASELINE="$FIXTURE_TMP/invalid.json"
ZERO_BYTE_BASELINE="$FIXTURE_TMP/zero-byte.json"
MISSING_BASELINE="$FIXTURE_TMP/missing.json"
ACCEPT_ALL="$FIXTURE_TMP/accept-all.json"
CLEAN_REPORT="$FIXTURE_TMP/clean.json"
HAZARD_REPORT="$FIXTURE_TMP/hazard.json"
HAZARD_REPORT_2="$FIXTURE_TMP/hazard-2.json"

printf '{"accepted": []}\n' >"$EMPTY_BASELINE"
printf 'not json\n' >"$INVALID_BASELINE"
: >"$ZERO_BYTE_BASELINE"
# A row for a constant that is *not* flagged, scoped to a library this run sweeps: the gate
# reports it as shrinkable rather than failing on it.
cat >"$STALE_BASELINE" <<'JSON'
{"accepted":
 [{"name": "VCVioInitSweepTestFixtures.Clean.Negatives.table",
   "library": "VCVioInitSweepTestFixtures.Clean",
   "entryPoints": ["Finset.univ"]}]}
JSON

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

# The respelling: the same instance at the same type, written as the instance the
# elaborator would have found. It names none of `enumerationEntryPoints` — what gives it
# away is that `Pi.instFintype` is *typed* `Fintype _`. This is the case a name test alone
# accepts, and the reason `enumerationClasses` exists.
named = "VCVioInitSweepTestFixtures.Hazard.Named.instFintypeYBundle"
assert named in flagged, sorted(flagged)
assert "Pi.instFintype" in flagged[named]["entryPoints"], flagged[named]
assert not any(point in flagged[named]["entryPoints"]
               for point in ("Finset.univ", "Fintype.elems", "Fintype.card",
                             "Fintype.piFinset", "Fintype.ofFinite", "Fintype.ofEquiv",
                             "Set.toFinset")), flagged[named]

# The route with no `Fintype` in the source at all: a top-level `decide` over a bounded
# quantifier enumerates the carrier through the `Decidable` instance.
decided = "VCVioInitSweepTestFixtures.Hazard.Decide.everyPointFixesZero"
assert decided in flagged, sorted(flagged)
assert "Pi.instFintype" in flagged[decided]["entryPoints"], flagged[decided]

# `initialize x : T ← e` leaves `x` valueless; the gate has to follow the registered
# initialiser to see anything at all.
initialized = "VCVioInitSweepTestFixtures.Hazard.Initialize.enumeration"
assert initialized in flagged, sorted(flagged)
assert flagged[initialized]["via"] == "initialize", flagged[initialized]
assert flagged[initialized]["source"] != initialized, flagged[initialized]
assert "Finset.univ" in flagged[initialized]["entryPoints"], flagged[initialized]

# The instance of the plain spelling is flagged in its own right as well as through its
# auxiliary: its value constructs a `Fintype`.
plain_instance = "VCVioInitSweepTestFixtures.Hazard.Plain.instFintypeYBundle"
assert plain_instance in flagged, sorted(flagged)

# `opaque` hides the value from unification, not from the backend: the emitted C assigns it
# from an `_init_` function like any other parameterless value, so the gate reads it and
# the blind-spot count stays at zero rather than absorbing the route.
opaque_value = "VCVioInitSweepTestFixtures.Hazard.Opaque.enumeration"
assert opaque_value in flagged, sorted(flagged)
assert flagged[opaque_value]["via"] == "value", flagged[opaque_value]
assert "Finset.univ" in flagged[opaque_value]["entryPoints"], flagged[opaque_value]

assert len(flagged) == 7, sorted(flagged)

# --- one negative control per clause, each witnessed by name -------------------------

clean_prefix = "VCVioInitSweepTestFixtures.Clean."

# Parameter clause: names `Finset.univ`, compiles, takes a parameter, so it is called
# rather than initialised and never enters the load-time population.
assert clean_prefix + "Negatives.enumerate" not in clean_entries

# Parameter clause against the class disjunct: names `Pi.instFintype` and `Fintype.elems`,
# and is still out of the population because it takes a parameter.
assert clean_prefix + "Negatives.enumerationSizeOf" not in clean_entries

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
    --check --baseline "$EMPTY_BASELINE"
expect_status 1 hazard-unaccepted \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$EMPTY_BASELINE"
grep -q "instFintypeYBundle._aux_1" "$FIXTURE_TMP/hazard-unaccepted.log"
grep -q "Hazard.Named.instFintypeYBundle" "$FIXTURE_TMP/hazard-unaccepted.log"
grep -q "Fintype.ofFinite" "$FIXTURE_TMP/hazard-unaccepted.log"
grep -q "update-baseline" "$FIXTURE_TMP/hazard-unaccepted.log"

# A baseline entry no longer flagged is reported, not failed, and points at the update
# command. (The row is scoped to a library this run sweeps; out-of-scope rows are silent.)
expect_status 0 clean-stale-row \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --baseline "$STALE_BASELINE"
grep -q "update-baseline" "$FIXTURE_TMP/clean-stale-row.log"

# --- the baseline accepts by name, and only what it names --------------------------------

# What `--update-baseline` writes is what `--check` then accepts.
expect_status 0 write-hazard-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --update-baseline --baseline "$ACCEPT_ALL"
expect_status 0 check-against-written \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$ACCEPT_ALL"

python3 - "$ACCEPT_ALL" "$FIXTURE_TMP" <<'PY'
import json
import sys

source, tmp = sys.argv[1:]
with open(source, encoding="utf-8") as stream:
    base = json.load(stream)

rows = base["accepted"]
assert len(rows) == 7, rows
assert all(row["library"] == "VCVioInitSweepTestFixtures.Hazard" for row in rows), rows

# Drop one constant: the other five stay accepted and that one is a regression.
one_missing = [row for row in rows if not row["name"].endswith("Named.instFintypeYBundle")]
with open(f"{tmp}/one-missing.json", "w", encoding="utf-8") as stream:
    json.dump({"accepted": one_missing}, stream)

# Keep every constant but narrow one row's entry points: a constant that starts naming a
# new entry point is a regression on a row that already exists.
narrowed = [dict(row, entryPoints=[point for point in row["entryPoints"]
                                   if point != "Pi.instFintype"])
            for row in rows]
with open(f"{tmp}/narrowed.json", "w", encoding="utf-8") as stream:
    json.dump({"accepted": narrowed}, stream)

# Same names, wrong library: scoping must not turn a row into a licence for another sweep.
mis_scoped = [dict(row, library="SomeOtherLibrary") for row in rows]
with open(f"{tmp}/mis-scoped.json", "w", encoding="utf-8") as stream:
    json.dump({"accepted": mis_scoped}, stream)

# A row for a library this run does not sweep, alongside the accepted six.
foreign = {"name": "SomeOtherLibrary.instFintypeThing",
           "library": "SomeOtherLibrary", "entryPoints": ["Fintype.mk"]}
with open(f"{tmp}/with-foreign.json", "w", encoding="utf-8") as stream:
    json.dump({"accepted": rows + [foreign]}, stream)
PY

expect_status 1 hazard-one-missing \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$FIXTURE_TMP/one-missing.json"
grep -q "Hazard.Named.instFintypeYBundle" "$FIXTURE_TMP/hazard-one-missing.log"

expect_status 1 hazard-narrowed-row \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$FIXTURE_TMP/narrowed.json"

expect_status 1 hazard-mis-scoped \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --check --baseline "$FIXTURE_TMP/mis-scoped.json"

# A row outside the swept roots is neither enforced nor lost: `--update-baseline` over a
# partial root set preserves it instead of silently dropping the other libraries' rows.
expect_status 0 update-preserves-foreign \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Hazard \
    --update-baseline --baseline "$FIXTURE_TMP/with-foreign.json"
grep -q "SomeOtherLibrary.instFintypeThing" "$FIXTURE_TMP/with-foreign.json"
grep -q "1 preserved" "$FIXTURE_TMP/update-preserves-foreign.log"

# Shrinking back to nothing is what a fix looks like.
expect_status 0 shrink-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --update-baseline --baseline "$ACCEPT_ALL"
python3 - "$ACCEPT_ALL" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    base = json.load(stream)
# The Clean sweep accepts nothing, and the Hazard rows belong to a library it did not
# sweep, so they survive untouched.
assert len(base["accepted"]) == 7, base
assert all(row["library"] == "VCVioInitSweepTestFixtures.Hazard"
           for row in base["accepted"]), base
PY

# --- infrastructure failures must never read as a ratchet verdict ----------------------

# A root that does not reach Mathlib cannot match any entry point. Reporting that as a
# clean tree would be the worst failure this gate can have, so it is an exit-2 instead.
expect_status 2 entry-points-absent \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Standalone \
    --check --baseline "$EMPTY_BASELINE"
grep -q "not present in the swept environment" "$FIXTURE_TMP/entry-points-absent.log"

expect_status 2 missing-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --baseline "$MISSING_BASELINE"
expect_status 2 invalid-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --baseline "$INVALID_BASELINE"
expect_status 2 empty-file-baseline \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --baseline "$ZERO_BYTE_BASELINE"
# An unparsable baseline must not be overwritten either: the rows it holds for libraries
# outside this run's roots cannot be preserved if they cannot be read.
expect_status 2 invalid-baseline-update \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --update-baseline --baseline "$INVALID_BASELINE"
grep -qx "not json" "$INVALID_BASELINE"
expect_status 2 conflicting-flags \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --check --update-baseline --baseline "$EMPTY_BASELINE"
expect_status 2 unknown-flag \
  lake exe initsweep --bogus
expect_status 2 bad-root \
  lake exe initsweep --root NoSuchModule --check --baseline "$EMPTY_BASELINE"
expect_status 2 unwritable-out \
  lake exe initsweep --root VCVioInitSweepTestFixtures.Clean \
    --out "$FIXTURE_TMP/no-such-dir/report.json"

echo "✓ Init sweep executable fixture matrix passed."
