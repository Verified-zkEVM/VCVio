#!/usr/bin/env python3
"""Exercise semantic capture on same-name Lean environments and a JSON-only mutation.

All fixture artifacts are written outside the checkout. This is a focused R0a regression,
not a proof of a future implementation's mathematical equivalence.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess

CHECKER = Path(__file__).resolve().parents[1] / "check-slh-dsa-r0.py"
spec = importlib.util.spec_from_file_location("slh_dsa_r0", CHECKER)
assert spec and spec.loader
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)

FIXTURE = '''/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

/-! # Semantic capture fixtures -/

public section
namespace R0Fixture
structure Counts where
  hash : Nat
  sign : Nat
  verify : Nat
@[expose] def helper (c : Counts) : Nat := c.hash + c.sign + c.verify
@[expose] def observed (c : Counts) : Nat := helper c
@[expose] def Fresh (signed : List (Nat × Nat)) (candidate : Nat × Nat) : Prop := candidate ∉ signed
opaque opaqueHelper (c : Counts) : Nat := c.hash + c.sign + c.verify
@[expose] def opaqueObserved (c : Counts) : Nat := opaqueHelper c
theorem headline (q : Nat) : 0 ≤ q := Nat.zero_le q
inductive QueryKind where
  | hash | sign | verify
@[expose] def classify (kind : QueryKind) : Nat := match kind with
  | .hash => 1 | .sign => 2 | .verify => 3
end R0Fixture
'''
ROOTS = ["R0Fixture." + name for name in (
    "observed", "Fresh", "opaqueObserved", "headline", "classify")]


def command(argv: list[str], log: Path, fixture: Path | None = None) -> int:
    environment = {key: value for key, value in os.environ.items()
                   if key not in ("LEAN_PATH", "LEAN_SRC_PATH")}
    environment["LEAN_NUM_THREADS"] = "4"
    if fixture:
        environment["LEAN_PATH"] = str(fixture)
    with log.open("wb") as output:
        return subprocess.run(argv, cwd=checker.ROOT, env=environment,
                              stdout=output, stderr=subprocess.STDOUT).returncode


def capture(directory: Path, source: str, *, import_all: bool = True) -> dict | None:
    directory.mkdir()
    module = directory / "R0Fixture.lean"
    module.write_text(source)
    code = command(["lake", "env", "lean", "-DautoImplicit=false", "--root", str(directory),
                    "-o", str(directory / "R0Fixture.olean"), str(module)], directory / "compile.log")
    if code:
        raise RuntimeError(f"Fixture did not compile: {directory}")
    configuration = directory / "input.json"
    protocol = json.loads((checker.DATA / "capture-input.json").read_text())
    configuration.write_text(json.dumps({
        "names": protocol["names"] + ROOTS,
        "localModuleRoots": protocol["localModuleRoots"] + ["R0Fixture"],
    }))
    output = directory / "capture.json"
    driver = directory / "Driver.lean"
    owners = sorted({entry["module"] for entry in checker.load_table(
        checker.DATA / "semantic-fingerprints.tsv").values()})
    if any(name.split(".")[0] not in protocol["localModuleRoots"] for name in owners):
        raise ValueError("A protocol implementation owner is not repository-local")
    driver.write_text("module\n" + "".join("import all " + name + "\n" for name in owners)
                      + "import " + ("all " if import_all else "") + "R0Fixture\n"
                      + "import " + checker.CAPTURE_MODULE + "\nimport " + checker.STRENGTH_MODULE
                      + "\nslhdsa_r0_capture "
                      + json.dumps(str(configuration)) + " to " + json.dumps(str(output)) + "\n")
    code = command(["lake", "env", "lean", "-DautoImplicit=false", str(driver)],
                   directory / "capture.log", directory)
    if code:
        if import_all:
            raise RuntimeError(f"Implementation capture failed: {directory}")
        if "unavailable or axiomatic" not in (directory / "capture.log").read_text():
            raise RuntimeError("Ordinary-import fixture failed for an unexpected reason")
        return None
    return json.loads(output.read_text())


def semantic_controls(report: Path) -> list[dict]:
    original = capture(report / "original", FIXTURE)
    repeated = capture(report / "repeated", FIXTURE)
    rules = checker.load_index_compat()
    protected = checker.load_table(checker.DATA / "semantic-fingerprints.tsv")
    recovered = checker.recover_index_universes(original, rules)
    expected = checker.semantic_records(recovered)
    assert {name: expected[name] for name in protected} == protected
    assert checker.compare_semantics(expected, checker.semantic_records(
        checker.recover_index_universes(repeated, rules))) == []
    # The complete old protocol also takes the unchanged raw-comparison path.
    assert checker.compare_semantics(expected, checker.semantic_records(
        checker.recover_index_universes(recovered, rules))) == []
    additive = capture(report / "unrelated-addition", FIXTURE.replace(
        "end R0Fixture", "def unrelatedAddition : Nat := 91\nend R0Fixture"))
    assert checker.compare_semantics(expected, checker.semantic_records(
        checker.recover_index_universes(additive, rules))) == []
    opaque = next(row for row in original["records"] if row["name"] == "R0Fixture.opaqueHelper")
    assert opaque["shape"][0] == "opaque" and len(opaque["values"]) == 1
    variants = {
        "helper": FIXTURE.replace(
            "def helper (c : Counts) : Nat := c.hash + c.sign + c.verify",
            "def helper (c : Counts) : Nat := c.hash + c.sign"),
        "prop": FIXTURE.replace("candidate ∉ signed", "candidate.1 ∉ signed.map Prod.fst"),
        "premise": FIXTURE.replace("theorem headline (q : Nat) : 0 ≤ q := Nat.zero_le q",
                                    "theorem headline (q : Nat) (_positive : 0 < q) : 0 ≤ q := Nat.zero_le q"),
        "constructor": FIXTURE.replace("| hash | sign | verify", "| sign | hash | verify"),
        "opaque": FIXTURE.replace(
            "opaque opaqueHelper (c : Counts) : Nat := c.hash + c.sign + c.verify",
            "opaque opaqueHelper (c : Counts) : Nat := c.hash + c.sign"),
    }
    results = [{"control": "repeat-stability", "accepted": True},
               {"control": "imported-nonexposed-opaque-body", "accepted": True}]
    for label, source in variants.items():
        actual = capture(report / label, source)
        assert actual["selected"] == original["selected"]
        records = checker.semantic_records(checker.recover_index_universes(actual, rules))
        differences = checker.compare_semantics(expected, records)
        assert differences, f"Semantic mutation escaped: {label}"
        if label in ("helper", "opaque"):
            anchor = "R0Fixture." + ("observed" if label == "helper" else "opaqueObserved")
            assert expected[anchor] == records[anchor], "Direct anchor changed rather than its helper"
        if label == "prop":
            assert expected["R0Fixture.Fresh"]["type"] == records["R0Fixture.Fresh"]["type"]
            assert "changed bodies: R0Fixture.Fresh" in differences
        if label == "premise":
            assert "changed type: R0Fixture.headline" in differences
        if label == "constructor":
            assert any("changed metadata:" in value for value in differences)
        results.append({"control": label, "accepted": True, "differences": differences})
    ordinary = capture(report / "ordinary-import", FIXTURE, import_all=False)
    if ordinary is not None:
        row = next(r for r in ordinary["records"] if r["name"] == "R0Fixture.opaqueHelper")
        assert row["shape"][0] == "opaque" and row["values"]
    results.append({"control": "ordinary-import-unavailable-body-fails-closed", "accepted": True,
                    "bodyAvailable": ordinary is not None})
    results += protocol_controls(original, rules)
    return results


def protocol_controls(original: dict, rules: dict) -> list[dict]:
    """Mutate serialized actual index slots, never the expected baseline or adapter data."""
    import copy

    def row(capture: dict, name: str) -> dict:
        return next(value for value in capture["records"] if value["name"] == name)

    def site_node(capture: dict, site: dict) -> list:
        node = row(capture, site["caller"])
        for key in site["path"]:
            node = node[key]
        return node

    results = []

    def reject(label: str, actual: dict) -> None:
        try:
            checker.recover_index_universes(actual, rules)
        except ValueError as error:
            results.append({"control": label, "accepted": True, "rejection": str(error),
                            "kind": "serialized-capture protocol mutation"})
        else:
            raise AssertionError(f"Invalid indexed protocol escaped: {label}")

    for number, site in enumerate(rules["referenceSites"]):
        actual = copy.deepcopy(original)
        node = site_node(actual, site)
        # A blind last-slot drop would erase this genuine extra-index mismatch.
        node[2][site["indexPosition"]] = ["succ", node[2][site["indexPosition"]]]
        reject(f"index-site-{number}", actual)
    for label in ("retained-role", "target-name", "moved-site", "duplicate-site"):
        actual = copy.deepcopy(original)
        site = rules["referenceSites"][0]
        node = site_node(actual, site)
        if label == "retained-role":
            node[2][0] = ["succ", node[2][0]]
        elif label == "target-name":
            node[1] = ["str", ["anonymous"], "UnknownTarget"]
        else:
            parent = row(actual, site["caller"])
            for key in site["path"][:-1]:
                parent = parent[key]
            # Both forms move the actual const; one also creates another occurrence.
            parent[site["path"][-1]] = ["app", node,
                copy.deepcopy(node) if label == "duplicate-site" else ["lit", "nat", 0]]
        reject(label, actual)
    for label in ("unknown-parameter", "retained-role-order", "mixed-mode", "missing-owner"):
        actual = copy.deepcopy(original)
        rule = rules["declarationMaps"][1]
        target = row(actual, rule["name"])
        if label == "unknown-parameter":
            target["levels"].append("unknown")
            target["levelNames"].append(["str", ["anonymous"], "unknown"])
        elif label == "retained-role-order":
            target["levels"][0:2] = reversed(target["levels"][0:2])
            target["levelNames"][0:2] = reversed(target["levelNames"][0:2])
        elif label == "mixed-mode":
            target["levels"] = rule["oldLevels"]
            target["levelNames"] = rule["oldLevelNames"]
        else:
            actual["records"].remove(target)
        reject(label, actual)
    return results


def json_control(report: Path) -> list[dict]:
    artifact = checker.DATA / "kernel-types.json"
    saved = artifact.read_bytes()
    try:
        bundle = json.loads(saved)
        # A JSON-only change must fail even when all .olean files are already warm.
        bundle["contracts"][0]["kind"] = "unsupported"
        artifact.write_text(json.dumps(bundle, separators=(",", ":")) + "\n")
        code = command(["python3", str(CHECKER), "--report-dir", str(report / "json-verifier")],
                       report / "json-verifier.log")
        assert code == 1
        failure = json.loads((report / "json-verifier/result.json").read_text())
        assert "Frozen artifact changed" in failure["error"]
        module = json.loads((checker.DATA / "capture-input.json").read_text())["witnessModules"][0]
        code = command(["lake", "env", "lean", "-DautoImplicit=false",
                        module.replace(".", "/") + ".lean"], report / "json-fresh-kernel.log")
        assert code != 0
        assert "Unsupported contract witness kind" in (report / "json-fresh-kernel.log").read_text()
    finally:
        artifact.write_bytes(saved)
    assert artifact.read_bytes() == saved
    return [{"control": "json-only-verifier-rejects-with-warm-cache", "accepted": True},
            {"control": "json-only-fresh-elaboration-executes", "accepted": True}]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-dir", type=Path, required=True)
    parser.add_argument("--skip-json-control", action="store_true")
    args = parser.parse_args()
    report = args.report_dir.resolve()
    if report.is_relative_to(checker.ROOT):
        parser.error("Use a report directory outside the checkout")
    report.mkdir(parents=True, exist_ok=True)
    if any(report.iterdir()):
        parser.error("Use an empty report directory")
    before = checker.frame()
    results = semantic_controls(report)
    if not args.skip_json_control:
        results += json_control(report)
    after = checker.frame()
    assert before == after, "The controls left source or dependencies changed"
    packet = {"accepted": True, "controls": results, "before": before, "after": after}
    (report / "result.json").write_text(json.dumps(packet, indent=2) + "\n")
    print(json.dumps({"accepted": True, "controls": len(results), "reportDir": str(report)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
