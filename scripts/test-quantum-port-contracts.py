#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Negative controls for the compiled-contract comparator's fail-closed behavior."""

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


def fixture():
    record = {
        "name": "Example.search", "module": "Example", "kind": "theorem",
        "levelParameters": ["u"], "reducibility": "regular",
        "type": ["forall", "h", "Lean.BinderInfo.instImplicit",
                 ["const", "Example.Budget", [["param", "u"]]],
                 ["const", "Example.Success", []]],
        "typePretty": "[h : Budget] → Success", "value": None, "valuePretty": None,
    }
    definition = {
        **record, "name": "Example.game", "kind": "definition",
        "type": ["sort", ["zero"]], "typePretty": "Prop",
        "value": ["const", "True", []], "valuePretty": "True",
    }
    return {
        "format": "qrom-port-signatures-v1", "leanVersion": "test",
        "priorityHeadlines": [record["name"]],
        "provenance": {"inspectorSHA256": "0" * 64},
        "declarations": [record, definition],
    }


class Contracts(unittest.TestCase):
    def compare(self, before, after, *, modules=None, renames=()):
        with tempfile.TemporaryDirectory(prefix="qrom-contract-test-") as scratch:
            scratch = Path(scratch)
            old, new, report = (scratch / n for n in ["old.json", "new.json", "report.json"])
            old.write_text(json.dumps(before))
            new.write_text(json.dumps(after))
            tool = Path(__file__).with_name("check-quantum-port-contracts.py")
            args = [sys.executable, str(tool),
                    "compare", str(old), str(new), "--out", str(report)]
            if modules is not None:
                scope = scratch / "modules.txt"
                scope.write_text(modules)
                args += ["--modules", str(scope)]
            for rename in renames:
                args += ["--rename", rename]
            result = subprocess.run(args, capture_output=True, text=True)
            return result.returncode, json.loads(report.read_text()) if report.exists() else None

    def test_identical_nonempty_contracts(self):
        status, report = self.compare(fixture(), fixture())
        self.assertEqual(status, 0)
        self.assertEqual(report["sharedDeclarations"], 2)

    def test_dropped_budget_hypothesis(self):
        changed = fixture()
        changed["declarations"][0]["type"] = ["const", "Example.Success", []]
        status, report = self.compare(fixture(), changed)
        self.assertEqual(status, 1)
        self.assertEqual(report["summary"]["priorityRawTypeChanges"], 1)

    def test_instance_binder_becoming_explicit(self):
        changed = fixture()
        changed["declarations"][0]["type"][2] = "Lean.BinderInfo.default"
        status, report = self.compare(fixture(), changed)
        self.assertEqual(status, 1)
        self.assertEqual(report["summary"]["priorityAlphaTypeChanges"], 1)

    def test_definition_body_changes_with_same_type(self):
        changed = fixture()
        changed["declarations"][1]["value"] = ["const", "False", []]
        status, report = self.compare(fixture(), changed)
        self.assertEqual(status, 1)
        self.assertEqual(report["summary"]["rawTypeChanges"], 0)
        self.assertEqual(report["summary"]["definitionValueChanges"], 1)

    def test_missing_headline(self):
        changed = fixture()
        changed["declarations"] = changed["declarations"][1:]
        status, report = self.compare(fixture(), changed)
        self.assertEqual(status, 1)
        self.assertEqual(report["priorityMissing"], ["Example.search"])

    def test_empty_or_misspelled_module_scope(self):
        for scope in ["", "# comments only\n", "  # indented comment\n", "Misspelled\n"]:
            with self.subTest(scope=scope):
                self.assertEqual(self.compare(fixture(), fixture(), modules=scope)[0], 2)

    def test_no_shared_declarations(self):
        changed = fixture()
        for record in changed["declarations"]:
            record["name"] += "New"
        self.assertEqual(self.compare(fixture(), changed)[0], 2)

    def test_approved_rename_does_not_suppress_raw_change(self):
        changed = fixture()
        changed["declarations"][0]["type"][4] = ["const", "Example.NewSuccess", []]
        status, report = self.compare(fixture(), changed,
                                     renames=["Example.Success=Example.NewSuccess"])
        self.assertEqual(status, 1)
        self.assertEqual(report["summary"]["approvedRenameAlphaTypeChanges"], 0)
        self.assertEqual(report["summary"]["rawTypeChanges"], 1)

    def test_alpha_renaming_does_not_suppress_raw_change(self):
        changed = fixture()
        changed["declarations"][0]["type"][1] = "renamed"
        status, report = self.compare(fixture(), changed)
        self.assertEqual(status, 1)
        self.assertEqual(report["summary"]["alphaTypeChanges"], 0)

    def test_universe_renaming_is_a_separate_view(self):
        changed = fixture()
        changed["declarations"][0]["levelParameters"] = ["v"]
        changed["declarations"][0]["type"][3][2] = [["param", "v"]]
        status, report = self.compare(fixture(), changed)
        self.assertEqual(status, 1)
        self.assertEqual(report["summary"]["alphaTypeChanges"], 0)

    def test_schema_and_tool_identity_mismatch(self):
        for key in ["schema", "tool"]:
            changed = copy.deepcopy(fixture())
            if key == "schema":
                changed["format"] = "unknown"
            else:
                changed["provenance"]["inspectorSHA256"] = "1" * 64
            with self.subTest(key=key):
                self.assertEqual(self.compare(fixture(), changed)[0], 2)

    def test_duplicate_record(self):
        changed = fixture()
        changed["declarations"].append(copy.deepcopy(changed["declarations"][0]))
        self.assertEqual(self.compare(fixture(), changed)[0], 2)

    def test_kernel_failure_cannot_be_hidden_by_equal_raw_types(self):
        changed = fixture()
        changed["kernelCompatibility"] = {"declarations": [
            {"name": "Example.search", "kernelAccepted": False}]}
        status, report = self.compare(fixture(), changed)
        self.assertEqual(status, 1)
        self.assertEqual(report["kernelCompatibilityFailures"], ["Example.search"])

    def test_empty_capture_scope_fails_before_invoking_lean(self):
        with tempfile.TemporaryDirectory(prefix="qrom-empty-scope-") as scratch:
            scratch = Path(scratch)
            scope = scratch / "empty.txt"
            scope.write_text("  # comment only\n")
            tool = Path(__file__).with_name("check-quantum-port-contracts.py")
            for option in ["--modules-file", "--declarations-file"]:
                result = subprocess.run([sys.executable, str(tool), "capture", str(scratch),
                    str(scratch / "out.json"), option, str(scope)],
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, 2)
                self.assertIn("scope is empty", result.stdout)

    @unittest.skipUnless(os.environ.get("QROM_CONTRACT_KERNEL_WORKTREE"),
                         "set QROM_CONTRACT_KERNEL_WORKTREE for actual kernel controls")
    def test_actual_kernel_accepts_old_type_and_rejects_false_type(self):
        with tempfile.TemporaryDirectory(prefix="qrom-kernel-controls-") as scratch:
            scratch = Path(scratch)
            worktree = os.environ["QROM_CONTRACT_KERNEL_WORKTREE"]
            tool = Path(__file__).with_name("check-quantum-port-contracts.py")
            baseline, positive, negative = (scratch / n for n in
                ["baseline.json", "positive.json", "negative.json"])
            args = [sys.executable, str(tool), "capture", worktree,
                    str(baseline), "--root", "Lean", "--decl", "True.intro"]
            subprocess.run(args, check=True, capture_output=True, text=True)
            args[4] = str(positive)
            result = subprocess.run(args + ["--check-against", str(baseline)],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            captured = json.loads(positive.read_text())
            self.assertTrue(captured["kernelCompatibility"]["declarations"][0]["kernelAccepted"])
            old = json.loads(baseline.read_text())
            old["declarations"][0]["type"] = ["const", "False", []]
            baseline.write_text(json.dumps(old))
            args[4] = str(negative)
            result = subprocess.run(args + ["--check-against", str(baseline)],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            captured = json.loads(negative.read_text())
            self.assertFalse(captured["kernelCompatibility"]["declarations"][0]["kernelAccepted"])
            inspector = tool.with_name("QuantumPortContracts.lean")
            direct = scratch / "direct-negative.json"
            result = subprocess.run(["lake", "env", "lean", "--run", str(inspector),
                str(direct), "--root", "Lean", "--decl", "True.intro",
                "--check-against", str(baseline)], cwd=worktree,
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertFalse(json.loads(direct.read_text())["kernelCompatibility"]
                             ["declarations"][0]["kernelAccepted"])


if __name__ == "__main__":
    unittest.main()
