#!/usr/bin/env python3
"""Fixtures for `classify-migration-errors.py`: the kind and name of each error message shape,
the codemod lookup of an unknown name, the scope of a file, and the CSV and summary of a run."""

import csv
import importlib.util
import pathlib
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("classify", HERE / "classify-migration-errors.py")
classify = importlib.util.module_from_spec(spec)
sys.modules["classify"] = classify
spec.loader.exec_module(classify)

LOG = """\
✖ [10/12] Building VCVio.New.Proof (1.2s)
error: VCVio/New/Proof.lean:12:4: Unknown identifier `probOutput_bind`
error: VCVio/New/Proof.lean:20:2: Unknown constant `OracleComp.notAThing`
error: VCVio/New/Proof.lean:31:0: failed to synthesize instance of type class
error: VCVio/Shared.lean:7:9: Type mismatch
error: Examples/Uses.lean:3:0: unsolved goals
error: VCVio/New/Proof.lean:40:2: unexpected token 'at'; expected term
"""


class ClassifyTests(unittest.TestCase):
    def test_kinds_and_names(self):
        self.assertEqual(classify.classify("Unknown identifier `foo`"), ("unknown-name", "foo"))
        self.assertEqual(classify.classify("unknown identifier 'bar'"), ("unknown-name", "bar"))
        self.assertEqual(classify.classify("bad import 'VCVio.Gone'"),
                         ("unknown-module", "VCVio.Gone"))
        self.assertEqual(classify.classify("failed to synthesize\n  Fintype X")[0], "instance")
        self.assertEqual(classify.classify("Application type mismatch")[0], "type-mismatch")
        self.assertEqual(classify.classify("Tactic `rewrite` failed")[0], "tactic-failed")
        self.assertEqual(classify.classify("something else")[0], "other")

    def test_codemod_lookup(self):
        renames = {"probOutput_bind": "prEvent_bind", "OracleComp.evalDist_x": "evalDist_y"}
        hints = {"IsUniformSpec": "use UniformAnswerMeasure"}
        self.assertEqual(classify.known("probOutput_bind", renames, hints), "rename")
        self.assertEqual(classify.known("OracleComp.probOutput_bind", renames, hints), "rename")
        self.assertEqual(classify.known("evalDist_x", renames, hints), "rename")
        self.assertEqual(classify.known("IsUniformSpec", renames, hints), "hint")
        self.assertEqual(classify.known("brandNew", renames, hints), "")

    def test_rows_csv_and_summary(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = pathlib.Path(tmp)
            pr = out / "pr-7"
            pr.mkdir()
            (pr / "build.log").write_text(LOG)
            (pr / "pr-files.txt").write_text("VCVio/New/Proof.lean\nVCVio/Shared.lean\n")
            (pr / "shared-files.txt").write_text("VCVio/Shared.lean\n")
            (pr / "status.txt").write_text("failed\n")
            self.assertEqual(classify.main([str(out)]), 0)
            with (out / "migration-dry-run.csv").open() as handle:
                rows = list(csv.DictReader(handle))
            self.assertEqual(len(rows), 6)
            self.assertEqual([row["scope"] for row in rows],
                             ["pr", "pr", "pr", "shared", "other", "pr"])
            self.assertEqual(rows[0]["name"], "probOutput_bind")
            summary = (out / "summary.md").read_text()
        self.assertIn("| #7 | failed | 6 | 4 | 1 | 1 |", summary)
        self.assertIn("`probOutput_bind`", summary)


if __name__ == "__main__":
    unittest.main()
