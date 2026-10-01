#!/usr/bin/env python3
"""Fixtures for `spec-coverage.py`: a wrapped trace line, a failed application that does not
count, a rule passed in brackets, the matrix over an injected inventory, and the baseline
comparison in its regression, obsolete and matching cases."""

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("coverage", HERE / "spec-coverage.py")
coverage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(coverage)

TRACE_A = """\
[Elab.Tactic.Do.vcgen] 📜 Program: $ᵗ Bool
[Elab.Tactic.Do.vcgen] Applying spec SpecProof.global OracleComp.Lower.Spec.uniformSample_sum for $ᵗ
      Bool. Excess args: []
[Elab.Tactic.Do.vcgen] Failed to apply spec SpecProof.global OracleComp.Necessary.Spec.uniformSample for $ᵗ Bool
[Elab.Tactic.Do.vcgen] Applying spec SpecProof.global OracleComp.Upper.Spec.uniformSample for $ᵗ Bool. Excess args: []
[Elab.Tactic.Do.vcgen] Applying spec SpecProof.global OracleComp.Upper.Spec.uniformSample for $ᵗ Bool. Excess args: []
"""
TRACE_B = """\
[Elab.Tactic.Do.vcgen] Applying spec SpecProof.local OracleComp.Possible.Spec.replicate for replicate 2 ($ᵗ Bool). Excess args: []
"""
RULES = ["OracleComp.Lower.Spec.uniformSample_sum", "OracleComp.Necessary.Spec.uniformSample",
         "OracleComp.Possible.Spec.replicate", "OracleComp.Upper.Spec.uniformSample",
         "Std.WP.Spec.mapM_list"]


class SpecCoverageTests(unittest.TestCase):
    def test_parse_counts_applications_only(self):
        self.assertEqual(coverage.parse_trace(TRACE_A), {
            "OracleComp.Lower.Spec.uniformSample_sum": 1,
            "OracleComp.Upper.Spec.uniformSample": 2})

    def test_matrix_and_uncovered(self):
        matrix = coverage.coverage(RULES, {"A.lean": TRACE_A, "B.lean": TRACE_B})
        self.assertEqual(matrix["OracleComp.Upper.Spec.uniformSample"], {"A.lean": 2})
        self.assertEqual(matrix["OracleComp.Possible.Spec.replicate"], {"B.lean": 1})
        self.assertEqual(coverage.uncovered(matrix), [
            "OracleComp.Necessary.Spec.uniformSample", "Std.WP.Spec.mapM_list"])

    def test_compare_regression_obsolete_and_match(self):
        self.assertEqual(coverage.compare(["a", "b"], ["b", "c"]), (["a"], ["c"]))
        self.assertEqual(coverage.compare(["b"], ["b"]), ([], []))

    def test_baseline_round_trip(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "baseline.json"
            coverage.write_baseline(path, ["z", "a"])
            self.assertEqual(json.loads(path.read_text())["uncovered"], ["a", "z"])
            self.assertEqual(coverage.load_baseline(path), ["a", "z"])
            self.assertEqual(coverage.load_baseline(Path(tmp) / "missing.json"), [])

    def test_render_has_a_column_per_file(self):
        matrix = coverage.coverage(RULES[:1], {"A.lean": TRACE_A, "B.lean": TRACE_B})
        table = coverage.render(matrix, ["A.lean", "B.lean"])
        self.assertIn("| Rule | A | B |", table)
        self.assertIn("| `OracleComp.Lower.Spec.uniformSample_sum` | 1 |  |", table)


if __name__ == "__main__":
    unittest.main()
