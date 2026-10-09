#!/usr/bin/env python3
"""Check the SPMF import-closure ratchet on a fixture tree, without invoking Lake."""

from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("check-spmf-closure.py")


class SpmfClosureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="vcvio-spmf-closure-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.baseline = self.root / "baseline.txt"
        self.write("ToMathlib/ProbabilityTheory/SPMF.lean", "module\n")
        self.write("VCVio/Legacy.lean", "module\npublic import ToMathlib.ProbabilityTheory.SPMF\n")
        self.write("VCVio/Client.lean", "module\npublic import VCVio.Legacy\n")
        self.write("VCVio/Native.lean", "module\nimport Mathlib.Order.Basic\n")
        # Umbrellas at the repository root are not tracked.
        (self.root / "VCVio.lean").write_text("module\npublic import VCVio.Legacy\n")

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def run_check(self, *extra):
        return subprocess.run(
            ["python3", str(SCRIPT), "--root", str(self.root), "--baseline", str(self.baseline),
             *extra],
            text=True, capture_output=True, timeout=30,
        )

    def test_exact_baseline_passes(self):
        self.baseline.write_text("VCVio.Client\nVCVio.Legacy\n")
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_new_module_reaching_spmf_fails(self):
        self.baseline.write_text("VCVio.Legacy\n")
        result = self.run_check()
        self.assertEqual(result.returncode, 1)
        self.assertIn("VCVio.Client", result.stderr)

    def test_obsolete_entry_fails_and_prunes(self):
        self.baseline.write_text("VCVio.Client\nVCVio.Legacy\nVCVio.Native\n")
        result = self.run_check()
        self.assertEqual(result.returncode, 1)
        self.assertIn("VCVio.Native", result.stderr)
        pruned = self.run_check("--prune-baseline")
        self.assertEqual(pruned.returncode, 0, pruned.stderr)
        self.assertEqual(self.baseline.read_text(), "VCVio.Client\nVCVio.Legacy\n")

    def test_prune_refuses_additions(self):
        self.baseline.write_text("VCVio.Legacy\n")
        result = self.run_check("--prune-baseline")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.baseline.read_text(), "VCVio.Legacy\n")

    def test_import_cycle_terminates(self):
        self.write("VCVio/A.lean", "module\nimport VCVio.B\n")
        self.write("VCVio/B.lean", "module\nimport VCVio.A\n")
        self.baseline.write_text("VCVio.Client\nVCVio.Legacy\n")
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
