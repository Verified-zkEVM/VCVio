#!/usr/bin/env python3
"""Fixtures for the compile-time tables: `module_times.py` parsing Lake's `Built` lines and
overlaying them, `compare_module_times.py` pairing two tables against a budget in its over,
under, new-module and gate cases, and the budget section of the rendered timing report."""

import importlib.util
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest

HERE = pathlib.Path(__file__).resolve().parent


def load(name: str, file: str):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    module = importlib.util.module_from_spec(spec)
    # Registered before it runs: dataclasses resolve their annotations through `sys.modules`.
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


module_times = load("module_times", "module_times.py")
compare = load("compare_module_times", "compare_module_times.py")


def table(**seconds: float) -> dict:
    return {"schema_version": 1, "commit": None,
            "modules": {module.replace("_", "."): {"seconds": value, "decimals": 1}
                        for module, value in seconds.items()}}


class ModuleTimesTests(unittest.TestCase):
    def test_parse_logs_keeps_modules_and_lake_precision(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = pathlib.Path(tmp) / "build.log"
            log.write_text("✔ [1/3] Built VCVio.A (850ms)\n"
                           "✔ [2/3] Built VCVio.B (12s)\n"
                           "✔ [3/3] Built VCVio.B:c.o (3.1s)\n"
                           "✔ Built Mathlib.Order (1.2s)\n")
            built = module_times.parse_logs([log])
        self.assertEqual(built, {"VCVio.A": {"seconds": 0.85, "decimals": 3},
                                 "VCVio.B": {"seconds": 12.0, "decimals": 0}})


class CompareTests(unittest.TestCase):
    def setUp(self):
        self.base = table(VCVio_Slow=20.0, VCVio_Fast=1.0, VCVio_Steady=10.0, VCVio_Gone=3.0)
        self.current = table(VCVio_Slow=31.0, VCVio_Fast=4.0, VCVio_Steady=12.0, VCVio_New=9.0)

    def test_pairs_shared_modules_and_lists_the_rest(self):
        comparison = compare.compare(self.base, self.current)
        self.assertEqual([c.module for c in comparison.changes],
                         ["VCVio.Fast", "VCVio.Slow", "VCVio.Steady"])
        self.assertEqual(comparison.added, ["VCVio.New"])
        self.assertEqual(comparison.removed, ["VCVio.Gone"])
        self.assertEqual((comparison.total_before, comparison.total_after), (31.0, 47.0))

    def test_both_thresholds_are_needed(self):
        comparison = compare.compare(self.base, self.current)
        # Slow grew by 11s and 55%; Fast by 3s (under 5s) though 300%; Steady by 2s and 20%.
        over = compare.over_budget(comparison, 5.0, 0.5)
        self.assertEqual([c.module for c in over], ["VCVio.Slow"])
        self.assertEqual(compare.over_budget(comparison, 5.0, 0.6), [])
        self.assertEqual([c.module for c in compare.over_budget(comparison, 2.5, 0.5)],
                         ["VCVio.Slow", "VCVio.Fast"])

    def test_total_budget(self):
        comparison = compare.compare(self.base, self.current)
        self.assertTrue(compare.total_over_budget(comparison, 0.05))
        self.assertFalse(compare.total_over_budget(comparison, 0.6))

    def test_markdown_lists_the_modules_over_budget(self):
        text = compare.render_markdown(compare.compare(self.base, self.current), 5.0, 0.5, 0.05)
        self.assertIn("| `VCVio/Slow.lean` | 20.0 | 31.0 | +11.0 | 1.55 |", text)
        self.assertIn("(over budget)", text)
        quiet = compare.render_markdown(compare.compare(self.base, self.base), 5.0, 0.5, 0.05)
        self.assertIn("No module is over budget.", quiet)

    def test_gate_exit_codes(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, current = pathlib.Path(tmp) / "base.json", pathlib.Path(tmp) / "cur.json"
            base.write_text(json.dumps(self.base))
            current.write_text(json.dumps(self.current))
            self.assertEqual(compare.main([str(base), str(current)]), 0)
            self.assertEqual(compare.main([str(base), str(current), "--gate"]), 1)
            self.assertEqual(compare.main([str(base), str(base), "--gate"]), 0)
            self.assertEqual(compare.main([str(base), str(pathlib.Path(tmp) / "none.json")]), 2)


class RenderTests(unittest.TestCase):
    def test_report_has_the_budget_section(self):
        repo = HERE.parent
        with tempfile.TemporaryDirectory() as tmp:
            data = pathlib.Path(tmp)
            (data / "module-times-base.json").write_text(json.dumps(table(VCVio_Slow=20.0)))
            (data / "module-times.json").write_text(json.dumps(table(VCVio_Slow=31.0)))
            (data / "library_build.log").write_text("✔ [1/1] Built VCVio.Slow (31s)\n")
            (data / "results.jsonl").write_text(json.dumps(
                {"label": "library_build", "real": 40.0, "user": 300.0, "sys": 10.0,
                 "exit_code": 0}) + "\n")
            result = subprocess.run(
                ["bash", "scripts/build_timing_report.sh", "render", str(data / "results.jsonl")],
                cwd=repo, env=dict(os.environ, BUILD_TIMING_LOG_DIR=str(data)),
                capture_output=True, text=True, check=True)
        self.assertIn("### Modules Over Budget", result.stdout)
        self.assertIn("| `VCVio/Slow.lean` | 20.0 | 31.0 | +11.0 | 1.55 |", result.stdout)


if __name__ == "__main__":
    unittest.main()
