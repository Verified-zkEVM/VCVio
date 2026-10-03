#!/usr/bin/env python3
"""Fixtures for `check-lifted-law-parity.py`: attribute kinds, flat and lifted declarations with
namespaces, the parity report, and the baseline comparison in its regression, obsolete and
matching cases."""

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("parity", HERE / "check-lifted-law-parity.py")
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)

FLAT = """\
@[simp, expect_norm]
theorem prEvent_pure (a : α) : True := trivial

theorem wp_const (c : ℝ≥0∞) : True := trivial

@[simp↓ high, grind norm↓]
theorem prFail_pure : True := trivial

theorem evalDist_pure : True := trivial

namespace Other
theorem prEvent_hidden : True := trivial
end Other
"""
OPTION = """\
namespace OptionT
@[simp, expect_norm]
theorem prEvent_pure : True := trivial
@[simp]
theorem wp_const : True := trivial
theorem wp_failure : True := trivial
end OptionT
"""
EXCEPT = """\
namespace ExceptT
@[simp, expect_norm]
theorem prEvent_pure : True := trivial
end ExceptT
"""


class ParityTests(unittest.TestCase):
    def test_attribute_kinds(self):
        self.assertEqual(parity.attribute_kinds("simp↓ high, grind norm↓, expect_eval"),
                         {"simp", "grind", "expect_eval"})
        self.assertEqual(parity.attribute_kinds(None), set())

    def test_flat_and_lifted_declarations(self):
        flat = parity.flat_laws({"a.lean": FLAT})
        self.assertEqual(set(flat), {"prEvent_pure", "wp_const", "prFail_pure"})
        self.assertEqual(flat["prEvent_pure"], {"simp", "expect_norm"})
        self.assertEqual(set(parity.lifted_laws(OPTION, "OptionT")),
                         {"prEvent_pure", "wp_const", "wp_failure"})

    def test_report(self):
        report = parity.parity(parity.flat_laws({"a.lean": FLAT}),
                               parity.lifted_laws(OPTION, "OptionT"),
                               parity.lifted_laws(EXCEPT, "ExceptT"))
        self.assertEqual(report["optionT_missing"], ["prFail_pure"])
        self.assertEqual(report["exceptT_missing"], ["prFail_pure", "wp_const"])
        self.assertEqual(report["exceptT_missing_of_optionT"], ["wp_const", "wp_failure"])
        self.assertEqual(report["attribute_mismatch"], ["wp_const: flat [], OptionT ['simp']"])

    def test_baseline_comparison(self):
        report = {c: [] for c in parity.CATEGORIES}
        report["optionT_missing"] = ["a", "b"]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "baseline.json"
            parity.write_baseline(path, report)
            self.assertEqual(parity.compare(report, parity.load_baseline(path)), [])
            regression = dict(report, optionT_missing=["a", "b", "c"])
            self.assertEqual(parity.compare(regression, parity.load_baseline(path)),
                             ["new gap (optionT_missing): c"])
            fixed = dict(report, optionT_missing=["a"])
            self.assertEqual(parity.compare(fixed, parity.load_baseline(path)),
                             ["obsolete baseline entry (optionT_missing): b"])
            self.assertEqual(json.loads(path.read_text())["optionT_missing"], ["a", "b"])


if __name__ == "__main__":
    unittest.main()
