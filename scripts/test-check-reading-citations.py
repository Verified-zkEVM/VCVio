#!/usr/bin/env python3
"""Fixtures for `check-reading-citations.py`: a resolving citation, a dead path, a line past the
end of a file, a range and a list checked at their first number, and an upstream tree that is
skipped unless required."""

import importlib.util
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("checker", HERE / "check-reading-citations.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class CitationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        (root / "Lib").mkdir()
        (root / "Lib" / "Short.lean").write_text("line 1\nline 2\nline 3\n")
        self.roots = {"V": [root], "M": [], "B": [], "Cs": [], "P": [], "C": []}
        self.doc = root / "doc.md"

    def tearDown(self):
        self.tmp.cleanup()

    def run_check(self, text, require_upstream=False):
        self.doc.write_text(text)
        return checker.check_file(self.doc, self.roots, require_upstream, {})

    def test_resolving_citations_pass(self):
        failures, checked, _ = self.run_check(
            "see `V:Lib/Short.lean:2`, `V:Lib/Short.lean:1–3`, `V:Lib/Short.lean:3,9` and "
            "`V:Lib/Short.lean`")
        self.assertEqual(failures, [])
        self.assertEqual(checked, 4)

    def test_dead_path_and_past_end_fail(self):
        failures, _, _ = self.run_check("`V:Lib/Gone.lean:1` and `V:Lib/Short.lean:4`")
        self.assertEqual(len(failures), 2)
        self.assertIn("does not exist", failures[0])
        self.assertIn("runs past the end of the file (3 lines)", failures[1])

    def test_missing_upstream_tree_is_skipped_unless_required(self):
        failures, checked, skipped = self.run_check("`M:Data/Nat.lean:1`")
        self.assertEqual((failures, checked, skipped), ([], 0, {"M"}))
        failures, _, _ = self.run_check("`M:Data/Nat.lean:1`", require_upstream=True)
        self.assertEqual(len(failures), 1)
        self.assertIn("not checked out", failures[0])

    def test_abbreviated_and_prose_forms_are_not_citations(self):
        failures, checked, _ = self.run_check(
            "`M:…/Lebesgue/Map.lean:27` is abbreviated; https://x.test/C:Init/Core.lean too")
        self.assertEqual((failures, checked), ([], 0))


if __name__ == "__main__":
    unittest.main()
