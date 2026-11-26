#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Exercise the listing of `Interop/` sub-projects and of their axiom-sweep roots."""

from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("interop-subprojects.py")


class SubprojectTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="vcvio-interop-subprojects-")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)

    def lakefile(self, sub, text):
        path = self.root / "Interop" / sub / "lakefile.toml"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def run_script(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), *args], cwd=self.root, text=True,
                              capture_output=True, timeout=10)

    def test_list_takes_every_directory_with_a_lakefile(self):
        self.lakefile("Beta", 'name = "B"\n')
        self.lakefile("Alpha", 'name = "A"\n')
        (self.root / "Interop/Notes").mkdir()
        (self.root / "Interop/README.md").write_text("index\n")
        result = self.run_script("list")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), ["Alpha", "Beta"])

    def test_roots_are_those_of_the_default_libraries(self):
        self.lakefile("A", '\n'.join([
            'name = "A"', 'defaultTargets = ["Main", "Named", "tool"]',
            '[[lean_lib]]', 'name = "Main"', 'roots = ["Interop.A.X", "Interop.A.Y"]',
            '[[lean_lib]]', 'name = "Named"',
            '[[lean_lib]]', 'name = "Generated"', 'globs = ["Interop.A.Gen.+"]',
            '[[lean_exe]]', 'name = "tool"', '']))
        result = self.run_script("roots", "Interop/A")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(), ["Interop.A.X", "Interop.A.Y", "Named"])

    def test_roots_refuse_an_empty_or_glob_only_sweep(self):
        cases = {
            "no default library": 'name = "A"\n[[lean_lib]]\nname = "L"\nroots = ["M"]\n',
            "glob-only default": 'name = "A"\ndefaultTargets = ["L"]\n'
                                 '[[lean_lib]]\nname = "L"\nglobs = ["Interop.A.+"]\n',
            "empty roots": 'name = "A"\ndefaultTargets = ["L"]\n'
                           '[[lean_lib]]\nname = "L"\nroots = []\n',
        }
        for case, text in cases.items():
            with self.subTest(case=case):
                self.lakefile("A", text)
                result = self.run_script("roots", "Interop/A")
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

    def test_repository_subprojects_have_sweep_roots(self):
        repo = SCRIPT.resolve().parents[1]
        listed = subprocess.run([sys.executable, str(SCRIPT), "list"], cwd=repo, text=True,
                                capture_output=True, check=True, timeout=10)
        subs = json.loads(listed.stdout)
        self.assertIn("Aeneas", subs)
        for sub in subs:
            with self.subTest(sub=sub):
                roots = subprocess.run([sys.executable, str(SCRIPT), "roots", f"Interop/{sub}"],
                                       cwd=repo, text=True, capture_output=True, timeout=10)
                self.assertEqual(roots.returncode, 0, roots.stderr)
                for root in roots.stdout.split():
                    self.assertTrue(root.startswith(f"Interop.{sub}."), root)
                    self.assertTrue((repo / (root.replace(".", "/") + ".lean")).is_file(), root)


if __name__ == "__main__":
    unittest.main()
