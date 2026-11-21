#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Exercise library import boundaries, including Lean import modifiers."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class IsolationTests(unittest.TestCase):
    def check(self, files, extern=False):
        with tempfile.TemporaryDirectory(prefix="vcvio-interop-isolation-") as temp:
            root = Path(temp)
            (root / "scripts").mkdir()
            shutil.copyfile(Path(__file__).with_name("check-interop-isolation.sh"),
                            root / "scripts/check-interop-isolation.sh")
            shutil.copyfile(Path(__file__).with_name("check-extern-isolation.sh"),
                            root / "scripts/check-extern-isolation.sh")
            shutil.copyfile(Path(__file__).with_name("CheckImports.lean"),
                            root / "scripts/CheckImports.lean")
            shutil.copyfile(Path(__file__).resolve().parents[1] / "lean-toolchain",
                            root / "lean-toolchain")
            for name, source in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            script = "check-extern-isolation.sh" if extern else "check-interop-isolation.sh"
            return subprocess.run(["bash", f"scripts/{script}"], cwd=root,
                                  text=True, capture_output=True, timeout=10)

    def test_forbidden_edges_and_modifiers(self):
        edges = [("VCVio/Algorithms/X.lean", "VCVio.OracleComp"),
                 ("VCVio/Algorithms/X.lean", "HashSig"),
                 ("VCVio/Algorithms/X.lean", "Interop.Aeneas.Hax"),
                 ("HashSig/X.lean", "Interop.Aeneas.Lift"),
                 ("VCVio.lean", "Interop"),
                 ("VCVioTest/X.lean", "Hax"),
                 ("Interop/Aeneas/Hax/X.lean", "HashSig")]
        for source, target in edges:
            for modifier in ("import", "public import", "import all", "public meta import", "public/-comment-/import",
                             "public\nimport", "import\n"):
                with self.subTest(source=source, target=target, modifier=modifier):
                    result = self.check({source: f"module\n{modifier} {target}\n"})
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(f"forbidden import {target}", result.stderr)

    def test_allowed_edges_comments_and_multiple_imports(self):
        result = self.check({
            "Interop/Aeneas/Hax/X.lean": "import VCVio\nimport ToMathlib\n"
                                         "import Interop.Aeneas.Lift.RustM\n",
            "HashSig/X.lean": "import VCVio\n/- outer /- nested -/ import Interop -/\n",
            "VCVio/Schemes/X.lean": "module\npublic import VCVio.CryptoFoundations.X\n",
            "VCVio/Algorithms/X.lean": "import Mathlib\nimport ToMathlib\nimport PolyFun\nimport VCVio.Algorithms.Y\n",
            "VCVio/Strings.lean": 'def text := "\nimport Interop\n"\n',
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        result = self.check({"HashSig/X.lean": "import Mathlib\nimport Interop.Cryptol.Model\n"})
        self.assertNotEqual(result.returncode, 0)

    def test_imports_between_interop_subprojects(self):
        allowlist = "scripts/interop_import_allowlist.txt"
        edges = [("Interop/Other/X.lean", "Interop.Aeneas.Lift.RustM"),
                 ("Interop/Aeneas/Hax/X.lean", "Interop.Other.Model"),
                 ("Interop/Aeneas/X.lean", "Interop.Other"),
                 ("Interop/Aeneas/X.lean", "Interop"),
                 ("Interop.lean", "Interop.Aeneas.WP")]
        for source, target in edges:
            with self.subTest(source=source, target=target):
                result = self.check({source: f"module\npublic import {target}\n"})
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(f"{source}: forbidden import {target} from another Interop "
                              "sub-project", result.stderr)
        listed = "# importer imported\nOther\tAeneas # through a `require`\n\n"
        result = self.check({"Interop/Other/X.lean": "import Interop.Aeneas.Lift.RustM\n"
                                                     "import Interop.Other.Y\n",
                             "Interop/Aeneas/X.lean": "import Interop.Aeneas.Lift.RustM\n",
                             allowlist: listed})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        # A pair allows one direction only.
        result = self.check({"Interop/Aeneas/X.lean": "import Interop.Other.Y\n",
                             allowlist: listed})
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("forbidden import Interop.Other.Y", result.stderr)
        result = self.check({"Interop/Other/X.lean": "import VCVio\n",
                             allowlist: "Other Aeneas Extra\n"})
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("expected `<importer> <imported>`", result.stderr)

    def test_extern_boundary(self):
        for source in ("VCVio.lean", "VCVio/X.lean", "HashSig/X.lean", "Interop/Aeneas/Hax/X.lean"):
            result = self.check({source: "module\npublic import all Extern.X\n"}, extern=True)
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("forbidden import Extern.X", result.stderr)
        result = self.check({"VCVioTest/X.lean": "import Extern.X\n",
                             "Extern/X.lean": "import Extern.Y\n"}, extern=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_nested_lakefile_and_umbrella_chain(self):
        for extern, target in ((False, "Interop.Hidden"), (True, "Extern.Hidden")):
            for chained in (False, True):
                with self.subTest(extern=extern, chained=chained):
                    files = {"VCVio/lakefile.lean": f"module\npublic import {target}\n"}
                    if chained:
                        files["VCVio.lean"] = "module\npublic import VCVio.lakefile\n"
                        files[target.replace(".", "/") + ".lean"] = "module\n"
                    result = self.check(files, extern=extern)
                    self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                    self.assertIn(f"VCVio/lakefile.lean: forbidden import {target}",
                                  result.stderr)

    def test_algorithms_umbrella_forbidden_import(self):
        result = self.check({
            "VCVio/Algorithms.lean": "module\npublic import VCVio.OracleComp.OracleComp\n",
            "VCVio/Algorithms/User.lean": "module\npublic import VCVio.Algorithms\n",
        })
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("VCVio/Algorithms.lean: forbidden import VCVio.OracleComp.OracleComp",
                      result.stderr)

    def test_algorithms_umbrella_allowed_imports(self):
        result = self.check({
            "VCVio/Algorithms.lean": "module\npublic import VCVio.Algorithms.X\nimport Mathlib\n",
            "VCVio/Algorithms/X.lean": "import ToMathlib\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
