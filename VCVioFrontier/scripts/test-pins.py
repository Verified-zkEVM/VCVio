"""Run the dependency-isolation fixtures without downloading Lake packages."""

import json
from pathlib import Path
import runpy
import tempfile
import unittest


PINS = runpy.run_path(str(Path(__file__).with_name("check-pins.py")))


class FrontierPins(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.package = self.root / "VCVioFrontier"
        self.package.mkdir()
        (self.root / "lakefile.lean").write_text("require PolyFun from git\n")
        (self.root / "lake-manifest.json").write_text('{"packages": []}')

    def test_root_without_updated_lockfile(self):
        lakefile = self.root / "lakefile.lean"
        lakefile.write_text("/- require «cslib-frontier» /- nested -/ -/\nrequire PolyFun from git\n")
        PINS["check_root"](self.root)
        for requirement in ('«cslib-frontier»', '"cslib-community" / "cslib-frontier"',
                            'PolyFunFrontier', 'VCVioFrontier'):
            with self.subTest(requirement=requirement):
                lakefile.write_text(f"require /- comment -/\n {requirement} from git\n")
                with self.assertRaisesRegex(SystemExit, "optional dependency"):
                    PINS["check_root"](self.root)

    def test_stale_root_manifest(self):
        (self.root / "lake-manifest.json").write_text('{"packages":[{"name":"«cslib-frontier»"}]}')
        with self.assertRaisesRegex(SystemExit, "unexpectedly resolves"):
            PINS["check_root"](self.root)

    def test_polyfun_locations(self):
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            (self.package / name).write_bytes((PINS["ROOT"] / name).read_bytes())
        for name in ("PolyFunFrontier/PolyFunFrontier", "cslib-frontier"):
            peer = self.package / ".lake/packages" / name
            peer.mkdir(parents=True)
            (peer / "lake-manifest.json").write_text('{"packages":[]}')
            (peer / "lean-toolchain").write_bytes((self.package / "lean-toolchain").read_bytes())
        lock = self.package / "lake-manifest.json"
        original = lock.read_text()
        PINS["check"](self.package)
        for field, value in (("url", "https://example.org/PolyFun"), ("subDir", None),
                             ("rev", "1" * 40)):
            with self.subTest(field=field):
                manifest = json.loads(original)
                next(p for p in manifest["packages"] if p["name"] == "PolyFunFrontier")[field] = value
                lock.write_text(json.dumps(manifest))
                with self.assertRaisesRegex(SystemExit, "PolyFunFrontier"):
                    PINS["check"](self.package)


if __name__ == "__main__":
    unittest.main()
