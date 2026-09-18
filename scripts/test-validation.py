#!/usr/bin/env python3
"""Exercise validation failure propagation with lightweight command substitutes."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class ValidationTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="vcvio-validation-")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        source = Path(__file__).parent
        for name in ("validate.sh", "build-project.sh", "check-warning-log.py"):
            shutil.copy2(source / name, scripts / name)
        for name in ("check-imports", "test-polyfun-boundary", "check-polyfun-boundary",
                     "test-expose-boundary",
                     "check-expose-boundary", "test-complexity-backend-isolation",
                     "check-complexity-backend-isolation", "check-extern-isolation",
                     "check-interop-isolation", "test-axiomsweep",
                     "test-comment-fences", "test-initsweep"):
            self.script(scripts / f"{name}.sh", 'exit 0\n')
        for name in ("test-check-imports.py", "test-validation.py", "test-lint.py", "check-agent-docs.py",
                     "extract-doc-fragments.py"):
            (scripts / name).write_text("pass\n")
        # Not a no-op stub: the default pass has to be shown to reach it.
        (scripts / "check-comment-fences.py").write_text(
            'print("comment fences: stub")\n')
        binary = self.root / "bin"
        binary.mkdir()
        self.script(binary / "lake", '''
printf '%s\\n' "$*" >> "$VALIDATION_CALLS"
if [ "$1" = test ]; then
  printf '%s\\n' "${VALIDATION_WARNING:-}"
  exit "${VALIDATION_TEST_EXIT:-0}"
fi
''')
        self.script(binary / "git", 'exit 0\n')
        self.env = dict(os.environ, PATH=f"{binary}{os.pathsep}{os.environ['PATH']}",
                        VALIDATION_CALLS=str(self.root / "calls"))

    @staticmethod
    def script(path, body):
        path.write_text("#!/usr/bin/env bash\nset -eu\n" + body)
        path.chmod(0o755)

    def validate(self, *args, wrapper=False, **env):
        name = "build-project.sh" if wrapper else "validate.sh"
        return subprocess.run(["bash", f"scripts/{name}", *args], cwd=self.root,
                              env=dict(self.env, **env), text=True, capture_output=True,
                              timeout=15)

    def test_clean_tests_pass(self):
        result = self.validate("--test")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("validate: OK.", result.stdout)
        self.assertIn("test", (self.root / "calls").read_text().splitlines())

    def test_lint_selectors_reuse_the_completed_build(self):
        result = self.validate("--lint")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = (self.root / "calls").read_text().splitlines()
        self.assertIn("lint -- --style-only", calls)
        self.assertIn("lint -- --env-only --no-build", calls)
        self.assertEqual(sum(call.startswith("build ") for call in calls), 1)

    def test_each_test_library_warning_fails(self):
        for library in ("VCVioTest", "LatticeCryptoTest", "HashSigTest"):
            with self.subTest(library=library):
                result = self.validate("--test", VALIDATION_WARNING=
                                       f"warning: {library}/Canary.lean:1:1: unused tactic")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("test-library warnings", result.stdout + result.stderr)

    def test_dependency_sorry_does_not_spend_test_budget(self):
        result = self.validate("--test", VALIDATION_WARNING=
                               "warning: VCVio/Existing.lean:1:1: declaration uses `sorry`")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_test_failure_survives_tee(self):
        for flags in (("--test",), ("--test", "--ffi")):
            with self.subTest(flags=flags):
                result = self.validate(*flags, VALIDATION_TEST_EXIT="7")
                self.assertEqual(result.returncode, 7, result.stdout + result.stderr)

    def test_ffi_wrapper_preserves_other_flags(self):
        result = self.validate("--ffi", "--axioms", wrapper=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = (self.root / "calls").read_text().splitlines()
        self.assertIn("test -- --ffi", calls)
        self.assertIn("exe axiomsweep --check", calls)

    def test_comment_fences_run_in_the_default_pass(self):
        result = self.validate()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("comment fences: stub", result.stdout)

    def test_init_sweep_runs_in_the_default_pass(self):
        result = self.validate()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = (self.root / "calls").read_text().splitlines()
        self.assertIn("exe initsweep --check", calls)
        # The test libraries cannot be swept before `lake test` has built their oleans.
        self.assertNotIn("exe initsweep --check --root VCVioTest --root LatticeCryptoTest",
                         calls)

    def test_init_sweep_covers_the_umbrella_test_libraries_after_lake_test(self):
        result = self.validate("--test")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        calls = (self.root / "calls").read_text().splitlines()
        self.assertIn("exe initsweep --check --root VCVioTest --root LatticeCryptoTest",
                      calls)
        self.assertLess(calls.index("test"),
                        calls.index("exe initsweep --check --root VCVioTest "
                                    "--root LatticeCryptoTest"))


if __name__ == "__main__":
    unittest.main()
