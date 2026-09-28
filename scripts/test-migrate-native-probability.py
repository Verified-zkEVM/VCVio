#!/usr/bin/env python3
"""Check the downstream probability codemod on fixture sources, without invoking Lake."""

from pathlib import Path
import importlib.util
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("migrate-native-probability.py")
spec = importlib.util.spec_from_file_location("migrate_native_probability", SCRIPT)
codemod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(codemod)


def migrate(text):
    report = codemod.Report()
    return codemod.migrate(text, "Fixture.lean", report), report.items


class EventTests(unittest.TestCase):
    def assertMigrates(self, source, expected):
        self.assertEqual(migrate(source)[0], expected)

    def test_singleton_events(self):
        self.assertMigrates("Pr[= a | mx]", "Pr{mx}[= a]")
        self.assertMigrates("Pr[(· = f a) | g <$> mx]", "Pr{g <$> mx}[= f a]")

    def test_function_events(self):
        self.assertMigrates("Pr[fun x => x.1 = a | mx]", "Pr{x ← mx}[x.1 = a]")
        self.assertMigrates("Pr[fun x ↦ p x | mx]", "Pr{x ← mx}[p x]")
        self.assertMigrates("Pr[(fun z : ℕ => z > 3) | mx]", "Pr{z ← mx}[z > 3]")
        self.assertMigrates("Pr[fun (z : α × β) => p z.1 | mx]", "Pr{z ← mx}[p z.1]")
        self.assertMigrates("Pr[fun ⟨a, b⟩ => a = b | mx]", "Pr{let ⟨a, b⟩ ← mx}[a = b]")

    def test_sections_and_predicates(self):
        self.assertMigrates("Pr[(· ∈ S) | mx]", "Pr{x ← mx}[x ∈ S]")
        self.assertMigrates("Pr[p | mx]", "Pr{x ← mx}[p x]")
        self.assertMigrates("Pr[S.contains | mx]", "Pr{x ← mx}[S.contains x]")
        self.assertMigrates("Pr[q ∘ f | mx]", "Pr{x ← mx}[(q ∘ f) x]")
        # The bound name avoids the names the event and computation use.
        self.assertMigrates("Pr[p x | f x]", "Pr{y ← f x}[(p x) y]")

    def test_failure_event(self):
        self.assertMigrates("Pr[⊥ | mx] = 0", "(1 - Pr{_ ← mx}[True]) = 0")

    def test_multiline_computation(self):
        source = "Pr[= true | do\n    let y ← mx\n    pure y]"
        self.assertMigrates(source, "Pr{do\n    let y ← mx\n    pure y}[= true]")

    def test_nested_events(self):
        self.assertMigrates("Pr[= a | mx] ≤ Pr[p | my] + ε", "Pr{mx}[= a] ≤ Pr{x ← my}[p x] + ε")

    def test_unparsed_event_is_reported(self):
        out, items = migrate("theorem t : Pr[(· + ·) | mx] = 0 := sorry")
        self.assertIn("Pr[(· + ·) | mx]", out)
        self.assertEqual([(line, "legacy event" in msg) for _, line, msg in items], [(1, True)])

    def test_prose_in_comments_is_not_reported(self):
        out, items = migrate("/-- factors as `Pr[commit] · 1/|F|` -/\ndef d : Nat := 0")
        self.assertIn("Pr[commit]", out)
        self.assertEqual(items, [])

    def test_comments_convert_only_syntactic_events(self):
        source = "-- `Pr[= a | mx]`, `Pr[ |L| ≤ ℓ ]` and `Pr[good | run]`\n"
        self.assertMigrates(source, "-- `Pr{mx}[= a]`, `Pr[ |L| ≤ ℓ ]` and `Pr[good | run]`\n")

    def test_let_items(self):
        self.assertMigrates("Pr{let x ← mx}[p x]", "Pr{x ← mx}[p x]")
        self.assertMigrates("Pr{let x ← mx; let y ← my x}[q x y]",
                            "Pr{x ← mx; y ← my x}[q x y]")
        self.assertMigrates("(h : Pr{\n      let y ← $ᵗ α}[p y])",
                            "(h : Pr{y ←\n      $ᵗ α}[p y])")
        # Patterns and nested `do` blocks keep their `let`.
        self.assertMigrates("Pr{let (a, b) ← mx}[a = b]", "Pr{let (a, b) ← mx}[a = b]")
        self.assertMigrates("Pr{x ← do\n    let y ← mx\n    pure y}[p x]",
                            "Pr{x ← do\n    let y ← mx\n    pure y}[p x]")


class BinderTests(unittest.TestCase):
    def test_answer_binders_are_deleted(self):
        source = (
            "variable {ι : Type} {spec : OracleSpec ι}\n"
            "  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]\n"
            "  [OracleSpec.IsMeasureSpec spec]\n"
            "\n"
            "omit [∀ t, DiscreteMeasurableSpace (spec.Range t)] in\n"
            "theorem t [∀ t : spec.Domain, MeasurableSpace (spec.Range t)] (x : Nat) : x = x := rfl\n"
            "theorem u [(t : spec.Domain) → MeasurableSpace (spec.Range t)] : True := trivial\n"
            "theorem v (t : ι) [MeasurableSpace (spec.Range t)] : True := trivial\n"
        )
        expected = (
            "variable {ι : Type} {spec : OracleSpec ι}\n"
            "  [OracleSpec.IsMeasureSpec spec]\n"
            "\n"
            "theorem t (x : Nat) : x = x := rfl\n"
            "theorem u : True := trivial\n"
            "theorem v (t : ι) [MeasurableSpace (spec.Range t)] : True := trivial\n"
        )
        self.assertEqual(migrate(source)[0], expected)

    def test_variable_left_empty_is_deleted(self):
        source = ("variable\n  [∀ t, MeasurableSpace (spec.Range t)]\n\n"
                  "variable [∀ t, MeasurableSpace (spec₁.Range t)]\n"
                  "theorem t : True := trivial\n")
        self.assertEqual(migrate(source)[0], "\ntheorem t : True := trivial\n")

    def test_classes(self):
        out, items = migrate("variable [IsProbabilitySpec spec] [OracleSpec.IsUniformSpec spec']\n"
                             "instance : IsUniformSpec s := IsUniformSpec.ofFintypeInhabited s\n")
        self.assertEqual(out, "variable [OracleSpec.IsMeasureSpec spec] "
                              "[OracleSpec.IsUniformMeasureSpec spec']\n"
                              "instance : IsUniformSpec s := IsUniformMeasureSpec.ofFiniteNonempty s\n")
        self.assertTrue(any("Fintype" in msg for _, _, msg in items))


class NameTests(unittest.TestCase):
    def test_renames(self):
        out, _ = migrate("exact (OracleComp.probEvent_mono h).trans (relTriple_of_evalSPMF_eq_left e)")
        self.assertEqual(out, "exact (OracleComp.prEvent_mono h).trans (relTriple_of_evalDistEq_left e)")

    def test_rename_respects_identifier_boundaries(self):
        self.assertEqual(migrate("probEvent_mono' h")[0], "probEvent_mono' h")
        self.assertEqual(migrate("my_probEvent_mono h")[0], "my_probEvent_mono h")

    def test_prEvent_le_one_takes_the_event_alone(self):
        out, items = migrate("exact prEvent_le_one _ _\nexact prEvent_le_one mx")
        self.assertEqual(out, "exact prEvent_le_one _\nexact prEvent_le_one mx")
        self.assertEqual([line for _, line, _ in items], [2])

    def test_game_equiv(self):
        out, _ = migrate("h : GameEquiv g₁ g₂\nh' : g₁ ≡ₚ g₂\nexact GameEquiv.symm h")
        self.assertEqual(out, "h : EvalDistEq g₁ g₂\nh' : g₁ =ᵈ g₂\nexact EvalDistEq.symm h")

    def test_legacy_names_are_reported_with_hints(self):
        _, items = migrate("theorem t : True := by\n  rw [probOutput_bind_eq_tsum]\n  exact h")
        self.assertEqual(len(items), 1)
        self.assertEqual(items[0][1], 2)
        self.assertIn("prEvent_bind_eq_lintegral", items[0][2])


class ReportTests(unittest.TestCase):
    def test_answer_instances_are_reported(self):
        source = ("local instance : ∀ q,\n"
                  "    MeasurableSpace (([(pSpec l).Message]ₒ).Range q) := fun _ => ⊤\n"
                  "instance : IsUniformMeasureSpec s :=\n"
                  "  @IsUniformMeasureSpec.ofFiniteNonempty _ _ h₁ h₂ _ _\n")
        _, items = migrate(source)
        self.assertEqual(sorted(line for _, line, _ in items), [2, 4])


class ImportTests(unittest.TestCase):
    def test_moved_modules(self):
        source = ("module\n\n"
                  "public import VCVio.CryptoFoundations.ForkMeasure\n"
                  "public import VCVio.CryptoFoundations.SeededFork\n"
                  "import VCVio.OracleComp.Constructions.Fork\n"
                  "import VCVio.OracleComp.OracleComp\n")
        expected = ("module\n\n"
                    "public import VCVio.CryptoFoundations.ReplayFork\n"
                    "public import VCVio.CryptoFoundations.SeededFork\n"
                    "import VCVio.OracleComp.Constructions.Fork.Basic\n"
                    "import VCVio.OracleComp.OracleComp\n")
        self.assertEqual(migrate(source)[0], expected)

    def test_unrelated_imports_are_untouched(self):
        source = "public import A\npublic import B\npublic import A\n"
        self.assertEqual(migrate(source)[0], source)


class CommandLineTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="vcvio-migrate-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.file = self.root / "Lib" / "A.lean"
        self.file.parent.mkdir()
        self.file.write_text("theorem t : Pr[= a | mx] = 1 := sorry\n")
        (self.root / ".lake").mkdir()
        (self.root / ".lake" / "Dep.lean").write_text("Pr[= a | mx]\n")

    def run_codemod(self, *extra):
        return subprocess.run(["python3", str(SCRIPT), *extra, str(self.root)],
                              text=True, capture_output=True, timeout=60)

    def test_dry_run_prints_a_diff(self):
        result = self.run_codemod("--dry-run")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("+theorem t : Pr{mx}[= a] = 1 := sorry", result.stdout)
        self.assertIn("Pr[= a | mx]", self.file.read_text())

    def test_rewrite_is_idempotent_and_skips_lake(self):
        self.assertEqual(self.run_codemod().returncode, 0)
        once = self.file.read_text()
        self.assertEqual(once, "theorem t : Pr{mx}[= a] = 1 := sorry\n")
        self.run_codemod()
        self.assertEqual(self.file.read_text(), once)
        self.assertEqual((self.root / ".lake" / "Dep.lean").read_text(), "Pr[= a | mx]\n")


if __name__ == "__main__":
    unittest.main()
