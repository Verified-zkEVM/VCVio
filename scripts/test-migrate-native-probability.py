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
        self.assertMigrates("Pr[= a | mx]", "Pr{let x ← mx}[x = a]")
        self.assertMigrates("Pr[(· = f x) | g <$> mx]", "Pr{let y ← g <$> mx}[y = f x]")
        # Singleton events of earlier versions of the measure API.
        self.assertMigrates("Pr{mx}[= a] = Pr{g <$> my}[(· = (f b, c))]",
                            "Pr{let x ← mx}[x = a] = Pr{let x ← g <$> my}[x = (f b, c)]")

    def test_reading_scopes_and_answer_measures(self):
        self.assertMigrates(
            "open scoped OracleComp.Qualitative in\n"
            "example [OracleSpec.IsMeasureSpec spec] [IsUniformMeasureSpec spec'] : True := by\n"
            "  exp_norm",
            "open scoped OracleComp.Necessary in\n"
            "example [OracleSpec.AnswerMeasure spec] [UniformAnswerMeasure spec'] : True := by\n"
            "  expect_arith")
        self.assertMigrates("simp only [game_rule]", "simp only [expect_norm, expect_eval]")

    def test_function_events(self):
        self.assertMigrates("Pr[fun x => x.1 = a | mx]", "Pr{let x ← mx}[x.1 = a]")
        self.assertMigrates("Pr[fun x ↦ p x | mx]", "Pr{let x ← mx}[p x]")
        self.assertMigrates("Pr[(fun z : ℕ => z > 3) | mx]", "Pr{let z : ℕ ← mx}[z > 3]")
        self.assertMigrates("Pr[fun (z : α × β) => p z.1 | mx]", "Pr{let z : α × β ← mx}[p z.1]")
        self.assertMigrates("Pr[fun ⟨a, b⟩ => a = b | mx]", "Pr{let ⟨a, b⟩ ← mx}[a = b]")
        self.assertMigrates("Pr[fun (⟨a, b⟩ : α × β) => a = b | mx]",
                            "Pr{let ⟨a, b⟩ : α × β ← mx}[a = b]")
        # A typed binder keeps its type: `x - 2 = 0` at `ℤ` is not the same event at `ℕ`.
        self.assertMigrates("Pr[fun (x : ℤ) => x - 2 = 0 | mx]", "Pr{let x : ℤ ← mx}[x - 2 = 0]")
        self.assertMigrates("Pr[fun x : ℤ => x - 2 = 0 | mx]", "Pr{let x : ℤ ← mx}[x - 2 = 0]")

    def test_deeply_typed_binder_is_kept_as_an_applied_predicate(self):
        # A type the binder regexes do not reach stays inside the predicate, type and all.
        self.assertMigrates("Pr[fun (x : ((ℕ × ℕ) × ℕ) → ℕ) => p x | mx]",
                            "Pr{let y ← mx}[(fun (x : ((ℕ × ℕ) × ℕ) → ℕ) => p x) y]")

    def test_sections_and_predicates(self):
        self.assertMigrates("Pr[(· ∈ S) | mx]", "Pr{let x ← mx}[x ∈ S]")
        self.assertMigrates("Pr[p | mx]", "Pr{let x ← mx}[p x]")
        self.assertMigrates("Pr[S.contains | mx]", "Pr{let x ← mx}[S.contains x]")
        self.assertMigrates("Pr[q ∘ f | mx]", "Pr{let x ← mx}[(q ∘ f) x]")
        # The bound name avoids the names the event and computation use.
        self.assertMigrates("Pr[p x | f x]", "Pr{let y ← f x}[(p x) y]")

    def test_failure_event(self):
        self.assertMigrates("Pr[⊥ | mx] = 0", "prFail mx = 0")
        self.assertMigrates("Pr[⊥ | f <$> mx] = 0", "prFail (f <$> mx) = 0")

    def test_multiline_computation(self):
        source = "Pr[= true | do\n    let y ← mx\n    pure y]"
        self.assertMigrates(source, "Pr{let x ← (do\n    let y ← mx\n    pure y)}[x = true]")

    def test_nested_events(self):
        self.assertMigrates("Pr[= a | mx] ≤ Pr[p | my] + ε",
                            "Pr{let x ← mx}[x = a] ≤ Pr{let x ← my}[p x] + ε")

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
        self.assertMigrates(source,
                            "-- `Pr{let x ← mx}[x = a]`, `Pr[ |L| ≤ ℓ ]` and `Pr[good | run]`\n")

    def test_draw_items(self):
        self.assertMigrates("Pr{x ← mx}[p x]", "Pr{let x ← mx}[p x]")
        self.assertMigrates("Pr{x ← mx; y ← my x}[q x y]",
                            "Pr{let x ← mx; let y ← my x}[q x y]")
        self.assertMigrates("Pr{x : α ← mx}[p x]", "Pr{let x : α ← mx}[p x]")
        self.assertMigrates("Pr{_ ← mx}[True]", "Pr{let _ ← mx}[True]")
        # A multi-line right-hand side is parenthesized.
        self.assertMigrates("(h : Pr{y ←\n      $ᵗ α}[p y])", "(h : Pr{let y ← ($ᵗ α)}[p y])")
        self.assertMigrates("Pr{y ←\n      f a\n        b}[p y]",
                            "Pr{let y ← (f a\n        b)}[p y]")
        self.assertMigrates("Pr{x ← f a\n    b}[p x]", "Pr{let x ← (f a\n    b)}[p x]")
        self.assertMigrates("Pr{x ← (f a\n    b)}[p x]", "Pr{let x ← (f a\n    b)}[p x]")
        self.assertMigrates("Pr{x ← do\n    let y ← mx\n    pure y}[p x]",
                            "Pr{let x ← (do\n    let y ← mx\n    pure y)}[p x]")
        # `do` statements, patterns and singleton events are left alone.
        self.assertMigrates("Pr{let x ← mx; let y := f x}[p y]",
                            "Pr{let x ← mx; let y := f x}[p y]")
        self.assertMigrates("Pr{let (a, b) ← mx}[a = b]", "Pr{let (a, b) ← mx}[a = b]")
        self.assertMigrates("prFail mx", "prFail mx")

    def test_sequence_after_multiline_draw_is_reported(self):
        text, items = migrate("Pr{x ← f a\n    b; y ← g x}[p y]")
        self.assertEqual(text, "Pr{let x ← (f a\n    b); let y ← g x}[p y]")
        self.assertEqual([("do` block" in msg) for _, _, msg in items], [True])


class BinderTests(unittest.TestCase):
    def test_answer_binders_are_deleted(self):
        source = (
            "variable {ι : Type} {spec : OracleSpec ι}\n"
            "  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]\n"
            "  [OracleSpec.AnswerMeasure spec]\n"
            "\n"
            "omit [∀ t, DiscreteMeasurableSpace (spec.Range t)] in\n"
            "theorem t [∀ t : spec.Domain, MeasurableSpace (spec.Range t)] (x : Nat) : x = x := rfl\n"
            "theorem u [(t : spec.Domain) → MeasurableSpace (spec.Range t)] : True := trivial\n"
            "theorem v (t : ι) [MeasurableSpace (spec.Range t)] : True := trivial\n"
        )
        expected = (
            "variable {ι : Type} {spec : OracleSpec ι}\n"
            "  [OracleSpec.AnswerMeasure spec]\n"
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
        self.assertEqual(out, "variable [OracleSpec.AnswerMeasure spec] "
                              "[OracleSpec.UniformAnswerMeasure spec']\n"
                              "instance : IsUniformSpec s := UniformAnswerMeasure.ofFiniteNonempty s\n")
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

    def test_failure_probability(self):
        self.assertEqual(migrate("probFailure mx ≤ 1 := probFailure_le_one mx")[0],
                         "prFail mx ≤ 1 := prFail_le_one mx")

    def test_quoted_names_are_kept(self):
        # A quoted Lean name denotes the name itself; a code span in prose is a mention.
        self.assertEqual(migrate("#[`SPMF, `probFailure]\n-- see `probFailure`\n")[0],
                         "#[`SPMF, `probFailure]\n-- see `prFail`\n")

    def test_game_equiv(self):
        out, _ = migrate("h : GameEquiv g₁ g₂\nh' : g₁ ≡ₚ g₂\nexact GameEquiv.symm h")
        self.assertEqual(out, "h : EvalDistEq g₁ g₂\nh' : g₁ =ᵈ g₂\nexact EvalDistEq.symm h")

    def test_reading_scopes_relative_to_open_oracle_comp(self):
        # A downstream rule that follows the scope idiom (`ProtocolSpec.Qualitative.Spec.…`) is
        # renamed with the scope.
        out, _ = migrate("prvcgen [Qualitative.Spec.ofSupport init, OracleComp.Qualitative.Spec.ofSupport oa]\n"
                         "rw [Qualitative.prEvent_eq_one_iff_triple]; exact ProtocolSpec.Qualitative.Spec.getChallenge")
        self.assertEqual(out,
            "prvcgen [Necessary.Spec.ofSupport init, OracleComp.Necessary.Spec.ofSupport oa]\n"
            "rw [Necessary.prEvent_eq_one_iff_triple]; exact ProtocolSpec.Necessary.Spec.getChallenge")

    def test_expectation_interpretation_namespace(self):
        out, _ = migrate("simp only [MeasureProgramLogic.wp_pure, MeasureProgramLogic.measureWP m,\n"
                         "  MeasureProgramLogic.toMAlgOrdered, MeasureProgramLogic.Quantitative.Spec.pure]")
        self.assertEqual(out, "simp only [ExpectationWP.wp_pure, ExpectationWP.wpMonad m,\n"
                              "  ExpectationWP.algebra, ExpectationWP.Lower.Spec.pure]")

    def test_total_variation(self):
        # The real-valued algebra keeps its names; the bounds are stated on `etvDist`.
        out, items = migrate(
            "exact (tvDist_simulateQ_le_probEvent_bad h).trans (tvDist_le_one _ _)\n"
            "exact AdvBound.of_measureETVDist hb "
            "(measureETVDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq i j)\n")
        self.assertEqual(out,
            "exact (etvDist_simulateQ_run'_le_prEvent_bad h).trans (tvDist_le_one _ _)\n"
            "exact AdvBound.of_etvDist hb (etvDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq i j)\n")
        self.assertEqual(items, [])
        _, items = migrate("exact tvDist_bind_left_le mx f g")
        self.assertEqual(len(items), 1)
        self.assertIn("etvDist_bind_left_le_tsum", items[0][2])

    def test_distribution_equations(self):
        # An equation of two output distributions is an equality in distribution.
        self.assertEqual(migrate("(h : 𝒮[oa >>= f] = 𝒮[ob])")[0], "(h : (oa >>= f) =ᵈ ob)")
        self.assertEqual(migrate("(h : ∀ a, 𝒮[f a] = 𝒮[g a]) : 𝒮[mx] = 𝒮[my] ∧ True")[0],
                         "(h : ∀ a, f a =ᵈ g a) : mx =ᵈ my ∧ True")
        # A pointwise mass, or a distribution passed as an argument, is left and reported.
        for source in ("𝒮[mx] x = 𝒮[my] x", "foo 𝒮[mx] = 𝒮[my]"):
            out, items = migrate(source)
            self.assertEqual(out, source)
            self.assertEqual(len(items), 1)

    def test_namespaced_counterparts_and_measure_semantics(self):
        self.assertEqual(migrate("exact tsum_probOutput_bind_mul mx g f")[0],
                         "exact OracleComp.tsum_prEvent_bind_mul mx g f")
        self.assertEqual(migrate("rw [probEvent_uniformSample]")[0],
                         "rw [SampleableType.prEvent_uniformSample]")
        self.assertEqual(migrate("(SPMFSemantics.withStateOracle h s).evalDist mx")[0],
                         "(MeasureSemanticsVia.withStateOracle h s).evalDist mx")
        _, items = migrate("def sem : SPMFSemantics m := s")
        self.assertIn("MeasureSemanticsVia", items[0][2])
        _, items = migrate("exact tvDist_bind_right_le f mx my")
        self.assertIn("tvDist_bind_le mx my f", items[0][2])

    def test_names_the_sources_declare_are_not_reported(self):
        source = ("theorem probOutput_mine (mx : ProbComp α) : True := trivial\n"
                  "example : True := probOutput_mine mx\n"
                  "example : True := probOutput_theirs mx\n")
        local = codemod.declared_names([source])
        self.assertIn("probOutput_mine", local)
        report = codemod.Report()
        codemod.migrate(source, "Fixture.lean", report, local)
        self.assertEqual([line for _, line, _ in report.items], [3])
        # Across files: a use in one file of a lemma another given file declares.
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "A.lean").write_text("lemma evalSPMF_mine : True := trivial\n")
            (Path(tmp) / "B.lean").write_text("example : True := evalSPMF_mine\n")
            result = subprocess.run(["python3", str(SCRIPT), "--dry-run", tmp],
                                    capture_output=True, text=True, check=True)
        self.assertIn("0 site(s) to finish by hand", result.stderr)
        # A local copy of a lemma VCVio replaces is reported once, at its declaration.
        source = ("lemma probOutput_bind_eq_tsum : True := trivial\n"
                  "example : True := probOutput_bind_eq_tsum\n")
        report = codemod.Report()
        codemod.migrate(source, "Fixture.lean", report, codemod.declared_names([source]))
        self.assertEqual([line for _, line, _ in report.items], [1])
        self.assertIn("prEvent_bind_eq_tsum", report.items[0][2])

    def test_legacy_names_are_reported_with_hints(self):
        _, items = migrate("theorem t : True := by\n  rw [probOutput_bind_eq_tsum]\n  exact h")
        self.assertEqual(len(items), 1)
        self.assertEqual(items[0][1], 2)
        self.assertIn("prEvent_bind_eq_lintegral", items[0][2])


class ReportTests(unittest.TestCase):
    def test_answer_instances_are_reported(self):
        source = ("local instance : ∀ q,\n"
                  "    MeasurableSpace (([(pSpec l).Message]ₒ).Range q) := fun _ => ⊤\n"
                  "instance : UniformAnswerMeasure s :=\n"
                  "  @UniformAnswerMeasure.ofFiniteNonempty _ _ h₁ h₂ _ _\n")
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
        # The event-keyed distances live beside their real form.
        self.assertEqual(migrate("module\n\npublic import VCVio.EvalDist.TVDist\n")[0],
                         "module\n\npublic import VCVio.EvalDist.EvalDistTV\n")

    def test_removed_namespaces_leave_open_commands(self):
        self.assertEqual(migrate("open ENNReal OracleComp.EvalDist OracleComp.ProgramLogic\n")[0],
                         "open ENNReal OracleComp.ProgramLogic\n")
        self.assertEqual(migrate("open OracleComp.EvalDist in\ntheorem t : True := trivial\n")[0],
                         "theorem t : True := trivial\n")
        self.assertEqual(migrate("open scoped OracleComp.EvalDist\n")[0], "")
        self.assertEqual(migrate("open OracleComp.EvalDistEq\n")[0],
                         "open OracleComp.EvalDistEq\n")

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
        self.assertIn("+theorem t : Pr{let x ← mx}[x = a] = 1 := sorry", result.stdout)
        self.assertIn("Pr[= a | mx]", self.file.read_text())

    def test_rewrite_is_idempotent_and_skips_lake(self):
        self.assertEqual(self.run_codemod().returncode, 0)
        once = self.file.read_text()
        self.assertEqual(once, "theorem t : Pr{let x ← mx}[x = a] = 1 := sorry\n")
        self.run_codemod()
        self.assertEqual(self.file.read_text(), once)
        self.assertEqual((self.root / ".lake" / "Dep.lean").read_text(), "Pr[= a | mx]\n")


if __name__ == "__main__":
    unittest.main()
