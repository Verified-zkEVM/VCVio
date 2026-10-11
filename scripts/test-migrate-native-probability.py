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

    def test_function_events(self):
        self.assertMigrates("Pr[fun x => x.1 = a | mx]", "Pr{let x ← mx}[x.1 = a]")
        self.assertMigrates("Pr[fun x ↦ p x | mx]", "Pr{let x ← mx}[p x]")
        self.assertMigrates("Pr[(fun z : ℕ => z > 3) | mx]", "Pr{let z ← mx}[z > 3]")
        self.assertMigrates("Pr[fun (z : α × β) => p z.1 | mx]", "Pr{let z ← mx}[p z.1]")
        self.assertMigrates("Pr[fun ⟨a, b⟩ => a = b | mx]", "Pr{let ⟨a, b⟩ ← mx}[a = b]")

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
            "  [OracleSpec.IsMeasureSpec spec]\n"
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

    def test_legacy_names_are_reported_with_hints(self):
        _, items = migrate("theorem t : True := by\n  rw [probOutput_congr rfl h]\n  exact h")
        self.assertEqual(len(items), 1)
        self.assertEqual(items[0][1], 2)
        self.assertIn("EvalDistEq.prEvent_eq", items[0][2])


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


class FirstReleaseTests(unittest.TestCase):
    """Sources written against the measure API's first release land on the final names."""

    def assertMigrates(self, source, expected):
        self.assertEqual(migrate(source)[0], expected)

    def test_answer_measures(self):
        self.assertMigrates("[OracleSpec.IsMeasureSpec spec] [IsUniformMeasureSpec spec']",
                            "[OracleSpec.AnswerMeasure spec] [UniformAnswerMeasure spec']")
        self.assertMigrates("IsMeasureSpec.toMeasure t = IsUniformMeasureSpec.add.toMeasure t",
                            "AnswerMeasure.toMeasure t = UniformAnswerMeasure.add.toMeasure t")
        self.assertMigrates("h.toIsMeasureSpec, instIsUniformMeasureSpecChalSingleton, "
                            "spec.toPFunctor.IsMeasureSpec, fairCoinMeasureSpec",
                            "h.toAnswerMeasure, instUniformAnswerMeasureChalSingleton, "
                            "spec.toPFunctor.AnswerMeasure, fairCoinAnswerMeasure")
        self.assertMigrates("spec.probHandler, simulateQ_probHandler, ProbHandler spec",
                            "spec.uniformHandler, simulateQ_uniformHandler, ProbHandler spec")

    def test_packages_and_bundled_semantics(self):
        self.assertMigrates("MeasureDistEquiv₀ h₀ h₁ ∧ QueryImpl.Stateful.MeasureDistEquiv i j",
                            "DistEquiv₀ h₀ h₁ ∧ QueryImpl.Stateful.DistEquiv i j")
        self.assertMigrates("runtime.toMeasureSemanticsVia.evalDist mx = "
                            "(MeasureSemanticsVia.ofEvalDistSemantics m).evalDist mx",
                            "runtime.toSemanticsVia.evalDist mx = "
                            "(SemanticsVia.ofEvalDistSemantics m).evalDist mx")
        out, items = migrate("exact MeasureDistEquiv.of_step h")
        self.assertEqual(out, "exact DistEquiv.of_step h")
        self.assertEqual(len(items), 1)

    def test_expectation_interpretation_and_readings(self):
        self.assertMigrates("MeasureProgramLogic.toMAlgOrdered m, MeasureProgramLogic.Quantitative.wp",
                            "ExpectationWP.algebra m, ExpectationWP.Lower.wp")
        self.assertMigrates("OracleComp.Qualitative.wp_eq_mAlgOrdered_wp, OracleComp.Quantitative.triple, "
                            "OracleComp.Rel.Qualitative.triple",
                            "OracleComp.Necessary.wp_eq_mAlgOrdered_wp, OracleComp.Lower.triple, "
                            "OracleComp.Rel.Qualitative.triple")

    def test_modules(self):
        source = ("public import VCVio.OracleComp.EvalDist.MeasureSpec\n"
                  "import VCVio.StateSeparating.DistEquiv\n"
                  "import VCVio.StateSeparating.MeasureDistEquiv\n"
                  "import VCVio.ProgramLogic.Unary.WP.Qualitative\n")
        expected = ("public import VCVio.OracleComp.EvalDist.AnswerMeasure\n"
                    "import VCVio.StateSeparating.DistEquiv\n"
                    "import VCVio.ProgramLogic.Unary.WP.Necessary\n")
        self.assertMigrates(source, expected)

    def test_distribution_equations(self):
        # An equation of two output distributions is an equality in distribution.
        self.assertMigrates("(h : 𝒮[oa >>= f] = 𝒮[ob])", "(h : (oa >>= f) =ᵈ ob)")
        self.assertMigrates("(h : ∀ a, 𝒮[f a] = 𝒮[g a]) : 𝒮[mx] = 𝒮[my] ∧ True",
                            "(h : ∀ a, f a =ᵈ g a) : mx =ᵈ my ∧ True")
        # A pointwise mass, or a distribution passed as an argument, is left and reported.
        for source in ("𝒮[mx] x = 𝒮[my] x", "foo 𝒮[mx] = 𝒮[my]"):
            out, items = migrate(source)
            self.assertEqual(out, source)
            self.assertEqual(len(items), 1)

    def test_tables_record_chains_by_their_final_name(self):
        self.assertEqual([old for old, new in codemod.RENAMES.items() if new in codemod.RENAMES],
                         [])
        self.assertEqual([old for old, targets in codemod.MODULES.items()
                          if old in targets or any(t in codemod.MODULES for t in targets)], [])


class EventLemmaTests(unittest.TestCase):
    """The discrete event lemmas land on the measure lemmas stated on the same singleton shapes."""

    def assertMigrates(self, source, expected):
        self.assertEqual(migrate(source)[0], expected)

    def test_singleton_shapes(self):
        self.assertMigrates("rw [probOutput_bind_eq_tsum, tsum_probOutput_eq_one', probOutput_ne_top]",
                            "rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.tsum_prEvent_eq_one, "
                            "prEvent_ne_top]")
        self.assertMigrates("probOutput_eq_zero_of_not_mem_support hx, probEvent_le_one, probOutput_pure",
                            "prEvent_eq_zero_of_not_mem_support hx, prEvent_le_one, prEvent_pure")
        self.assertMigrates("evalSPMF_bind, evalSPMF_map, evalSPMF_bind_congr_left oa f g h",
                            "evalDist_bind_of_discrete, evalDist_map_of_discrete, "
                            "EvalDistEq.bind_right oa f g h")
        self.assertMigrates("SPMFSemantics.withStateOracle, SPMFSemantics m, "
                            "evalSPMF_map_eq_of_evalSPMF_eq h f",
                            "SemanticsVia.withStateOracle, SemanticsVia m, EvalDistEq.map h f")

    def test_qualified_occurrences_keep_one_namespace(self):
        self.assertMigrates("OracleComp.probOutput_bind_eq_tsum oa g p",
                            "OracleComp.prEvent_bind_eq_tsum oa g p")
        self.assertMigrates("OracleComp.tsum_probOutput_bind_mul", "OracleComp.tsum_prEvent_bind_mul")

    def test_real_total_variation_is_reported(self):
        _, items = migrate("le_trans (tvDist_bind_right_le k a b) (tvDist_nonneg _ _)")
        self.assertEqual(sorted(name for _, _, name in items),
                         sorted(["`tvDist_bind_right_le`: `OracleComp.measureTVDist_bind_right_le` "
                                 "(real) or `OracleComp.measureETVDist_bind_right_le`",
                                 "`tvDist_nonneg`: `measureTVDist_nonneg` (real); `measureETVDist` "
                                 "is `ℝ≥0∞`-valued"]))

    def test_no_name_is_both_renamed_and_reported(self):
        self.assertEqual([k for k in codemod.RENAMES if k in codemod.LEGACY_HINTS], [])
        self.assertEqual([k for k in codemod.RENAMES if k in codemod.REPORT_NAMES], [])


class RepositoryTests(unittest.TestCase):
    def test_repository_is_a_fixed_point(self):
        """Every tracked Lean source of the libraries is unchanged by the codemod: a retired name
        that reappears is reported here, with no build."""
        root = SCRIPT.parent.parent
        listed = subprocess.run(["git", "ls-files", "*.lean"], cwd=root, capture_output=True,
                                text=True, encoding="utf-8").stdout.split()
        changed = []
        for name in listed:
            if name.startswith(("Interop/", "third_party/")):
                continue
            text = (root / name).read_text(encoding="utf-8")
            if codemod.migrate(text, name, codemod.Report()) != text:
                changed.append(name)
        self.assertEqual(changed, [])


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
