/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Defs.Measure.FinRatPMF
public import VCVioTest.MeasureSemantics
public import VCVio.EvalDist.Inequalities
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.EvalDist.PFunctorPath
public import VCVio.EvalDist.Defs.Measure.ExceptT
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Computation probability notation canaries

These examples exercise the same `Pr{...}[...]` syntax with a finite computation,
an optional computation, and a continuous oracle interpreted only by measures.
-/

public section

open MeasureTheory ProbabilityTheory OracleComp PFunctor ProbComp
open scoped ENNReal

namespace VCVioTest.ProbabilityNotation

/-- A closed draw whose implementation is opaque to consumers. -/
opaque opaqueDraw : ProbComp ℝ := pure 0

example : IsProbabilityMeasure 𝒟[opaqueDraw] := inferInstance

example : IsSubprobabilityMeasure 𝒟[opaqueDraw] := inferInstance

example (mx : ProbComp ℝ) : IsProbabilityMeasure 𝒟[OptionT.lift mx] := inferInstance

example (mx : ProbComp ℝ) : IsProbabilityMeasure 𝒟[(liftM mx : OptionT ProbComp ℝ)] :=
  inferInstance

example (mx : ProbComp ℝ) : IsProbabilityMeasure 𝒟[(liftM mx : ExceptT Bool ProbComp ℝ)] :=
  inferInstance

example {α : Type} [MeasurableSpace α] (mx : OptionT ProbComp α) :
    𝒟[mx] = (𝒟[mx.run]).comap some := OptionT.evalDist_eq_comap_some mx

example {α : Type} [MeasurableSpace α] (mx : ExceptT Bool ProbComp α) :
    𝒟[mx] = (𝒟[mx.run]).comap Except.ok := ExceptT.evalDist_eq_comap_ok mx

example {α : Type} [SampleableType α] [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    Pr{let x ← $ᵗ α}[p x] = (Finset.univ.filter p).card / (Fintype.card α : ENNReal) := by
  simp

example {α : Type} [SampleableType α] [Fintype α]
    (p : α → Prop) [DecidablePred p] {bound : ENNReal}
    (h : (Finset.univ.filter p).card / (Fintype.card α : ENNReal) ≤ bound) :
    Pr{let x ← $ᵗ α}[p x] ≤ bound := by grind

example (mx : ProbComp ℝ) : IsProbabilityMeasure 𝒟[mx] := inferInstance

example (mx : OracleComp coinSpec ℝ) : IsProbabilityMeasure 𝒟[mx] := inferInstance

example {α : Type} [MeasurableSpace α] (mx : OptionT ProbComp α) :
    IsSubprobabilityMeasure 𝒟[mx] := inferInstance

example (μ : Measure ℝ) [IsSubprobabilityMeasure μ] (f : ℝ → ℝ) :
    IsSubprobabilityMeasure (μ.map f) := inferInstance

example (μ : Measure ℝ) [IsSubprobabilityMeasure μ] (f : ℝ → Measure ℝ)
    [∀ x, IsSubprobabilityMeasure (f x)] : IsSubprobabilityMeasure (μ.bind f) := inferInstance

example (mx : ProbComp ℝ) : IsProbabilityMeasure (FreeM.denote mx) := inferInstance

example (mx : ProbComp ℝ) [MeasurableSpace (FreeM.Path mx)] :
    IsProbabilityMeasure (FreeM.pathMeasure mx) := inferInstance

example (mx : ProbComp ℝ) : IsProbabilityMeasure (FreeM.queryCountMeasure mx) := inferInstance

example (mx : ProbComp ℝ) : ∫⁻ _, (1 : ENNReal) ∂𝒟[mx] = 1 := by simp

example {α : Type} (mx : ProbComp α) (b : Bool) :
    𝒟[(fun _ ↦ b) <$> mx] {b} = 1 := by simp

example {α : Type} (mx : ProbComp α) (f : α → ℕ) (c : ℕ) :
    (∫⁻ n, (n : ENNReal) ∂𝒟[(fun x ↦ f x + c) <$> mx]) =
      (∫⁻ n, (n : ENNReal) ∂𝒟[f <$> mx]) + c := by simp

example {α : Type} (mx : ProbComp α) (f : α → ℕ) (c : ℕ) :
    (∫⁻ n, (n : ENNReal) ∂𝒟[Nat.add c <$> (f <$> mx)]) =
      (∫⁻ n, (n : ENNReal) ∂𝒟[f <$> mx]) + c := by grind [measure_univ, mul_one]

example {α : Type} (mx : ProbComp α) (f : α → ℕ) (c : ℕ) {bound : ENNReal}
    (h : (∫⁻ n, (n : ENNReal) ∂𝒟[f <$> mx]) ≤ bound) :
    (∫⁻ n, (n : ENNReal) ∂𝒟[(fun x ↦ f x + c) <$> mx]) ≤ bound + c := by
  grw [lintegral_evalDist_map_add_nat, measure_univ, mul_one, h]

example : (∫⁻ _ : Fin 0, (⊤ : ENNReal) ∂uniformOn Set.univ) = 0 := by
  simp

example : (∫⁻ _, (⊤ : ENNReal) ∂𝒟[uniformFin 0]) = ⊤ := by
  simp only [lintegral_const, measure_univ, mul_one]

example (mx : ProbComp Bool) :
    Pr{let b ← mx}[b] = 𝒟[mx] {true} := by
  rw [prEvent_eq_evalDist_of_discrete]
  simp

example (mx : OptionT ProbComp Bool) :
    Pr{let b ← mx}[b] = 𝒟[mx] {true} := by
  rw [prEvent_eq_evalDist_of_discrete]
  simp

example (mx : FinRatPMF.Raw Bool) :
    Pr{let b ← mx}[b] = ((mx.prob true : NNReal) : ENNReal) := by
  rw [prEvent_eq_evalDist_of_discrete]
  simp

example : FinRatPMF.Raw.coin.prob true = 1 / 2 := by
  simpa only [one_div] using FinRatPMF.Raw.prob_coin true

example (mx : ProbComp (Fin 3)) :
    Pr{let n ← mx; let value := n.val}[value = 1] =
      𝒟[mx] {n | n.val = 1} := by
  simpa only using prEvent_eq_evalDist_of_discrete mx (fun n => n.val = 1)

open VCVioTest.MeasureSemantics in
example : IsProbabilityMeasure 𝒟[(FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)] :=
  FreeM.isProbabilityMeasure_evalDist_lift (P := gaussSpec) _

open VCVioTest.MeasureSemantics in
example : IsProbabilityMeasure 𝒟[(pure (1 : ℝ) : FreeM gaussSpec ℝ)] := inferInstance

open VCVioTest.MeasureSemantics in
example : 𝒟[(failure : OptionT (FreeM gaussSpec) ℝ)] = 0 := by simp

open VCVioTest.MeasureSemantics in
example : ¬ IsProbabilityMeasure 𝒟[(failure : OptionT (FreeM gaussSpec) Bool)] := by
  simp [isProbabilityMeasure_iff]

open VCVioTest.MeasureSemantics in
example :
    Pr{let x ← (FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)}[x > 0] =
      gaussianReal 0 1 {x | x > 0} := by
  rw [FreeM.evalDist_lift_bind_pure (P := gaussSpec) _ _ (by fun_prop),
    FreeM.evalDist_eq_denote (P := gaussSpec), denote_gauss_lift,
    Measure.map_apply (by fun_prop) (measurableSet_singleton True)]
  simp

open VCVioTest.MeasureSemantics in
example (acc B : ℝ → ENNReal) (q hinv : ENNReal) (hacc : Measurable acc)
    (hle : ∀ x, acc x ≤ 1) (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    let mx := (FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)
    (∫⁻ x, acc x ∂𝒟[mx]) * ((∫⁻ x, acc x ∂𝒟[mx]) / q - hinv) ≤ ∫⁻ x, B x ∂𝒟[mx] :=
  OracleComp.EvalDist.marginalized_jensen_forking_bound _ acc B q hinv hacc.aemeasurable
    (Filter.Eventually.of_forall hle) (Filter.Eventually.of_forall hper)

open VCVioTest.MeasureSemantics in
example :
    𝒟[(pure (1 : ℝ) : OptionT (FreeM gaussSpec) ℝ)] {1} = 1 := by
  simp

open VCVioTest.MeasureSemantics in
example :
    Pr{let x ← (pure (1 : ℝ) : OptionT (FreeM gaussSpec) ℝ)}[x = 1] = 1 := by
  simp

end VCVioTest.ProbabilityNotation
