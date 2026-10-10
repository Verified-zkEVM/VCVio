/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioTest.Tactic.GeneralizedRelations
public import VCVio.ProgramLogic.Tactics
public import VCVio.ProgramLogic.Relational.Measure
public import Mathlib.Tactic.Monotonicity
public import Mathlib.Tactic.ApplyCongr
public import Mathlib.Tactic.CongrM

/-!
# Experiments with generalized relations

Local registrations separate feasible extensions from the production tactic contract. These
examples cover support-aware equality in distribution, postconditions, support-restricted
equality, and alternative congruence tactics. Local instances and attributes do not escape their
sections.
-/

public section

open OracleComp OracleComp.ProgramLogic OracleSpec MeasureTheory
open scoped ENNReal

namespace VCVioTest.GeneralizedRelationsExperiments

/-! ## Support-aware congruence for equality in distribution is local

`EvalDistEq.bind_congr` is the registered congruence. Registering the support-aware form in its
place keeps the reachable output in context for the continuation goal. -/

section Games

/-- A coin whose negation is taken only on the reachable outputs of the draw. -/
def negatedCoin : ProbComp Bool := do
  let b ← $ᵗ Bool
  pure !b

attribute [local gcongr] OracleComp.EvalDistEq.bind_congr_of_support

example {f g : Bool → ProbComp Bool} (h : ∀ b ∈ support ($ᵗ Bool : ProbComp Bool), f b =ᵈ g b) :
    ($ᵗ Bool : ProbComp Bool) >>= f =ᵈ ($ᵗ Bool : ProbComp Bool) >>= g := by
  gcongr with b hb
  guard_hyp hb : b ∈ support ($ᵗ Bool : ProbComp Bool)
  exact h b hb

example : negatedCoin =ᵈ ($ᵗ Bool : ProbComp Bool) := by
  unfold negatedCoin
  simpa only [bind_pure_comp] using
    SampleableType.map_uniformSample_evalDistEq_of_bijective
      (Function.Involutive.bijective (f := not) Bool.not_not)

end Games

/-! ## Congruence registries for equality are separate -/

section Equality

variable {α : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞)

example (h : ∀ x ∈ support mx, f x = g x) : wp mx f = wp mx g := by
  -- gap(gcongr, 2026-09-08): support-aware equality congruence is not registered globally.
  fail_if_success gcongr
  exact wp_congr_of_support mx h

attribute [local gcongr] wp_congr_of_support

attribute [local congr] wp_congr_of_support

example (h : ∀ x ∈ support mx, f x = g x) : wp mx f = wp mx g := by
  gcongr with x hx
  guard_hyp hx : x ∈ support mx
  guard_target = f x = g x
  exact h x hx

example (h : ∀ x ∈ support mx, f x = g x) : wp mx f = wp mx g := by
  -- gap(grw, 2026-09-08): equality rules use ordinary rewriting without support context.
  fail_if_success grw [h]
  exact wp_congr_of_support mx h

example (h : ∀ x, f x = g x) : wp mx f = wp mx g := by
  congrm wp mx ?_
  guard_target = f = g
  exact funext h

example (h : ∀ x, f x = g x) : wp mx f = wp mx g := by
  congr! 1
  guard_target = f _ = g _
  exact h _

example (h : ∀ x ∈ support mx, f x = g x) : wp mx f = wp mx g := by
  conv_lhs =>
    apply_congr (wp_congr_of_support (oa := mx) (f := f) (g := g))
    tactic => exact h _ (by assumption)

end Equality

/-! ## Qualitative consequence has an abbreviation boundary -/

section Relational

open OracleComp.ProgramLogic.Relational

attribute [local gcongr] relTriple_post_mono

example {α β : Type} (oa : ProbComp α) (ob : ProbComp β) (R S : α → β → Prop)
    (h : ∀ a b, R a b → S a b) : RelTriple oa ob R → RelTriple oa ob S := by
  -- gap(gcongr, 2026-09-08): the reducible triple's lookup head differs from its registration.
  fail_if_success gcongr
  intro hR
  rel_conseq with R
  · exact hR
  · exact fun {a b} => h a b

end Relational

/-! ## Measure postconditions and almost-everywhere bounds -/

section MeasurePosts

/--
error: `f` appears on the LHS and `g` on the RHS, but there is no corresponding hypothesis `f ~ g` or `g ~ f`.

This means that the `@[gcongr]` lemma cannot be used in the `grw` tactic. Please use `@[gcongr only]` instead.
-/
#guard_msgs in
attribute [local gcongr] Measure.bind_mono_right

attribute [local gcongr] MeasureProgramLogic.eRelWP_mono MeasureProgramLogic.CouplingPost.mono

example {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {m : Type → Type} [EvalDistSemantics m]
    (mx : m α) (my : m β) (g h : α → β → ℝ≥0∞)
    (hgh : ∀ a b, g a b ≤ h a b) :
    MeasureProgramLogic.eRelWP mx my g ≤ MeasureProgramLogic.eRelWP mx my h := by grw [hgh]

example {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (R S : α → β → Prop)
    (h : ∀ a b, R a b → S a b) :
    MeasureProgramLogic.CouplingPost μ ν R → MeasureProgramLogic.CouplingPost μ ν S := by
  gcongr with a b
  guard_target = R a b → S a b
  exact h a b

attribute [local gcongr only] Measure.bind_mono_right

example {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f g : α → Measure β)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : ∀ᵐ x ∂μ, f x ≤ g x) :
    μ.bind f ≤ μ.bind g := by gcongr

end MeasurePosts

/-! ## Monotonicity search and lower cost bounds -/

section Costs

attribute [local mono] AddWriterT.queryBoundedAboveBy_mono
attribute [local gcongr] AddWriterT.pathwiseCostAtLeast_mono AddWriterT.queryBoundedBelowBy_mono

variable {α : Type} (oa : AddWriterT ℕ ProbComp α) {a b : ℕ}

example (h : a ≤ b) (ha : AddWriterT.QueryBoundedAboveBy oa a) :
    AddWriterT.QueryBoundedAboveBy oa b := by mono

example (h : a ≤ b) (hb : AddWriterT.PathwiseCostAtLeast oa b) :
    AddWriterT.PathwiseCostAtLeast oa a := by
  grw [h]
  guard_target = AddWriterT.PathwiseCostAtLeast oa b
  exact hb

example (h : a ≤ b) (hb : AddWriterT.QueryBoundedBelowBy oa b) :
    AddWriterT.QueryBoundedBelowBy oa a := by
  grw [h]
  guard_target = AddWriterT.QueryBoundedBelowBy oa b
  exact hb

end Costs

end VCVioTest.GeneralizedRelationsExperiments
