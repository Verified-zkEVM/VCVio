/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.ProgramLogic.Prob
public import VCVio.ProgramLogic.Unary.WP.Measure
public import PolyFun.Control.Monad.Algebra.Restrict
public import ToMathlib.Control.Monad.Algebra

/-!
# Probability-bounded measure weakest preconditions

Lawful successful-output measure semantics give bounded probability assertions by restricting
the expectation algebra to `Prob`. Enable this interpretation with
`open scoped MeasureProgramLogic.Probabilistic`.
-/

public section

open MeasureTheory Std.Internal.Do
open scoped ENNReal

universe v

namespace MeasureProgramLogic.Probabilistic

variable (m : Type → Type v) [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

attribute [local instance] MeasureProgramLogic.Quantitative.instMAlgOrdered

omit [LawfulMonad m] in
/-- Subprobability expectations preserve the upper bound one. -/
theorem wp_one_le {α : Type} (mx : m α) :
    MAlgOrdered.wp mx (fun _ ↦ (1 : ENNReal)) ≤ 1 := by
  let : MeasurableSpace α := MeasurableSpace.comap (fun _ : α ↦ (1 : ENNReal)) inferInstance
  exact Quantitative.wp_le_const mx measurable_const
    (Filter.Eventually.of_forall fun _ ↦ le_rfl)


/-- The native expectation algebra restricted to bounded probability assertions. -/
@[expose, instance_reducible]
noncomputable def toMAlgOrdered : MAlgOrdered m Prob :=
  MAlgOrdered.restrictIic 1 (fun {_} mx ↦ wp_one_le m mx)

/-- Select probability-bounded measure expectations. -/
noncomputable scoped instance (priority := 1100) instMAlgOrdered : MAlgOrdered m Prob :=
  toMAlgOrdered m

/-- Core WP with bounded probability assertions and no exception postcondition. -/
noncomputable scoped instance (priority := 1100) instWP : WPMonad m Prob EPost.Nil :=
  MAlgOrdered.toWPMonad

variable {m} {α : Type}

/-- The bounded algebra's values are the quantitative algebra's expectations. -/
@[simp]
theorem mAlgOrdered_wp_val (mx : m α) (post : α → Prob) :
    (MAlgOrdered.wp mx post).val = MAlgOrdered.wp mx (fun a ↦ (post a).val) :=
  MAlgOrdered.wp_restrictIic_val (m := m) 1 (fun {_} mx ↦ wp_one_le m mx) mx post

/-- Forgetting the bound recovers the native quantitative expectation. -/
theorem wp_val_eq_mAlgOrdered_wp (mx : m α) (post : α → Prob) :
    (wp mx post (Lean.Order.bot : EPost.Nil)).val =
      MAlgOrdered.wp mx (fun a ↦ (post a).val) :=
  mAlgOrdered_wp_val mx post

/-- A pure computation evaluates its bounded assertion. -/
theorem wp_pure (a : α) (post : α → Prob) :
    wp (pure a : m α) post (Lean.Order.bot : EPost.Nil) = post a := by
  simpa only [MAlgOrdered.toWPMonad_wp] using
    MAlgOrdered.wp_pure (m := m) (l := Prob) a post

/-- Bounded weakest preconditions compose through bind. -/
theorem wp_bind {β : Type} (mx : m α) (f : α → m β) (post : β → Prob) :
    wp (mx >>= f) post (Lean.Order.bot : EPost.Nil) =
      wp mx (fun a ↦ wp (f a) post (Lean.Order.bot : EPost.Nil))
        (Lean.Order.bot : EPost.Nil) := by
  simpa only [MAlgOrdered.toWPMonad_wp] using
    MAlgOrdered.wp_bind (m := m) (l := Prob) mx f post

/-- Pointwise bounded assertion comparisons are understood by generalized congruence. -/
@[gcongr low]
theorem wp_mono (mx : m α) {f g : α → Prob} (hfg : ∀ a, f a ≤ g a) :
    wp mx f (Lean.Order.bot : EPost.Nil) ≤ wp mx g (Lean.Order.bot : EPost.Nil) := by
  simpa only [MAlgOrdered.toWPMonad_wp] using
    MAlgOrdered.wp_mono (m := m) (l := Prob) mx hfg

variable [MeasurableSpace α]

/-- A bounded expectation is the integral of the assertion's underlying value. -/
theorem wp_val_eq_lintegral (mx : m α) (post : α → Prob)
    (hpost : Measurable fun a ↦ (post a).val) :
    (wp mx post (Lean.Order.bot : EPost.Nil)).val = ∫⁻ a, (post a).val ∂𝒟[mx] := by
  rw [wp_val_eq_mAlgOrdered_wp, Quantitative.wp_eq_lintegral mx _ hpost]

/-- Constant assertions retain the successful-output mass. -/
theorem wp_const (mx : m α) (p : Prob) :
    (wp mx (fun _ ↦ p) (Lean.Order.bot : EPost.Nil)).val = p.val * 𝒟[mx] Set.univ := by
  rw [wp_val_eq_lintegral mx _ measurable_const, lintegral_const]

end MeasureProgramLogic.Probabilistic
