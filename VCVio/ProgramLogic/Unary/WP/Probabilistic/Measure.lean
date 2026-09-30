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

/-- Subprobability expectations preserve the upper bound one. -/
theorem μ_one_le {α : Type} (mx : m α) :
    MAlgOrdered.μ (mx >>= fun _ ↦ pure (1 : ENNReal)) ≤ 1 := by
  let : MeasurableSpace α := MeasurableSpace.comap (fun _ : α ↦ (1 : ENNReal)) inferInstance
  exact Quantitative.wp_le_const mx measurable_const
    (Filter.Eventually.of_forall fun _ ↦ le_rfl)

/-- The expectation algebra restricted to bounded probability assertions. -/
@[expose, instance_reducible]
noncomputable def toMAlgOrdered : MAlgOrdered m Prob :=
  MAlgOrdered.restrictIic 1 (fun {_} mx ↦ μ_one_le m mx)

/-- Select probability-bounded measure expectations. -/
noncomputable scoped instance (priority := 1100) instMAlgOrdered : MAlgOrdered m Prob :=
  toMAlgOrdered m

/-- Core WP with bounded probability assertions and no exception postcondition. -/
noncomputable scoped instance (priority := 1100) instWP : WPMonad m Prob EPost.Nil :=
  MAlgOrdered.toWPMonad

variable {m} {α : Type}

/-- The bounded interpretation's values are the quantitative algebra's expectations. -/
@[simp]
theorem wp_val (mx : m α) (post : α → Prob) :
    (wp mx post (Lean.Order.bot : EPost.Nil)).val =
      MAlgOrdered.μ (mx >>= fun a ↦ pure (post a).val) := by
  change (MAlgOrdered.μ (Subtype.val <$> (mx >>= fun a ↦ pure (post a))) : ENNReal) = _
  simp only [map_bind, map_pure]
  rfl

/-- Pointwise bounded assertion comparisons are understood by generalized congruence. -/
@[gcongr low]
theorem wp_mono (mx : m α) {f g : α → Prob} (hfg : ∀ a, f a ≤ g a) :
    wp mx f (Lean.Order.bot : EPost.Nil) ≤ wp mx g (Lean.Order.bot : EPost.Nil) :=
  MAlgOrdered.μ_bind_pure_mono (l := Prob) mx hfg

/-- A bounded expectation integrates the assertion's underlying value. -/
theorem wp_val_eq_lintegral_map (mx : m α) (post : α → Prob) :
    (wp mx post (Lean.Order.bot : EPost.Nil)).val = ∫⁻ y, y ∂𝒟[(fun a ↦ (post a).val) <$> mx] := by
  rw [wp_val, bind_pure_comp]
  exact Quantitative.μ_eq_lintegral _

variable [MeasurableSpace α]

/-- A bounded expectation is the integral of the assertion's underlying value. -/
theorem wp_val_eq_lintegral (mx : m α) (post : α → Prob)
    (hpost : Measurable fun a ↦ (post a).val) :
    (wp mx post (Lean.Order.bot : EPost.Nil)).val = ∫⁻ a, (post a).val ∂𝒟[mx] := by
  rw [wp_val]
  exact Quantitative.wp_eq_lintegral mx _ hpost

/-- Constant assertions retain the successful-output mass. -/
theorem wp_const (mx : m α) (p : Prob) :
    (wp mx (fun _ ↦ p) (Lean.Order.bot : EPost.Nil)).val = p.val * 𝒟[mx] Set.univ := by
  rw [wp_val_eq_lintegral mx _ measurable_const, lintegral_const]

end MeasureProgramLogic.Probabilistic
