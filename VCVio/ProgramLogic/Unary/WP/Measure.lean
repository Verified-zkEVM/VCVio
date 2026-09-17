/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public import PolyFun.Control.Monad.Algebra.WP

/-!
# Weakest preconditions from successful-output measures

The ordered expectation algebra integrates the identity against a computation's
successful-output measure. Its construction only needs lawful measure semantics;
neither uniform sampling nor losslessness is required.

Enable the quantitative interpretation with `open scoped MeasureProgramLogic.Quantitative`.
The integral characterization uses a discrete space on the intermediate output, so every
postcondition is admissible. Continuous effects require their own measurable program interface
rather than a blanket lawful interpretation of arbitrary bind continuations.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v

namespace MeasureProgramLogic

variable (m : Type → Type v) [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- The ordered algebra of nonnegative expectations under successful-output measures. -/
@[expose, instance_reducible]
noncomputable def toMAlgOrdered : MAlgOrdered m ENNReal where
  μ mx := ∫⁻ x, x ∂𝒟[mx]
  μ_pure x := by simp
  μ_bind_mono {α} f g hfg mx := by
    let : MeasurableSpace α := ⊤
    rw [lintegral_evalDist_bind_of_discrete mx f (g := fun x ↦ x) measurable_id,
      lintegral_evalDist_bind_of_discrete mx g (g := fun x ↦ x) measurable_id]
    exact lintegral_mono hfg

namespace Quantitative

/-- Select the native ordered expectation algebra. -/
noncomputable scoped instance instMAlgOrdered : MAlgOrdered m ENNReal :=
  toMAlgOrdered m

/-- Core WP with nonnegative expectations and an empty exception postcondition.

Opening this scope selects the quantitative carrier before core instances
whose carrier is `Prop`. -/
noncomputable scoped instance (priority := 1100) instWP [LawfulMonad m] :
    Std.Internal.Do.WPMonad m ENNReal Std.Internal.Do.EPost.Nil :=
  MAlgOrdered.toWPMonad

variable {m} {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]

/-- An ordered expectation WP is the integral of its postcondition. -/
theorem wp_eq_lintegral (mx : m α) (post : α → ENNReal) :
    MAlgOrdered.wp mx post = ∫⁻ x, post x ∂𝒟[mx] := by
  change (∫⁻ y, y ∂𝒟[mx >>= fun x ↦ pure (post x)]) = _
  rw [lintegral_evalDist_bind_of_discrete mx _ (g := fun x ↦ x) measurable_id]
  simp

/-- Constant postconditions retain the successful-output mass. -/
@[simp]
theorem wp_const (mx : m α) (c : ENNReal) :
    MAlgOrdered.wp mx (fun _ ↦ c) = c * 𝒟[mx] Set.univ := by
  rw [wp_eq_lintegral, lintegral_const]

/-- Expectation is additive in discrete postconditions. -/
@[simp]
theorem wp_add (mx : m α) (f g : α → ENNReal) :
    MAlgOrdered.wp mx (fun x ↦ f x + g x) = MAlgOrdered.wp mx f + MAlgOrdered.wp mx g := by
  simp only [wp_eq_lintegral, lintegral_add_left (Measurable.of_discrete : Measurable f)]

/-- Scaling a discrete postcondition scales its expectation. -/
@[simp]
theorem wp_const_mul (mx : m α) (c : ENNReal) (f : α → ENNReal) :
    MAlgOrdered.wp mx (fun x ↦ c * f x) = c * MAlgOrdered.wp mx f := by
  simp only [wp_eq_lintegral, lintegral_const_mul c (Measurable.of_discrete : Measurable f)]

/-- Finite sums of postconditions commute with their expectation. -/
theorem wp_finsetSum {κ : Type*} (mx : m α) (s : Finset κ) (f : κ → α → ENNReal) :
    MAlgOrdered.wp mx (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, MAlgOrdered.wp mx (f i) := by
  simp only [wp_eq_lintegral, lintegral_finsetSum s (fun _ _ ↦ Measurable.of_discrete)]

/-- Pointwise comparison of postconditions is understood by generalized congruence. -/
@[gcongr low]
theorem wp_mono (mx : m α) {f g : α → ENNReal} (hfg : ∀ x, f x ≤ g x) :
    MAlgOrdered.wp mx f ≤ MAlgOrdered.wp mx g := by
  rw [wp_eq_lintegral, wp_eq_lintegral]
  exact lintegral_mono hfg

/-- Almost-everywhere comparison is sufficient for quantitative correctness. -/
theorem wp_mono_ae (mx : m α) {f g : α → ENNReal} (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ g x) :
    MAlgOrdered.wp mx f ≤ MAlgOrdered.wp mx g := by
  rw [wp_eq_lintegral, wp_eq_lintegral]
  exact lintegral_mono_ae hfg

/-- Monotone convergence for quantitative weakest preconditions. -/
theorem wp_iSup (mx : m α) (f : ℕ → α → ENNReal) (hf : Monotone f) :
    MAlgOrdered.wp mx (fun x ↦ ⨆ n, f n x) = ⨆ n, MAlgOrdered.wp mx (f n) := by
  simp only [wp_eq_lintegral]
  exact lintegral_iSup (fun _ ↦ Measurable.of_discrete) hf

/-- Bounding a postcondition almost everywhere bounds its expectation with the success mass. -/
theorem wp_le_mul_mass (mx : m α) {post : α → ENNReal} {c : ENNReal}
    (hpost : ∀ᵐ x ∂𝒟[mx], post x ≤ c) :
    MAlgOrdered.wp mx post ≤ c * 𝒟[mx] Set.univ := by
  rw [wp_eq_lintegral]
  exact (lintegral_mono_ae hpost).trans_eq (lintegral_const c)

/-- A subprobability expectation of an almost everywhere bounded postcondition is bounded. -/
theorem wp_le_const (mx : m α) {post : α → ENNReal} {c : ENNReal}
    (hpost : ∀ᵐ x ∂𝒟[mx], post x ≤ c) : MAlgOrdered.wp mx post ≤ c :=
  (wp_le_mul_mass mx hpost).trans <| by
    exact (mul_le_mul' le_rfl (evalDist_apply_univ_le_one mx)).trans_eq (mul_one c)

/-- An additive comparison retains the missing-mass factor for a lossy computation. -/
theorem wp_le_const_mul_mass_add (mx : m α) {f g : α → ENNReal} {c : ENNReal}
    (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ c + g x) :
    MAlgOrdered.wp mx f ≤ c * 𝒟[mx] Set.univ + MAlgOrdered.wp mx g := by
  rw [wp_eq_lintegral, wp_eq_lintegral]
  exact (lintegral_mono_ae hfg).trans_eq <| by
    rw [lintegral_add_left measurable_const, lintegral_const]

end Quantitative
end MeasureProgramLogic
