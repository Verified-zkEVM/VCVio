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
The integral characterization uses the chosen output space and explicit measurability of
postconditions. Unobserved outputs can instead be mapped into the assertion carrier.
Continuous effects require their own measurable program interface
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
    let obs : α → Measure ENNReal × Measure ENNReal := fun a ↦ (𝒟[f a], 𝒟[g a])
    let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
    have hobs : Measurable obs := comap_measurable obs
    rw [lintegral_evalDist_bind mx f (measurable_fst.comp hobs)
      (g := fun x ↦ x) measurable_id,
      lintegral_evalDist_bind mx g (measurable_snd.comp hobs)
        (g := fun x ↦ x) measurable_id]
    exact lintegral_mono hfg

namespace Quantitative

/-- Select the native ordered expectation algebra. -/
noncomputable scoped instance (priority := 1100) instMAlgOrdered : MAlgOrdered m ENNReal :=
  toMAlgOrdered m

/-- Core WP with nonnegative expectations and an empty exception postcondition.

Opening this scope selects the quantitative carrier before core instances
whose carrier is `Prop`. -/
noncomputable scoped instance (priority := 1100) instWP [LawfulMonad m] :
    Std.Internal.Do.WPMonad m ENNReal Std.Internal.Do.EPost.Nil :=
  MAlgOrdered.toWPMonad

variable {m} {α : Type}

/-- The quantitative algebra integrates its actual nonnegative output. -/
@[simp]
theorem μ_eq_lintegral (mx : m ENNReal) :
    MAlgOrdered.μ mx = ∫⁻ x, x ∂𝒟[mx] := rfl

/-- An ordered expectation WP integrates its assertion-valued observation. -/
theorem wp_eq_lintegral_map [LawfulMonad m] (mx : m α) (post : α → ENNReal) :
    MAlgOrdered.wp mx post = ∫⁻ y, y ∂𝒟[post <$> mx] := by
  rw [MAlgOrdered.wp, ← bind_pure_comp]
  exact μ_eq_lintegral _

/-- Pointwise comparison of postconditions is understood by generalized congruence. -/
@[gcongr low]
theorem wp_mono (mx : m α) {f g : α → ENNReal} (hfg : ∀ x, f x ≤ g x) :
    MAlgOrdered.wp mx f ≤ MAlgOrdered.wp mx g := MAlgOrdered.wp_mono mx hfg

variable [MeasurableSpace α]

/-- An ordered expectation WP is the integral of a measurable postcondition. -/
theorem wp_eq_lintegral (mx : m α) (post : α → ENNReal) (hpost : Measurable post) :
    MAlgOrdered.wp mx post = ∫⁻ x, post x ∂𝒟[mx] := by
  have hf : Measurable (fun x ↦ 𝒟[(pure (post x) : m ENNReal)]) := by
    simpa only [evalDist_pure, Function.comp_def] using Measure.measurable_dirac.comp hpost
  rw [MAlgOrdered.wp, μ_eq_lintegral,
    lintegral_evalDist_bind mx (fun x ↦ pure (post x)) hf (g := fun y ↦ y) measurable_id]
  simp

/-- Constant postconditions retain the successful-output mass. -/
@[simp]
theorem wp_const (mx : m α) (c : ENNReal) :
    MAlgOrdered.wp mx (fun _ ↦ c) = c * 𝒟[mx] Set.univ := by
  rw [wp_eq_lintegral mx _ measurable_const, lintegral_const]

/-- Expectation is additive in measurable postconditions. -/
theorem wp_add (mx : m α) (f g : α → ENNReal) (hf : Measurable f) (hg : Measurable g) :
    MAlgOrdered.wp mx (fun x ↦ f x + g x) = MAlgOrdered.wp mx f + MAlgOrdered.wp mx g := by
  rw [wp_eq_lintegral mx (fun x ↦ f x + g x) (hf.add hg), wp_eq_lintegral mx _ hf,
    wp_eq_lintegral mx _ hg, lintegral_add_left hf]

/-- Scaling a measurable postcondition scales its expectation. -/
theorem wp_const_mul (mx : m α) (c : ENNReal) (f : α → ENNReal) (hf : Measurable f) :
    MAlgOrdered.wp mx (fun x ↦ c * f x) = c * MAlgOrdered.wp mx f := by
  rw [wp_eq_lintegral mx (fun x ↦ c * f x) (measurable_const.mul hf), wp_eq_lintegral mx _ hf,
    lintegral_const_mul c hf]

/-- Finite sums of measurable postconditions commute with their expectation. -/
theorem wp_finsetSum {κ : Type*} (mx : m α) (s : Finset κ) (f : κ → α → ENNReal)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    MAlgOrdered.wp mx (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, MAlgOrdered.wp mx (f i) := by
  rw [wp_eq_lintegral mx _ (Finset.measurable_sum s hf), lintegral_finsetSum s hf]
  exact Finset.sum_congr rfl fun i hi ↦ (wp_eq_lintegral mx _ (hf i hi)).symm

/-- Almost-everywhere comparison is sufficient for measurable quantitative assertions. -/
theorem wp_mono_ae (mx : m α) {f g : α → ENNReal} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ g x) : MAlgOrdered.wp mx f ≤ MAlgOrdered.wp mx g := by
  rw [wp_eq_lintegral mx _ hf, wp_eq_lintegral mx _ hg]
  exact lintegral_mono_ae hfg

/-- Monotone convergence for measurable quantitative weakest preconditions. -/
theorem wp_iSup (mx : m α) (f : ℕ → α → ENNReal) (hf : Monotone f)
    (hmeas : ∀ n, Measurable (f n)) :
    MAlgOrdered.wp mx (fun x ↦ ⨆ n, f n x) = ⨆ n, MAlgOrdered.wp mx (f n) := by
  rw [wp_eq_lintegral mx _ (Measurable.iSup hmeas), lintegral_iSup hmeas hf]
  simp only [wp_eq_lintegral mx _ (hmeas _)]

/-- Bounding a measurable postcondition almost everywhere retains the success mass. -/
theorem wp_le_mul_mass (mx : m α) {post : α → ENNReal} {c : ENNReal}
    (hmeas : Measurable post) (hpost : ∀ᵐ x ∂𝒟[mx], post x ≤ c) :
    MAlgOrdered.wp mx post ≤ c * 𝒟[mx] Set.univ := by
  rw [wp_eq_lintegral mx _ hmeas]
  exact (lintegral_mono_ae hpost).trans_eq (lintegral_const c)

/-- A subprobability expectation of a bounded measurable postcondition is bounded. -/
theorem wp_le_const (mx : m α) {post : α → ENNReal} {c : ENNReal}
    (hmeas : Measurable post) (hpost : ∀ᵐ x ∂𝒟[mx], post x ≤ c) :
    MAlgOrdered.wp mx post ≤ c :=
  (wp_le_mul_mass mx hmeas hpost).trans <| by
    exact (mul_le_mul' le_rfl (evalDist_apply_univ_le_one mx)).trans_eq (mul_one c)

/-- An additive AE comparison retains the missing-mass factor for a lossy computation. -/
theorem wp_le_const_mul_mass_add (mx : m α) {f g : α → ENNReal} {c : ENNReal}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ c + g x) :
    MAlgOrdered.wp mx f ≤ c * 𝒟[mx] Set.univ + MAlgOrdered.wp mx g := by
  rw [wp_eq_lintegral mx _ hf, wp_eq_lintegral mx _ hg]
  exact (lintegral_mono_ae hfg).trans_eq <| by
    rw [lintegral_add_left measurable_const, lintegral_const]

end Quantitative
end MeasureProgramLogic
