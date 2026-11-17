/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.NumberedQueries

/-!
# Hybrid bounds for one numbered oracle call

A numbered translation fixes each port's tag to the call's position. When two runtime
schedules agree away from one tag, the square-root hybrid argument charges only that call.
The final observation is arbitrary and common to both runs; it may depend on externally
fixed challenge data, including a hidden endpoint.

The schedules retain the same private register and initial state. This is an event bound
for adaptive mixed and subnormalized programs, without an independence assumption on the
externally fixed data.
-/

public section

open Matrix MeasureTheory
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.QuantumRuntime

universe u v u₁ v₁ w

private theorem event_le_of_rpow_inv_two_le {p a e : ℝ≥0∞} (hp : p ≤ 1) (ha : a ≤ 1)
    (h : p ^ (2⁻¹ : ℝ) ≤ a ^ (2⁻¹ : ℝ) + e) : p ≤ a + 2 * e := by
  by_cases he : e = ⊤
  · simp [he]
  have hp' : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have ht : a + 2 * e ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha', ENNReal.mul_ne_top (by norm_num) he⟩
  apply (ENNReal.toReal_le_toReal hp' ht).mp
  rw [ENNReal.toReal_add ha' (ENNReal.mul_ne_top (by norm_num) he), ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_ofNat]
  have hr := (ENNReal.toReal_le_toReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hp')
    (ENNReal.add_ne_top.mpr ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) ha', he⟩)).mpr h
  rw [ENNReal.toReal_add (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ha') he,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hr
  have hsqrt (z : ℝ) : z ^ (2⁻¹ : ℝ) = Real.sqrt z := by
    simpa only [one_div] using (Real.sqrt_eq_rpow z).symm
  rw [hsqrt, hsqrt] at hr
  have hpp : p.toReal ≤ 1 := by simpa using (ENNReal.toReal_le_toReal hp' ENNReal.one_ne_top).mpr hp
  have haa : a.toReal ≤ 1 := by simpa using (ENNReal.toReal_le_toReal ha' ENNReal.one_ne_top).mpr ha
  have hsp : Real.sqrt p.toReal ≤ 1 := (Real.sqrt_le_one).mpr hpp
  have hsa : Real.sqrt a.toReal ≤ 1 := (Real.sqrt_le_one).mpr haa
  have hps := Real.sq_sqrt (ENNReal.toReal_nonneg (a := p))
  have has := Real.sq_sqrt (ENNReal.toReal_nonneg (a := a))
  by_cases hpa : p.toReal ≤ a.toReal
  · exact hpa.trans (le_add_of_nonneg_right (by positivity))
  · have hsap : Real.sqrt a.toReal ≤ Real.sqrt p.toReal := Real.sqrt_le_sqrt (by linarith)
    have hm := mul_le_mul (show Real.sqrt p.toReal - Real.sqrt a.toReal ≤ e.toReal by linarith)
      (show Real.sqrt p.toReal + Real.sqrt a.toReal ≤ 2 by linarith)
      (by positivity : 0 ≤ Real.sqrt p.toReal + Real.sqrt a.toReal)
      (ENNReal.toReal_nonneg (a := e))
    nlinarith

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}}
  {W : QReg → Type w} {A D : QReg}
  {s₀ s₁ : ∀ i, SubInstrument (spec.numbered.In i × D)
    (spec.numbered.Out i × D) (spec.numbered.Result i)}
  {U V : ∀ i, spec.numbered.Result i → Matrix (spec.numbered.Out i × D)
    (spec.numbered.In i × D) ℂ}

/-- Changing only the schedule entry tagged `t + h` charges the pre-query weight at
actual call `h` of a program numbered from `t`. -/
theorem rpow_inv_two_evalDistMap_numberQueries_le_of_eq_off_tag (I : L.Interp) (σ : SubState D)
    (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
    (hV : ∀ i r, (s₁ i).branch r = MatrixMap.conj (V i r))
    (x : QuantumComp L spec W A) (t h : ℕ)
    (hoff : ∀ i r, i.1 ≠ t + h → U i r = V i r)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ B, W B) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (QuantumRuntime.mk D σ s₁).evalDistMap I (x.numberQueries t) ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ s₀).evalDistMap I (x.numberQueries t) ρ f s ^ (2⁻¹ : ℝ) +
        (QuantumRuntime.mk D σ s₀).queryWeight I
          (QuantumRuntime.krausWeight (fun i r ↦ U i r - V i r))
          (x.numberQueries t) (ρ.matrix ⊗ₖ σ.matrix) h ^ (2⁻¹ : ℝ) := by
  have hb := QuantumRuntime.rpow_inv_two_outcomeLawWith_le'
    (spec := spec.numbered) (D := D) (s₀ := s₀) (s₁ := s₁) (U := U) (W := V)
    I σ hU hV (x.numberQueries t) ρ f hs
  refine hb.trans_eq ?_
  congr 1
  apply tsum_eq_single h
  intro j hj
  have hz : (QuantumRuntime.mk D σ s₀).queryWeight I
      (QuantumRuntime.krausWeight (fun i r ↦ U i r - V i r))
      (x.numberQueries t) (ρ.matrix ⊗ₖ σ.matrix) j = 0 := by
    apply QuantumRuntime.queryWeight_numberQueries_eq_zero
    intro i η hi
    have hne : i.1 ≠ t + h := by omega
    simp [QuantumRuntime.krausWeight, hoff i _ hne]
  rw [hz, ENNReal.zero_rpow_of_pos (by norm_num)]

/-- The event probability gap for a change at one numbered call. Both output laws
are subprobabilities, so converting the square-root gap costs a factor of two. -/
theorem evalDistMap_numberQueries_le_of_eq_off_tag (I : L.Interp) (σ : SubState D)
    (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
    (hV : ∀ i r, (s₁ i).branch r = MatrixMap.conj (V i r))
    (x : QuantumComp L spec W A) (t h : ℕ)
    (hoff : ∀ i r, i.1 ≠ t + h → U i r = V i r)
    (ρ : SubState A) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ B, W B) → γ) {s : Set γ} (hs : MeasurableSet s) :
    (QuantumRuntime.mk D σ s₁).evalDistMap I (x.numberQueries t) ρ f s ≤
      (QuantumRuntime.mk D σ s₀).evalDistMap I (x.numberQueries t) ρ f s +
        2 * (QuantumRuntime.mk D σ s₀).queryWeight I
          (QuantumRuntime.krausWeight (fun i r ↦ U i r - V i r))
          (x.numberQueries t) (ρ.matrix ⊗ₖ σ.matrix) h ^ (2⁻¹ : ℝ) := by
  exact event_le_of_rpow_inv_two_le (measure_le_one _ _) (measure_le_one _ _)
    (rpow_inv_two_evalDistMap_numberQueries_le_of_eq_off_tag I σ hU hV x t h hoff ρ f hs)

end Quantum.QuantumRuntime
