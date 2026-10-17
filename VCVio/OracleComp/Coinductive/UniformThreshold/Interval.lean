/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.UniformThreshold.Cost
public import VCVio.ProgramLogic.Relational.Reconstruction
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lebesgue reconstruction of a retained dyadic prefix

A prefix represents the normalized Lebesgue law on its half-open cell. Refining it by one
fair bit splits that law into the equal mixture of its two child cells. This posterior law
is the semantic connection between the finite integer representation and the ideal real
state; the implementation never constructs or samples a real number.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor Set
open scoped ENNReal

namespace UniformThreshold

/-- A dyadic cell has exactly the reciprocal-power width. -/
theorem Prefix.width (p : Prefix) : p.upper - p.lower = ((2 : ℚ) ^ p.depth)⁻¹ := by
  simp only [Prefix.upper, Prefix.lower]
  field_simp
  ring

/-- The real states represented by a finite bit prefix. -/
def Prefix.interval (p : Prefix) : Set ℝ := Ico (p.lower : ℝ) (p.upper : ℝ)

/-- Membership in a represented cell is the corresponding pair of endpoint inequalities. -/
theorem Prefix.mem_interval (p : Prefix) (u : ℝ) :
    u ∈ p.interval ↔ (p.lower : ℝ) ≤ u ∧ u < (p.upper : ℝ) := by rfl

/-- Normalized Lebesgue measure on the prefix's half-open dyadic cell. -/
noncomputable def cellLaw (p : Prefix) : Measure ℝ :=
  (2 : ℝ≥0∞) ^ p.depth • volume.restrict p.interval

/-- The Lebesgue volume of a dyadic cell is its reciprocal-power width. -/
theorem Prefix.volume_interval (p : Prefix) : volume p.interval = (2 : ℝ≥0∞)⁻¹ ^ p.depth := by
  rw [Prefix.interval, Real.volume_Ico, ← Rat.cast_sub, Prefix.width]
  simp only [Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat]
  rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < (2 : ℝ) ^ p.depth),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  exact ENNReal.inv_pow

instance (p : Prefix) : IsProbabilityMeasure (cellLaw p) := by
  constructor
  rw [cellLaw, Measure.smul_apply, Measure.restrict_apply_univ, p.volume_interval, smul_eq_mul,
    ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]

/-- The normalized cell law is concentrated on the represented interval. -/
theorem cellLaw_ae_interval (p : Prefix) : ∀ᵐ u ∂cellLaw p, u ∈ p.interval := by
  unfold cellLaw
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ico) _

/-- The initial prefix represents exactly uniform Lebesgue measure on `[0,1)`. -/
theorem cellLaw_empty : cellLaw Prefix.empty = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [cellLaw, Prefix.empty, Prefix.interval, Prefix.lower, Prefix.upper]

/-- The child cells partition their parent, with no duplicated midpoint. -/
theorem Prefix.interval_split (p : Prefix) :
    (p.push false).interval ∪ (p.push true).interval = p.interval := by
  have hm : ((p.push false).upper : ℝ) = ((p.push true).lower : ℝ) :=
    congrArg (fun q : ℚ => (q : ℝ)) p.upper_push_false_eq_lower_push_true
  have hl : ((p.push false).lower : ℝ) < ((p.push false).upper : ℝ) :=
    by exact_mod_cast (p.push false).lower_lt_upper
  have hr : ((p.push true).lower : ℝ) < ((p.push true).upper : ℝ) :=
    by exact_mod_cast (p.push true).lower_lt_upper
  simp only [Prefix.interval, Prefix.lower_push_false, Prefix.upper_push_true] at *
  ext u
  simp only [mem_union, mem_Ico]
  constructor
  · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
  · intro h
    by_cases hu : u < ((p.push false).upper : ℝ)
    · exact Or.inl ⟨h.1, hu⟩
    · exact Or.inr ⟨by linarith, h.2⟩

/-- The two child cells are disjoint. -/
theorem Prefix.disjoint_intervals (p : Prefix) :
    Disjoint (p.push false).interval (p.push true).interval := by
  apply Set.disjoint_left.mpr
  intro u hl hr
  have hm := congrArg (fun q : ℚ => (q : ℝ)) p.upper_push_false_eq_lower_push_true
  exact (not_lt_of_ge hr.1) (hl.2.trans_eq hm)

/-- One fair bit reconstructs the parent law as the equal mixture of its child laws. -/
theorem cellLaw_split (p : Prefix) :
    (2 : ℝ≥0∞)⁻¹ • (cellLaw (p.push false) + cellLaw (p.push true)) = cellLaw p := by
  have hc : (2 : ℝ≥0∞)⁻¹ * 2 ^ (p.depth + 1) = 2 ^ p.depth := by
    rw [pow_succ, mul_left_comm, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  rw [cellLaw, cellLaw, cellLaw, smul_add, smul_smul, smul_smul,
    Prefix.depth_push, Prefix.depth_push, hc, ← smul_add,
    ← Measure.restrict_union p.disjoint_intervals measurableSet_Ico, p.interval_split]

/-- The measurable posterior kernel reconstructing a real state from finite bits. -/
noncomputable def reconstruct : Kernel Prefix ℝ := ⟨cellLaw, Measurable.of_discrete⟩

instance : IsMarkovKernel reconstruct := ⟨fun p => by
  change IsProbabilityMeasure (cellLaw p)
  infer_instance⟩

/-- The posterior kernel at a prefix is its normalized cell law. -/
theorem reconstruct_apply (p : Prefix) : reconstruct p = cellLaw p := by rfl

end UniformThreshold
