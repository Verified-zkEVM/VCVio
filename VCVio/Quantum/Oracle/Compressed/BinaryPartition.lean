/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.CommutatorBound

/-!
# Cross blocks and two-label partitions of the truncated compressed oracle

Let `π` label the databases, `P^(i)` be the projector onto the databases of label `i` and
`I = I(π, t)` the instability (`Quantum.Database.instability`, Definition 5.3 of Chiesa, Di, Hu
and Zheng, ePrint 2025/2166). This file proves:

* **Cross blocks** (`Quantum.l2_opNorm_labelProjector_mul_truncatedOracle_mul_sq_le_six_mul`): for
  distinct labels `i ≠ j`, `‖P^(i) O^(t) P^(j)‖² ≤ 6 I`. For a set `S` of databases with
  projector `Q_S`, this is `‖Q_Sᶜ O^(t) Q_S‖² ≤ 6 I(S)`, where `I(S)` is the instability of the
  two-label partition into `S` and its complement
  (`Quantum.l2_opNorm_setProjector_mul_truncatedOracle_mul_sq_le_six_mul`).
* **Projector commutators**
  (`Quantum.l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul`):
  `‖[P^(i), O^(t)]‖² ≤ 6 I` for every label `i`, with no restriction on `π`.
* **Pinching for two labels**
  (`Quantum.l2_opNorm_pinch_truncatedOracle_sub_sq_le_six_mul`): if `π` takes at most two values,
  `‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖² ≤ 6 I`. This is the constant `6` of Chiesa, Manohar and
  Spooner (TCC 2019, Lemma 5.10), here with a proof that covers databases of size exactly `t`.
  For arbitrary labellings the optimal constant is `8`
  (`Quantum.l2_opNorm_pinch_truncatedOracle_sub_sq_le_eight_mul`).

## Comparison with [CDHZ]

[CDHZ, Lemma 5.9] bounds the pinching defect by `20 I` for every labelling. For two labels this
file proves `6`, and the cross-block and projector-commutator bounds `6 I` for every labelling.
The constant `6` is optimal for two labels: Lemma 5.10
(`Quantum.l2_opNorm_commutator_truncatedOracle_le_pinch`) and the lower bound
`Quantum.le_l2_opNorm_commutator_truncatedOracle_sq` give a two-label pinching defect of squared
norm at least `6 / N - 9 / N²` at instability at most `1 / N`; this consequence is not stated as
a separate theorem. For the commutator of [CDHZ, Theorem 5.4], the bound
`‖[V, O^(t) ⊗ 1]‖² ≤ 24 I` (`Quantum.l2_opNorm_commutator_truncatedOracle_sq_le_twentyFour_mul`
in `VCVio.Quantum.Oracle.Compressed.CommutatorSharp`) holds for every labelling, so no separate
two-label statement is given here.

## Proof

In the phase basis the cross block `P^(i) O_ph^(t) P^(j)` keeps the blocks of
`Quantum.l2_opNorm_le_of_queryBlock`. In the block of `((x, χ), r)`, its rows are the contents of
label `i` and its columns those of label `j`, and its diagonal vanishes since `i ≠ j`. If
`π r ≠ i`, every nonzero row is the row of a content `u` with `π r[x ↦ u] ≠ π r`; if `π r = i`,
the same holds for the columns. Such a row or column carries, off the diagonal, squared entries
summing to at most `6 / N` (`Quantum.sum_ite_norm_phaseCell_sq_le`), so the squared Frobenius
norm of the block is at most `6 I`. For two labels, both `O^(t) - pinch O^(t)` and
`[P^(i), O^(t)]` are sums of two cross blocks with orthogonal domains and orthogonal ranges, so
their norms are at most the larger cross block (`Matrix.l2_opNorm_sub_pinch_le_max_bool`,
`Matrix.l2_opNorm_labelProjector_commutator_le_max_bool`).

## References

* [CDHZ] A. Chiesa, Z. Di, Z. Hu and Y. Zheng, *How to Prove Post-Quantum Security for Succinct
  Non-Interactive Reductions*, ePrint 2025/2166.
-/

public section

open Matrix
open OracleSpec
open scoped Matrix.Norms.L2Operator Kronecker

namespace Quantum

/-! ## Cross blocks -/

section cross

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)] {ι : Type*} [DecidableEq ι]

/-- **The cross block, phase basis.** For distinct labels `i ≠ j`, the part of the truncated phase
oracle from the databases of label `j` to those of label `i` has
`‖P^(i) O_ph^(t) P^(j)‖² ≤ 6 I(π, t)`. -/
theorem l2_opNorm_labelProjector_mul_truncatedPhaseOracle_mul_sq_le_six_mul
    (π : Database X Y → ι) (t : ℕ) {i j : ι} (hij : i ≠ j) :
    ‖labelProjector (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) i *
        truncatedPhaseOracle X Y t *
          labelProjector (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) j‖ ^ 2 ≤
      6 * (Database.instability π t).toReal := by
  have hI : 0 ≤ (Database.instability π t).toReal := ENNReal.toReal_nonneg
  set G := labelProjector (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) i *
    truncatedPhaseOracle X Y t *
      labelProjector (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) j with hGdef
  have hG : ∀ m' m, G m' m = (if π m'.2 = i then 1 else 0) * truncatedPhaseOracle X Y t m' m *
      (if π m.2 = j then 1 else 0) := by
    intro m' m
    simp only [hGdef, labelProjector, mul_diagonal, diagonal_mul]
  suffices key : ‖G‖ ≤ √(6 * (Database.instability π t).toReal) by
    calc ‖G‖ ^ 2 ≤ √(6 * (Database.instability π t).toReal) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) key 2
      _ = 6 * (Database.instability π t).toReal := Real.sq_sqrt (by positivity)
  refine l2_opNorm_le_of_queryBlock (fun m' m h ↦ phaseBlock_eq_of_truncatedPhaseOracle_ne_zero
    fun h0 ↦ h (by rw [hG, h0]; simp)) (Real.sqrt_nonneg _) ?_
  rintro ⟨x, χ⟩ r hr
  change r x = none at hr
  change ‖of fun a' a : Option Y ↦ G ((x, χ), Function.update r x a')
    ((x, χ), Function.update r x a)‖ ≤ _
  have hrow0 : ∀ a' a, π (Function.update r x a') ≠ i →
      G ((x, χ), Function.update r x a') ((x, χ), Function.update r x a) = 0 := by
    intro a' a h
    simp [hG, h]
  have hcol0 : ∀ a' a, π (Function.update r x a) ≠ j →
      G ((x, χ), Function.update r x a') ((x, χ), Function.update r x a) = 0 := by
    intro a' a h
    simp [hG, h]
  have hle : ∀ a' a, ‖G ((x, χ), Function.update r x a') ((x, χ), Function.update r x a)‖ ^ 2 ≤
      if a' = a then 0 else ‖truncatedPhaseOracle X Y t ((x, χ), Function.update r x a')
        ((x, χ), Function.update r x a)‖ ^ 2 := by
    intro a' a
    by_cases h : a' = a
    · subst h
      by_cases hi : π (Function.update r x a') = i
      · rw [hcol0 a' a' fun hj ↦ hij (hi.symm.trans hj)]
        simp
      · rw [hrow0 a' a' hi]
        simp
    · rw [ite_eq_right h, hG]
      split_ifs <;> simp
  rw [← Real.sqrt_sq (norm_nonneg _)]
  refine Real.sqrt_le_sqrt ((l2_opNorm_sq_le_sum_sq _).trans ?_)
  simp only [of_apply]
  by_cases hri : π r = i
  · rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun a _ ↦ ?_).trans
      (sum_ite_sum_norm_truncatedPhaseOracle_col_sq_le π t x χ hr)
    split_ifs with hp
    · exact (Finset.sum_eq_zero fun a' _ ↦ by
        simp [hcol0 a' a fun hj ↦ hij (hri.symm.trans (hp.symm.trans hj))]).le
    · exact Finset.sum_le_sum fun a' _ ↦ hle a' a
  · refine (Finset.sum_le_sum fun a' _ ↦ ?_).trans
      (sum_ite_sum_norm_truncatedPhaseOracle_row_sq_le π t x χ hr)
    split_ifs with hp
    · exact (Finset.sum_eq_zero fun a _ ↦ by
        simp [hrow0 a' a fun hi ↦ hri (hp.symm.trans hi)]).le
    · exact Finset.sum_le_sum fun a _ ↦ hle a' a

/-- **The cross block.** For distinct labels `i ≠ j`, the part of the truncated compressed oracle
from the databases of label `j` to those of label `i` has `‖P^(i) O^(t) P^(j)‖² ≤ 6 I(π, t)`. -/
theorem l2_opNorm_labelProjector_mul_truncatedOracle_mul_sq_le_six_mul
    (π : Database X Y → ι) (t : ℕ) {i j : ι} (hij : i ≠ j) :
    ‖labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i * truncatedOracle X Y t *
          labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) j‖ ^ 2 ≤
      6 * (Database.instability π t).toReal := by
  have hU : ∀ a b, (queryFourier X Y)ᴴ a b ≠ 0 →
      (fun m : (X × Y) × Database X Y ↦ π m.2) a =
        (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) b := by
    rintro ⟨⟨x, y⟩, D⟩ ⟨⟨x', χ⟩, D'⟩ h
    rw [conjTranspose_apply, queryFourier_apply] at h
    by_cases hc : x' = x ∧ D' = D
    · simp [hc.2]
    · simp only [hc, ↓reduceIte, star_zero, ne_eq, not_true_eq_false] at h
  have hV : ∀ a b, queryFourier X Y a b ≠ 0 →
      (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) a =
        (fun m : (X × Y) × Database X Y ↦ π m.2) b := fun a b h ↦
    (hU b a (by rw [conjTranspose_apply]; exact star_ne_zero.mpr h)).symm
  have e₁ := mul_labelProjector_eq_labelProjector_mul _ _ hU i
  have e₂ := mul_labelProjector_eq_labelProjector_mul _ _ hV j
  have e : labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i * truncatedOracle X Y t *
      labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) j =
        (queryFourier X Y)ᴴ *
          (labelProjector (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) i *
            truncatedPhaseOracle X Y t *
              labelProjector (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) j) *
          queryFourier X Y := by
    rw [truncatedOracle_eq]
    simp only [← Matrix.mul_assoc]
    rw [← e₁]
    simp only [Matrix.mul_assoc]
    rw [e₂]
  rw [e]
  exact (pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_conjTranspose_mul_mul_le
    (queryFourier_mul_conjTranspose X Y) _) 2).trans
    (l2_opNorm_labelProjector_mul_truncatedPhaseOracle_mul_sq_le_six_mul π t hij)

omit [DecidableEq ι] in
/-- **The cross block of a set of databases.** For a set `S` of databases with projector `Q_S`,
`‖Q_Sᶜ O^(t) Q_S‖² ≤ 6 I(S)` and `‖Q_S O^(t) Q_Sᶜ‖² ≤ 6 I(S)`, where `I(S)` is the instability of
the two-label partition into `S` and its complement. -/
theorem l2_opNorm_setProjector_mul_truncatedOracle_mul_sq_le_six_mul (S : Set (Database X Y))
    [DecidablePred (· ∈ S)] (t : ℕ) (b : Bool) :
    ‖labelProjector (fun m : (X × Y) × Database X Y ↦ decide (m.2 ∈ S)) (!b) *
        truncatedOracle X Y t *
          labelProjector (fun m : (X × Y) × Database X Y ↦ decide (m.2 ∈ S)) b‖ ^ 2 ≤
      6 * (Database.instability (fun D ↦ decide (D ∈ S)) t).toReal :=
  l2_opNorm_labelProjector_mul_truncatedOracle_mul_sq_le_six_mul (fun D ↦ decide (D ∈ S)) t
    (Bool.not_ne_self b)

end cross

/-! ## Two labels -/

section bool

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [UniformAnswerMeasure (X →ₒ Y)]

/-- Each of the two cross blocks of a labelling by `Bool` has norm at most `√(6 I)`. -/
private theorem l2_opNorm_labelProjector_mul_truncatedOracle_mul_le_sqrt
    (π : Database X Y → Bool) (t : ℕ) (b : Bool) :
    ‖labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) b * truncatedOracle X Y t *
          labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) (!b)‖ ≤
      √(6 * (Database.instability π t).toReal) := by
  simpa using Real.abs_le_sqrt
    (l2_opNorm_labelProjector_mul_truncatedOracle_mul_sq_le_six_mul π t (Bool.not_ne_self b).symm)

/-- Pinching by a labelling by `Bool`, with the constant `6`. -/
private theorem l2_opNorm_pinch_truncatedOracle_sub_sq_le_six_mul_of_bool
    (π : Database X Y → Bool) (t : ℕ) :
    ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
        truncatedOracle X Y t‖ ^ 2 ≤ 6 * (Database.instability π t).toReal := by
  have hI : 0 ≤ (Database.instability π t).toReal := ENNReal.toReal_nonneg
  have h := l2_opNorm_sub_pinch_le_max_bool (fun m : (X × Y) × Database X Y ↦ π m.2)
    (truncatedOracle X Y t)
  rw [norm_sub_rev] at h
  have h' := h.trans (max_le (l2_opNorm_labelProjector_mul_truncatedOracle_mul_le_sqrt π t true)
    (l2_opNorm_labelProjector_mul_truncatedOracle_mul_le_sqrt π t false))
  calc _ ≤ √(6 * (Database.instability π t).toReal) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = _ := Real.sq_sqrt (by positivity)

variable {ι : Type*} [DecidableEq ι]

/-- **The commutator with a label projector.** For every labelling `π` and every label `i`, the
projector `P^(i)` onto the databases of label `i` almost commutes with the truncated compressed
oracle: `‖[P^(i), O^(t)]‖² ≤ 6 I(π, t)`. -/
theorem l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul
    (π : Database X Y → ι) (t : ℕ) (i : ι) :
    ‖labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i * truncatedOracle X Y t -
        truncatedOracle X Y t * labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i‖ ^ 2 ≤
      6 * (Database.instability π t).toReal := by
  have hI : 0 ≤ (Database.instability (fun D ↦ decide (π D = i)) t).toReal :=
    ENNReal.toReal_nonneg
  have hP : (labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) i :
      Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) =
        labelProjector (fun m : (X × Y) × Database X Y ↦ decide (π m.2 = i)) true := by
    simp only [labelProjector, decide_eq_true_eq]
  rw [hP]
  have h := l2_opNorm_labelProjector_commutator_le_max_bool
    (fun m : (X × Y) × Database X Y ↦ decide (π m.2 = i)) true (truncatedOracle X Y t)
  have h' := h.trans (max_le
    (l2_opNorm_labelProjector_mul_truncatedOracle_mul_le_sqrt (fun D ↦ decide (π D = i)) t true)
    (l2_opNorm_labelProjector_mul_truncatedOracle_mul_le_sqrt (fun D ↦ decide (π D = i)) t false))
  calc _ ≤ √(6 * (Database.instability (fun D ↦ decide (π D = i)) t).toReal) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = 6 * (Database.instability (fun D ↦ decide (π D = i)) t).toReal :=
        Real.sq_sqrt (by positivity)
    _ ≤ 6 * (Database.instability π t).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (Database.instability_ne_top π t)
          (Database.instability_decide_eq_le π i t)) (by norm_num)

/-- **Pinching for two labels with the constant `6`.** If the labelling `π` takes at most two
values, pinching the truncated compressed oracle moves it by at most `√(6 I)`:
`‖∑ i, P^(i) O^(t) P^(i) - O^(t)‖² ≤ 6 I(π, t)`. This is the constant of Chiesa, Manohar and
Spooner (TCC 2019, Lemma 5.10), and it is optimal for two labels (proved on paper). -/
theorem l2_opNorm_pinch_truncatedOracle_sub_sq_le_six_mul (π : Database X Y → ι) (t : ℕ)
    (hπ : ∃ i₀ i₁, ∀ D, π D = i₀ ∨ π D = i₁) :
    ‖pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) -
        truncatedOracle X Y t‖ ^ 2 ≤ 6 * (Database.instability π t).toReal := by
  obtain ⟨i₀, i₁, hπ⟩ := hπ
  have hb : ∀ D D', π D = π D' ↔ decide (π D = i₀) = decide (π D' = i₀) := by
    intro D D'
    by_cases e : i₁ = i₀
    · subst e
      have h₁ : π D = π D' := by
        rcases hπ D with h | h <;> rcases hπ D' with h' | h' <;> rw [h, h']
      simp [h₁]
    · have e' : i₀ ≠ i₁ := fun h ↦ e h.symm
      rcases hπ D with h | h <;> rcases hπ D' with h' | h' <;> simp [h, h', e, e']
  have hpinch : pinch (fun m : (X × Y) × Database X Y ↦ π m.2) (truncatedOracle X Y t) =
      pinch (fun m : (X × Y) × Database X Y ↦ decide (π m.2 = i₀)) (truncatedOracle X Y t) := by
    ext a b
    rw [pinch_apply, pinch_apply]
    exact if_congr (hb a.2 b.2) rfl rfl
  rw [hpinch]
  exact (l2_opNorm_pinch_truncatedOracle_sub_sq_le_six_mul_of_bool
    (fun D ↦ decide (π D = i₀)) t).trans
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (Database.instability_ne_top π t)
      (Database.instability_decide_eq_le π i₀ t)) (by norm_num))

/-- **Pinching for two labels with the constant `6`, phase basis.** -/
theorem l2_opNorm_pinch_truncatedPhaseOracle_sub_sq_le_six_mul (π : Database X Y → ι) (t : ℕ)
    (hπ : ∃ i₀ i₁, ∀ D, π D = i₀ ∨ π D = i₁) :
    ‖pinch (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) (truncatedPhaseOracle X Y t) -
        truncatedPhaseOracle X Y t‖ ^ 2 ≤ 6 * (Database.instability π t).toReal := by
  have hV : ∀ a b, queryFourier X Y a b ≠ 0 →
      (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2) a =
        (fun m : (X × Y) × Database X Y ↦ π m.2) b := by
    rintro ⟨⟨x', χ⟩, D'⟩ ⟨⟨x, y⟩, D⟩ h
    rw [queryFourier_apply] at h
    by_cases hc : x' = x ∧ D' = D
    · simp [hc.2]
    · simp only [hc, ↓reduceIte, ne_eq, not_true_eq_false] at h
  have e := mul_pinch_mul_conjTranspose (fun m : (X × AddChar Y ℂ) × Database X Y ↦ π m.2)
    (fun m : (X × Y) × Database X Y ↦ π m.2) hV (truncatedOracle X Y t)
  rw [← truncatedPhaseOracle_eq] at e
  rw [← e, truncatedPhaseOracle_eq, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_mul_mul_conjTranspose_le
    (conjTranspose_queryFourier_mul X Y) _) 2).trans
    (l2_opNorm_pinch_truncatedOracle_sub_sq_le_six_mul π t hπ)

end bool

end Quantum
