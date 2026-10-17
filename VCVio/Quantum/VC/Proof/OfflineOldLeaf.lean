/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldChallenger

/-!
# The four old-checker amplitudes at an adaptive leaf

The checker budget counts all raw path checks. Each bound retains the original leaf trace,
so it can be summed over arbitrary adaptive leaves without a cardinality loss.
-/

public section

open Matrix
open scoped ENNReal Kronecker Matrix.Norms.L2Operator
namespace Quantum

/-- Two real checker discrepancies combine before charging the leaf's trace. -/
theorem checker_amplitudes_le {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a + b ≤ 2 * Real.sqrt r) (m : ℝ≥0∞) :
    (ENNReal.ofReal (a ^ 2) * m) ^ (2⁻¹ : ℝ) +
      (ENNReal.ofReal (b ^ 2) * m) ^ (2⁻¹ : ℝ) ≤
        (ENNReal.ofReal (4 * r) * m) ^ (2⁻¹ : ℝ) := by
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹),
    ENNReal.ofReal_rpow_inv_two, Real.sqrt_sq ha, Real.sqrt_sq hb, ← add_mul]
  apply mul_le_mul_left
  rw [← ENNReal.ofReal_add ha hb, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  exact ENNReal.ofReal_le_ofReal h

end Quantum

namespace Quantum.SaltedMerkle
open _root_.SaltedMerkle
variable {X Y Msg Salt : Type} [DecidableEq X] [LinearOrder Y] [SampleableType Salt]
  (enc : Encoding X Y Msg Salt) {k : ℕ} (d : ℕ)

/-- Both checker batches together use at most one path of `d + 1` checks per opened leaf. -/
theorem length_two_batches_le (qs : ℕ)
    (c : OpeningClaim k Y Msg (fun _ ↦ 2 ^ d) (fun _ ↦ Pf Y Salt d))
    (hq : ∑ i, (c.ans i).dom.card ≤ qs) :
    (batchIO (fun _ ↦ checkIOForm enc d) c.W c).length +
      (batchIO (fun _ ↦ checkIOForm enc d) c.Wᶜ c).length ≤ qs * (d + 1) := by
  classical
  rw [length_batchIO, length_batchIO, Finset.sum_add_sum_compl]
  calc
    _ ≤ ∑ i, (c.ans i).dom.card * (d + 1) := by
      apply Finset.sum_le_sum
      intro i _
      cases he : outputIO enc d (c.cm i) (c.ans i) (c.pf i) with
      | none => simp [checkIOForm, he]
      | some ps =>
        simpa [checkIOForm, he] using length_outputIO_le enc (c.cm i) (c.ans i) (c.pf i) ps he
    _ = (∑ i, (c.ans i).dom.card) * (d + 1) := (Finset.sum_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hq

omit [DecidableEq X] in
open scoped Classical in
/-- The Merkle good-database complement is exactly the ordinary-runtime collision event. -/
theorem good_complement_eq_collision [Fintype X] :
    1 - diagonal (fun D : Fin k → Database X Y ↦
      if ∀ i, D i ∈ collisionFree then (1 : ℂ) else 0) =
        extractCollisionMatrix (k := k) (X := X) (Y := Y) := by
  classical
  rw [← diagonal_one, diagonal_sub]
  unfold extractCollisionMatrix labelProjector
  congr 1
  funext D
  have he : (∀ i, D i ∈ collisionFree) ↔ Database.AllCollisionFree D := by
    rfl
  simp only [Database.allCollisionLabel, decide_eq_true_eq, he]
  by_cases h : Database.AllCollisionFree D <;> simp [h]

variable [Fintype X] [Fintype Y] [AddCommGroup Y] [Fintype Msg] [LinearOrder Msg]
  [Fintype Salt] [LinearOrder Salt] {Z : Type} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The actual old offline challenger satisfies the four-amplitude bound on each original
population-supported leaf, including over-budget and malformed claims. -/
theorem offlineChallenger_four_amplitudes
    (code : TpDCode k (DmOf (fun _ ↦ 2 ^ d) Msg (fun _ ↦ Td Y Salt d)) Z)
    (hk : 1 ≤ k) (s qs : ℕ)
    (c : OpeningClaim k Y Msg (fun _ ↦ 2 ^ d) (fun _ ↦ Pf Y Salt d)) (B : QReg)
    (ρ : SubState (B × (Fin k → Database X Y)))
    (hpop : diagonal (fun a : B × (Fin k → Database X Y) ↦
      if databasePopulation a.2 ≤ s then (1 : ℂ) else 0) * ρ.matrix = ρ.matrix) :
    let VC := fun _ : Fin k ↦ (scheme enc d).toVectorCommitment
    let R := ((compressedVCOracle k X Y).withExtract
      (multiExtract enc (fun _ ↦ d)) code).coherent.toRuntime
    ((R.run₂ .instruments (offlineChallenger VC code hk qs c B)).outcomeMeasure ρ {true}) ^
        (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ extractCollisionMatrix)
          ρ.matrix).trace.re ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * (qs * (d + 1) : ℕ) / (Fintype.card Y : ℝ)) *
          ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) +
        (QuantumRuntime.potential (CompressedReplay.invalidStack (k := k) (X := X) (Y := Y))
          ρ.matrix) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (4 * s * oldChangingFraction (Fintype.card Y) s) *
          ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) := by
  classical
  let io := fun _ : Fin k ↦ checkIOForm enc d
  let ME := multiExtract enc (fun _ : Fin k ↦ d)
  by_cases hq : ∑ i, (c.ans i).dom.card ≤ qs
  · have hh := offlineChallenger_le_bad_add_distances io ME (fun _ ↦ tdBot) collisionFree
      (conditions enc (fun _ ↦ d)) code hk qs c B ρ
    have hi := measured_actual_filled_le_invalid enc (fun _ ↦ d) io hk c B s
      ρ.posSemidef hpop
    have hl := length_two_batches_le enc d qs c hq
    have hl' : (((batchIO io c.W c).length : ℝ) + (batchIO io c.Wᶜ c).length) /
        (Fintype.card Y : ℝ) ≤ (qs * (d + 1) : ℕ) / (Fintype.card Y : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hl
    have hn := (two_batch_reference_distance_le io c B).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl') (by norm_num : (0 : ℝ) ≤ 2))
    have hc := checker_amplitudes_le (norm_nonneg _) (norm_nonneg _) hn
      (ENNReal.ofReal ρ.matrix.trace.re)
    rw [← mul_div_assoc] at hc
    have hsum := add_le_add (add_le_add (le_refl (ENNReal.ofReal
      (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ extractCollisionMatrix) ρ.matrix).trace.re ^
        (2⁻¹ : ℝ))) hc) hi
    dsimp only at hh
    have he := good_complement_eq_collision (k := k) (X := X) (Y := Y)
    rw [he] at hh
    exact hh.trans (by simpa only [add_assoc] using hsum)
  · dsimp only
    rw [offlineChallenger_over_budget io ME code hk qs c B ρ hq,
      ENNReal.zero_rpow_of_pos (by norm_num)]
    positivity

end Quantum.SaltedMerkle
