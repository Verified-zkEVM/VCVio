/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldBatches
import all VCVio.Quantum.VC.Tuples

/-!
# The outcome-preserving partial-database comparison

The accepted partial-database map, followed by the actual randomized opening and mismatch
decision, is charged entirely to the original bad-database weight. The extraction result
remains a classical outcome throughout this comparison.
-/

public section

open Matrix
open scoped ComplexOrder Kronecker ENNReal Matrix.Norms.L2Operator
namespace Quantum

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z]
  [DecidableEq Z] [AddGroup Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  [∀ i, DecidableEq (DmOf ℓ Msg Td i)] [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).CheckIOForm)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))
  (tdBot : ∀ i, Td i) (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]

omit [DecidableEq Msg] [∀ i, DecidableEq (Pf i)] [AddCommGroup Y] [Fintype Cm]
  [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z] in
/-- The measured extraction projectors form a trace-nonincreasing family on every reference
register. The outcome type is unrestricted. -/
theorem extractProj_isCPTNIFamily (tic : TpIC k Cm) (B : QReg) :
    MatrixMap.IsCPTNIFamily (fun tdm ↦
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ extractProj ME tic tdm)) := by
  classical
  have he (tdm) : (1 : Matrix B B ℂ) ⊗ₖ extractProj ME tic tdm =
      diagonal (fun b : B × (Fin k → Database X Y) ↦
        if True ∧ ME.extract tic b.2 = tdm then (1 : ℂ) else 0) := by
    simp only [extractProj, ← diagonal_one, diagonal_kronecker_diagonal, one_mul, true_and]
  simp_rw [he]
  convert MatrixMap.accepted_label_isCPTNIFamily
    (ι := TpDLen k (DmOf ℓ Msg Td) tic.1)
    (fun _ : B × (Fin k → Database X Y) ↦ True)
    (fun b : B × (Fin k → Database X Y) ↦ ME.extract tic b.2) using 1

/-- The outcome-preserving partial-database mismatch event is bounded by the original
bad-database weight. This includes randomized openings and arbitrary entangled input matrices. -/
theorem offlineFinish_partial_le_bad (hC : Conditions VC io ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    {ρ : Matrix (B × (Fin k → Database X Y)) (B × (Fin k → Database X Y)) ℂ}
    (hρ : ρ.PosSemidef) :
    let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
    let Pa := checkPassProjector io c.W c.idx c.cm c.ans c.pf
    let Pb := checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf
    let G := diagonal (fun D : Fin k → Database X Y ↦
      if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
    (∑' tdm, ENNReal.ofReal (((R.run₂ .instruments
      (offlineFinish (VC := VC) (Z := Z) hk qs c B (true, some tdm, true))).branch true)
        (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
          (Pb * extractProj ME (TpIC.full hk c.idx c.cm) tdm * Pa)) ρ)).trace.re) ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (1 - G)) ρ).trace.re := by
  classical
  let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
  let Pa := checkPassProjector io c.W c.idx c.cm c.ans c.pf
  let Pb := checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf
  let G := diagonal (fun D : Fin k → Database X Y ↦
    if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
  let Φ := fun tdm ↦ (R.run₂ .instruments
    (offlineFinish (VC := VC) (Z := Z) hk qs c B (true, some tdm, true))).branch true
  let K := fun (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) ↦ (1 : Matrix B B ℂ) ⊗ₖ
    (Pb * extractProj ME (TpIC.full hk c.idx c.cm) tdm * Pa)
  have hK : MatrixMap.IsCPTNIFamily (fun tdm ↦ MatrixMap.conj (K tdm)) := by
    have he : ∀ tdm, K tdm = diagonal (fun b : B × (Fin k → Database X Y) ↦
        if ((∀ i ∈ c.Wᶜ, (io i).checkOn (b.2 (c.idx i))
            (c.cm i) (c.ans i) (c.pf i) = true) ∧
          (∀ i ∈ c.W, (io i).checkOn (b.2 (c.idx i))
            (c.cm i) (c.ans i) (c.pf i) = true)) ∧
          ME.extract (TpIC.full hk c.idx c.cm) b.2 = tdm then (1 : ℂ) else 0) := by
      intro tdm
      simp only [K, Pa, Pb, checkPassProjector, extractProj, diagonal_mul_diagonal,
        ← diagonal_one, diagonal_kronecker_diagonal, one_mul]
      congr 1
      funext b
      have hp (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
          (if a then (1 : ℂ) else 0) * (if b then 1 else 0) *
            (if c then 1 else 0) = if (a ∧ c) ∧ b then 1 else 0 := by
        by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp [ha, hb, hc]
      convert hp
        (∀ i ∈ c.Wᶜ, (io i).checkOn (b.2 (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true)
        (ME.extract (TpIC.full hk c.idx c.cm) b.2 = tdm)
        (∀ i ∈ c.W, (io i).checkOn (b.2 (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true)
        using 1
      congr! 4
    simp_rw [he]
    convert MatrixMap.accepted_label_isCPTNIFamily
      (ι := TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk))
      (fun b : B × (Fin k → Database X Y) ↦
        (∀ i ∈ c.Wᶜ, (io i).checkOn (b.2 (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true) ∧
        (∀ i ∈ c.W, (io i).checkOn (b.2 (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true))
      (fun b ↦ ME.extract (TpIC.full hk c.idx c.cm) b.2) using 1
    congr! 6
  have hz (tdm) : Φ tdm ∘ₗ MatrixMap.conj (K tdm * ((1 : Matrix B B ℂ) ⊗ₖ G)) = 0 := by
    dsimp only [K]
    rw [← mul_kronecker_mul, Matrix.one_mul]
    exact run₂_offlineFinish_partial_good_zero io ME tdBot Pgood hC code hk qs c B tdm
  have hh := MatrixMap.finish_sum_le_complement Φ
    (fun tdm ↦ (R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z)
      hk qs c B (true, some tdm, true))).isCP_branch true)
    (fun tdm ↦ (R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z)
      hk qs c B (true, some tdm, true))).isCPTNIFamily.isTNI true)
    K hK ((1 : Matrix B B ℂ) ⊗ₖ G) hz hρ
  have he : (1 : Matrix (B × (Fin k → Database X Y)) _ ℂ) - 1 ⊗ₖ G =
      (1 : Matrix B B ℂ) ⊗ₖ (1 - G) := by
    rw [← Matrix.one_kronecker_one]
    ext a b
    simp only [Matrix.sub_apply, kroneckerMap_apply, mul_sub]
  rw [he] at hh
  exact hh

/-- The filled comparison retains each extraction outcome and its finishing instrument.
Its mismatch amplitude is bounded by the original bad-database amplitude and the two
checker discrepancies, with the substate trace retained in both discrepancy terms. -/
theorem offlineFinish_filled_le_bad_add_distance (hC : Conditions VC io ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    {ρ : Matrix (B × (Fin k → Database X Y)) (B × (Fin k → Database X Y)) ℂ}
    (hρ : ρ.PosSemidef) :
    let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
    let P := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf
    let Q := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c
    let G := diagonal (fun D : Fin k → Database X Y ↦
      if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
    (∑' tdm, ENNReal.ofReal (((R.run₂ .instruments
      (offlineFinish (VC := VC) (Z := Z) hk qs c B (true, some tdm, true))).branch true)
        (MatrixMap.conj (Q c.Wᶜ * ((1 : Matrix B B ℂ) ⊗ₖ
          extractProj ME (TpIC.full hk c.idx c.cm) tdm) * Q c.W) ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (1 - G)) ρ).trace.re ^
          (2⁻¹ : ℝ) +
        (ENNReal.ofReal (‖Q c.W - P c.W‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (‖Q c.Wᶜ - P c.Wᶜ‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  classical
  let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
  let P := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf
  let Q := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c
  let T := fun (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) ↦
    (1 : Matrix B B ℂ) ⊗ₖ extractProj ME (TpIC.full hk c.idx c.cm) tdm
  let Φ := fun tdm ↦ (R.run₂ .instruments
    (offlineFinish (VC := VC) (Z := Z) hk qs c B (true, some tdm, true))).branch true
  have hΦ (tdm) : (Φ tdm).IsCP := (R.run₂ .instruments
    (offlineFinish (VC := VC) (Z := Z) hk qs c B (true, some tdm, true))).isCP_branch true
  have ht (tdm) : (Φ tdm).IsTNI := (R.run₂ .instruments
    (offlineFinish (VC := VC) (Z := Z) hk qs c B
      (true, some tdm, true))).isCPTNIFamily.isTNI true
  have hT : MatrixMap.IsCPTNIFamily (fun tdm ↦ MatrixMap.conj (T tdm)) :=
    extractProj_isCPTNIFamily ME (TpIC.full hk c.idx c.cm) B
  have hd := MatrixMap.measured_two_batches_distance_le T hT
    (Q c.W) (Q c.Wᶜ) (P c.W) (P c.Wᶜ)
    ((MatrixMap.norm_one_kronecker_le _).trans (norm_filledBatch_le_one io c.Wᶜ c))
    ((MatrixMap.norm_one_kronecker_le _).trans (norm_checkPassProjector_le_one io c.W c)) hρ
  have hh := MatrixMap.finish_comparison Φ hΦ ht hρ
    (fun tdm ↦ Q c.Wᶜ * T tdm * Q c.W) (fun tdm ↦ P c.Wᶜ * T tdm * P c.W)
  have hb := offlineFinish_partial_le_bad io ME tdBot Pgood hC code hk qs c B hρ
  have he (tdm) : P c.Wᶜ * T tdm * P c.W = (1 : Matrix B B ℂ) ⊗ₖ
      (checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf *
        extractProj ME (TpIC.full hk c.idx c.cm) tdm *
          checkPassProjector io c.W c.idx c.cm c.ans c.pf) := by
    simp only [P, T, ← mul_kronecker_mul, Matrix.one_mul]
  simp_rw [← he] at hb
  have hbound := hh.trans (add_le_add
    (ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 2⁻¹)) hd)
  simp only [add_assoc] at hbound ⊢
  convert hbound using 1

end Quantum
