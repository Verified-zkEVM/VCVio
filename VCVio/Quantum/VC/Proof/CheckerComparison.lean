/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.CheckerDistance
public import VCVio.Quantum.MatrixMap.Commutant
public import VCVio.Quantum.MatrixMap.Comparison
public import VCVio.Quantum.Pure.Tensor

/-!
# Outcome-preserving checker comparison

Measured extraction fibres retain each randomized opening outcome. The partial-table
mismatch vanishes on good databases, and two checked batches add their operator distances.
-/

public section

open scoped ComplexOrder ENNReal Kronecker Matrix.Norms.L2Operator

open Matrix OracleComp
open scoped Kronecker
namespace Quantum
variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (chk : ∀ i, (VC i).NonadaptiveCheck)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))
  (tdBot : ∀ i, Td i) (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]

open scoped Classical in
/-- The accepted partial-database comparison map has no mismatch branch on good databases.
The extraction outcome and every possible randomized opening outcome remain fixed. -/
theorem partialAccepted_mismatch_good_zero (hC : Conditions VC chk ME tdBot Pgood)
    (hk : 1 ≤ k) (c : OpeningClaim k Cm Msg ℓ Pf)
    (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) (pf' : ∀ i, Pf i)
    (hpf : ∀ i, pf' i ∈ support ((VC i).opening (c.ans i).dom (tdm i).2)) :
    (if Function.Injective c.idx ∧
        (∃ i, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) then
      checkPassProjector chk c.Wᶜ c.idx c.cm c.ans c.pf *
        extractProj ME (TpIC.full hk c.idx c.cm) tdm *
          checkPassProjector chk c.W c.idx c.cm c.ans c.pf else 0) *
      diagonal (fun D : Fin k → Database X Y ↦ if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0) = 0 := by
  classical
  split_ifs with hm
  · simp only [checkPassProjector, extractProj, diagonal_mul_diagonal]
    rw [← diagonal_zero]
    congr 1
    funext D
    split_ifs with hb he ha hg <;> simp only [zero_mul, mul_zero, one_mul]
    have hall : ∀ i, (chk i).checkOn (D (c.idx i))
        (c.cm i) (c.ans i) (c.pf i) = true := by
      intro i
      by_cases hi : i ∈ c.W
      · exact ha i hi
      · exact hb i (Finset.mem_compl.mpr hi)
    have hbind := hC.binding hk c.idx hm.1 c.cm c.ans c.pf D hg hall
    rw [he] at hbind
    obtain ⟨i, hi | hi⟩ := hm.2
    · exact (hi (hbind i).1).elim
    · exact (hi ((hbind i).2 _ (hpf i))).elim
  · simp

variable [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z]
  [AddGroup Z] [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
/-- The actual opening/decision instrument has zero mismatch branch after the ideal
partial-database accepted map on good databases. Randomized openings are included. -/
theorem run₂_offlineFinish_partial_good_zero (hC : Conditions VC chk ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) :
    let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
    let K := checkPassProjector chk c.Wᶜ c.idx c.cm c.ans c.pf *
      extractProj ME (TpIC.full hk c.idx c.cm) tdm *
        checkPassProjector chk c.W c.idx c.cm c.ans c.pf *
          diagonal (fun D : Fin k → Database X Y ↦ if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
    (R.run₂ .instruments (offlineFinish VC (Z := Z) hk qs c B
      (true, some tdm, true))).branch true ∘ₗ
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ K) = 0 := by
  classical
  let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
  dsimp only
  ext ρ : 1
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [offlineFinish_accept, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply]
  refine (tsum_congr fun pf' ↦ ?_).trans tsum_zero
  obtain ⟨c₀, hc₀, hz⟩ := exists_branch_run₂_pi_eq_smul R
    (fun i ↦ openAt VC B i (c.ans i).dom (tdm i).2)
    (fun i ↦ support ((VC i).opening (c.ans i).dom (tdm i).2))
    (fun i b ↦ exists_branch_run₂_toQuantumAt_coinImpl_eq_smul _ _ b) pf'
  rw [hc₀, LinearMap.smul_apply, LinearMap.id_apply, QuantumRuntime.run₂_pure]
  by_cases hs : ∃ i, pf' i ∉ support ((VC i).opening (c.ans i).dom (tdm i).2)
  · rw [hz hs, zero_smul, map_zero]
  · by_cases he : (decide (∃ i : Fin k, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) &&
        decide (∑ i, (c.ans i).dom.card ≤ qs) && decide (Function.Injective c.idx)) = true
    · rw [he, SubInstrument.branch_pure_self, LinearMap.id_apply]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he
      have hh := partialAccepted_mismatch_good_zero chk ME tdBot Pgood hC hk c tdm pf'
        (fun i ↦ by by_contra hh; exact hs ⟨i, hh⟩)
      rw [ite_eq_left ⟨he.2, he.1.1⟩] at hh
      rw [hh]
      erw [Matrix.kronecker_zero, MatrixMap.conj_zero, LinearMap.zero_apply, smul_zero]
    · rw [SubInstrument.branch_pure_of_ne (Ne.symm he), LinearMap.zero_apply]
end Quantum

namespace Quantum

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z]
  [DecidableEq Z] [AddGroup Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  [∀ i, DecidableEq (DmOf ℓ Msg Td i)] [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (chk : ∀ i, (VC i).NonadaptiveCheck)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))
  (tdBot : ∀ i, Td i) (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]

/-- The outcome-preserving partial-database mismatch event is bounded by the original
bad-database weight. This includes randomized openings and arbitrary entangled input matrices. -/
theorem offlineFinish_partial_le_bad (hC : Conditions VC chk ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    {ρ : Matrix (B × (Fin k → Database X Y)) (B × (Fin k → Database X Y)) ℂ}
    (hρ : ρ.PosSemidef) :
    let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
    let Pa := checkPassProjector chk c.W c.idx c.cm c.ans c.pf
    let Pb := checkPassProjector chk c.Wᶜ c.idx c.cm c.ans c.pf
    let G := diagonal (fun D : Fin k → Database X Y ↦
      if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
    (∑' tdm, ENNReal.ofReal (((R.run₂ .instruments
      (offlineFinish VC (Z := Z) hk qs c B (true, some tdm, true))).branch true)
        (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
          (Pb * extractProj ME (TpIC.full hk c.idx c.cm) tdm * Pa)) ρ)).trace.re) ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (1 - G)) ρ).trace.re := by
  classical
  let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
  let Pa := checkPassProjector chk c.W c.idx c.cm c.ans c.pf
  let Pb := checkPassProjector chk c.Wᶜ c.idx c.cm c.ans c.pf
  let G := diagonal (fun D : Fin k → Database X Y ↦
    if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
  let Φ := fun tdm ↦ (R.run₂ .instruments
    (offlineFinish VC (Z := Z) hk qs c B (true, some tdm, true))).branch true
  let K := fun (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) ↦ (1 : Matrix B B ℂ) ⊗ₖ
    (Pb * extractProj ME (TpIC.full hk c.idx c.cm) tdm * Pa)
  have hK : MatrixMap.IsCPTNIFamily (fun tdm ↦ MatrixMap.conj (K tdm)) := by
    have he : ∀ tdm, K tdm = diagonal (fun b : B × (Fin k → Database X Y) ↦
        if ((∀ i ∈ c.Wᶜ, (chk i).checkOn (b.2 (c.idx i))
            (c.cm i) (c.ans i) (c.pf i) = true) ∧
          (∀ i ∈ c.W, (chk i).checkOn (b.2 (c.idx i))
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
        (∀ i ∈ c.Wᶜ, (chk i).checkOn (b.2 (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true)
        (ME.extract (TpIC.full hk c.idx c.cm) b.2 = tdm)
        (∀ i ∈ c.W, (chk i).checkOn (b.2 (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true)
        using 1
      congr! 4
    simp_rw [he]
    convert MatrixMap.accepted_label_isCPTNIFamily
      (ι := TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk))
      (fun b : B × (Fin k → Database X Y) ↦
        (∀ i ∈ c.Wᶜ, (chk i).checkOn (b.2 (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true) ∧
        (∀ i ∈ c.W, (chk i).checkOn (b.2 (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true))
      (fun b ↦ ME.extract (TpIC.full hk c.idx c.cm) b.2) using 1
    congr! 6
  have hz (tdm) : Φ tdm ∘ₗ MatrixMap.conj (K tdm * ((1 : Matrix B B ℂ) ⊗ₖ G)) = 0 := by
    dsimp only [K]
    rw [← mul_kronecker_mul, Matrix.one_mul]
    exact run₂_offlineFinish_partial_good_zero chk ME tdBot Pgood hC code hk qs c B tdm
  have hh := MatrixMap.finish_sum_le_complement Φ
    (fun tdm ↦ (R.run₂ .instruments (offlineFinish VC (Z := Z)
      hk qs c B (true, some tdm, true))).isCP_branch true)
    (fun tdm ↦ (R.run₂ .instruments (offlineFinish VC (Z := Z)
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
theorem offlineFinish_le_bad_add_distance (hC : Conditions VC chk ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    {ρ : Matrix (B × (Fin k → Database X Y)) (B × (Fin k → Database X Y)) ℂ}
    (hρ : ρ.PosSemidef) :
    let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
    let P := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector chk W c.idx c.cm c.ans c.pf
    let Q := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ filledBatch chk W c
    let G := diagonal (fun D : Fin k → Database X Y ↦
      if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
    (∑' tdm, ENNReal.ofReal (((R.run₂ .instruments
      (offlineFinish VC (Z := Z) hk qs c B (true, some tdm, true))).branch true)
        (MatrixMap.conj (Q c.Wᶜ * ((1 : Matrix B B ℂ) ⊗ₖ
          extractProj ME (TpIC.full hk c.idx c.cm) tdm) * Q c.W) ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (1 - G)) ρ).trace.re ^
          (2⁻¹ : ℝ) +
        (ENNReal.ofReal (‖Q c.W - P c.W‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (‖Q c.Wᶜ - P c.Wᶜ‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  classical
  let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
  let P := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector chk W c.idx c.cm c.ans c.pf
  let Q := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ filledBatch chk W c
  let T := fun (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) ↦
    (1 : Matrix B B ℂ) ⊗ₖ extractProj ME (TpIC.full hk c.idx c.cm) tdm
  let Φ := fun tdm ↦ (R.run₂ .instruments
    (offlineFinish VC (Z := Z) hk qs c B (true, some tdm, true))).branch true
  have hΦ (tdm) : (Φ tdm).IsCP := (R.run₂ .instruments
    (offlineFinish VC (Z := Z) hk qs c B (true, some tdm, true))).isCP_branch true
  have ht (tdm) : (Φ tdm).IsTNI := (R.run₂ .instruments
    (offlineFinish VC (Z := Z) hk qs c B
      (true, some tdm, true))).isCPTNIFamily.isTNI true
  have hT : MatrixMap.IsCPTNIFamily (fun tdm ↦ MatrixMap.conj (T tdm)) :=
    extractProj_isCPTNIFamily ME (TpIC.full hk c.idx c.cm) B
  have hd := MatrixMap.measured_two_batches_distance_le T hT
    (Q c.W) (Q c.Wᶜ) (P c.W) (P c.Wᶜ)
    ((l2_opNorm_one_kronecker_le _).trans (norm_filledBatch_le_one chk c.Wᶜ c))
    ((l2_opNorm_one_kronecker_le _).trans (norm_checkPassProjector_le_one chk c.W c)) hρ
  have hh := MatrixMap.finish_comparison Φ hΦ ht hρ
    (fun tdm ↦ Q c.Wᶜ * T tdm * Q c.W) (fun tdm ↦ P c.Wᶜ * T tdm * P c.W)
  have hb := offlineFinish_partial_le_bad chk ME tdBot Pgood hC code hk qs c B hρ
  have he (tdm) : P c.Wᶜ * T tdm * P c.W = (1 : Matrix B B ℂ) ⊗ₖ
      (checkPassProjector chk c.Wᶜ c.idx c.cm c.ans c.pf *
        extractProj ME (TpIC.full hk c.idx c.cm) tdm *
          checkPassProjector chk c.W c.idx c.cm c.ans c.pf) := by
    simp only [P, T, ← mul_kronecker_mul, Matrix.one_mul]
  simp_rw [← he] at hb
  have hbound := hh.trans (add_le_add
    (ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 2⁻¹)) hd)
  simp only [add_assoc] at hbound ⊢
  convert hbound using 1

end Quantum
