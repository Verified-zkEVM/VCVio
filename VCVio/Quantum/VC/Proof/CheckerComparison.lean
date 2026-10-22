/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.CheckerDistance
public import VCVio.Quantum.MatrixMap.Commutant

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
  (io : ∀ i, (VC i).NonadaptiveCheck)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))
  (tdBot : ∀ i, Td i) (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]

open scoped Classical in
/-- The accepted partial-database comparison map has no mismatch branch on good databases.
The extraction outcome and every possible randomized opening outcome remain fixed. -/
theorem partialAccepted_mismatch_good_zero (hC : Conditions VC io ME tdBot Pgood)
    (hk : 1 ≤ k) (c : OpeningClaim k Cm Msg ℓ Pf)
    (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) (pf' : ∀ i, Pf i)
    (hpf : ∀ i, pf' i ∈ support ((VC i).opening (c.ans i).dom (tdm i).2)) :
    (if Function.Injective c.idx ∧
        (∃ i, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) then
      checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf *
        extractProj ME (TpIC.full hk c.idx c.cm) tdm *
          checkPassProjector io c.W c.idx c.cm c.ans c.pf else 0) *
      diagonal (fun D : Fin k → Database X Y ↦ if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0) = 0 := by
  classical
  split_ifs with hm
  · simp only [checkPassProjector, extractProj, diagonal_mul_diagonal]
    rw [← diagonal_zero]
    congr 1
    funext D
    split_ifs with hb he ha hg <;> simp only [zero_mul, mul_zero, one_mul]
    have hall : ∀ i, (io i).checkOn (D (c.idx i))
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
theorem run₂_offlineFinish_partial_good_zero (hC : Conditions VC io ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) :
    let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
    let K := checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf *
      extractProj ME (TpIC.full hk c.idx c.cm) tdm *
        checkPassProjector io c.W c.idx c.cm c.ans c.pf *
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
      have hh := partialAccepted_mismatch_good_zero io ME tdBot Pgood hC hk c tdm pf'
        (fun i ↦ by by_contra hh; exact hs ⟨i, hh⟩)
      rw [ite_eq_left ⟨he.2, he.1.1⟩] at hh
      rw [hh]
      erw [Matrix.kronecker_zero, MatrixMap.conj_zero, LinearMap.zero_apply, smul_zero]
    · rw [SubInstrument.branch_pure_of_ne (Ne.symm he), LinearMap.zero_apply]
end Quantum


namespace Quantum.MatrixMap

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- A completely positive trace-nonincreasing finishing map preserves the square-root triangle
inequality for two preceding Kraus operators. -/
theorem IsCP.finish_triangle {Φ : MatrixMap B C} (hΦ : Φ.IsCP) (hT : Φ.IsTNI)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) (K L : Matrix B A ℂ) :
    ENNReal.ofReal (Φ (conj (K + L) ρ)).trace.re ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (Φ (conj K ρ)).trace.re ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (Φ (conj L ρ)).trace.re ^ (2⁻¹ : ℝ) := by
  classical
  obtain ⟨S, rfl, _⟩ := hΦ.exists_stinespring_of_isTNI hT
  simp only [LinearMap.comp_apply, trace_traceRight]
  simp only [← LinearMap.comp_apply, ← conj_mul]
  rw [Matrix.mul_add]
  exact ofReal_trace_conj_add_rpow_le hρ _ _

/-- Replacing preceding Kraus operators adds their difference before taking the final square.
The finishing map can depend on the measured classical outcome. -/
theorem finish_comparison {ι : Type*} (Φ : ι → MatrixMap B C)
    (hΦ : ∀ i, (Φ i).IsCP) (hT : ∀ i, (Φ i).IsTNI)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) (K L : ι → Matrix B A ℂ) :
    (∑' i, ENNReal.ofReal (Φ i (conj (K i) ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' i, ENNReal.ofReal (Φ i (conj (L i) ρ)).trace.re) ^ (2⁻¹ : ℝ) +
        (∑' i, ENNReal.ofReal (conj (K i - L i) ρ).trace.re) ^ (2⁻¹ : ℝ) := by
  apply rpow_inv_two_tsum_le_of_le_add
  intro i
  have hh := (hΦ i).finish_triangle (hT i) hρ (L i) (K i - L i)
  rw [show L i + (K i - L i) = K i by abel] at hh
  apply hh.trans
  apply add_le_add le_rfl
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
    (hT i _ ((isCP_conj (K i - L i)).posSemidef hρ))) (by norm_num)

/-- A finishing branch that vanishes on a subspace is bounded by its action on the
complement. This retains coherent cross terms until the square-root triangle inequality. -/
theorem IsCP.finish_le_complement [DecidableEq A] {Φ : MatrixMap B C}
    (hΦ : Φ.IsCP) (hT : Φ.IsTNI) (K : Matrix B A ℂ) (G : Matrix A A ℂ)
    (hzero : Φ ∘ₗ conj (K * G) = 0) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (Φ (conj K ρ)).trace.re ≤
      ENNReal.ofReal (Φ (conj K (conj (1 - G) ρ))).trace.re := by
  have h := hΦ.finish_triangle hT hρ (K * (1 - G)) (K * G)
  have he : K * (1 - G) + K * G = K := by
    simp only [Matrix.mul_sub, Matrix.mul_one, sub_add_cancel]
  rw [he] at h
  have hz := LinearMap.congr_fun hzero ρ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rw [hz, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), add_zero] at h
  rw [conj_mul, LinearMap.comp_apply] at h
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2⁻¹)).mp h

/-- An outcome-dependent family of finishing branches supported on the bad subspace has total
weight bounded by the original bad-subspace weight. No post-check population bound is used. -/
theorem finish_sum_le_complement [DecidableEq A] {ι : Type*}
    (Φ : ι → MatrixMap B C) (hΦ : ∀ i, (Φ i).IsCP) (hT : ∀ i, (Φ i).IsTNI)
    (K : ι → Matrix B A ℂ) (hK : IsCPTNIFamily (fun i ↦ conj (K i)))
    (G : Matrix A A ℂ) (hzero : ∀ i, Φ i ∘ₗ conj (K i * G) = 0)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∑' i, ENNReal.ofReal (Φ i (conj (K i) ρ)).trace.re ≤
      ENNReal.ofReal (conj (1 - G) ρ).trace.re := by
  calc _ ≤ ∑' i, ENNReal.ofReal (Φ i (conj (K i) (conj (1 - G) ρ))).trace.re :=
          ENNReal.tsum_le_tsum fun i ↦ (hΦ i).finish_le_complement
            (hT i) (K i) G (hzero i) hρ
    _ ≤ ∑' i, ENNReal.ofReal (conj (K i) (conj (1 - G) ρ)).trace.re := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact ENNReal.ofReal_le_ofReal
        (hT i _ ((isCP_conj _).posSemidef ((isCP_conj _).posSemidef hρ)))
    _ ≤ _ := hK.tsum_ofReal_trace_re_le ((isCP_conj _).posSemidef hρ)

/-- A classical predicate followed by a label measurement is a trace-nonincreasing family. -/
theorem accepted_label_isCPTNIFamily [DecidableEq A] {ι : Type*}
    [DecidableEq ι] (p : A → Prop) [DecidablePred p] (β : A → ι) :
    IsCPTNIFamily (fun i ↦ conj (diagonal fun a ↦
      if p a ∧ β a = i then (1 : ℂ) else 0)) := by
  classical
  let K (i : ι) : Matrix A A ℂ := diagonal fun a ↦ if p a ∧ β a = i then 1 else 0
  refine ⟨fun _ ↦ isCP_conj _, fun s ρ hρ ↦ ?_⟩
  have hg : ∑ i ∈ s, (K i)ᴴ * K i =
      diagonal (fun a ↦ if p a ∧ β a ∈ s then (1 : ℂ) else 0) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp only [K, Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal,
        diagonal_apply_eq]
      by_cases hp : p a <;> simp [hp]
    · simp [K, Matrix.sum_apply, diagonal_conjTranspose, diagonal_mul_diagonal, hab]
  have ht : (1 - ∑ i ∈ s, (K i)ᴴ * K i).PosSemidef := by
    rw [hg, ← diagonal_one, diagonal_sub]
    apply PosSemidef.diagonal
    intro a
    by_cases hp : p a ∧ β a ∈ s <;> simp [hp]
  have hh := ht.trace_mul_re_nonneg hρ
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, ← trace_conj_apply] at hh
  exact sub_nonneg.mp hh

/-- Tensoring on the left with a reference identity does not increase the operator norm. -/
theorem norm_one_kronecker_le [DecidableEq A] [DecidableEq B] (M : Matrix A A ℂ) :
    ‖(1 : Matrix B B ℂ) ⊗ₖ M‖ ≤ ‖M‖ := by
  have he : (1 : Matrix B B ℂ) ⊗ₖ M = (M ⊗ₖ (1 : Matrix B B ℂ)).submatrix
      (Equiv.prodComm B A) (Equiv.prodComm B A) := by
    ext a b
    simp only [kroneckerMap_apply, submatrix_apply, Equiv.prodComm_apply]
    exact mul_comm _ _
  rw [he, l2_opNorm_submatrix_equiv]
  exact l2_opNorm_kronecker_one_le M

/-- Operator norm bounds for a family measured between two operators. The middle family's
trace bound is used once, so the estimate does not multiply by its number of outcomes. -/
theorem measured_sandwich_weight_le [DecidableEq A] {ι : Type*}
    (P : ι → Matrix A A ℂ) (hP : IsCPTNIFamily (fun i ↦ conj (P i)))
    (L R : Matrix A A ℂ) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (∑' i, ENNReal.ofReal (conj (L * P i * R) ρ).trace.re) ≤
      ENNReal.ofReal (‖L‖ ^ 2) * ENNReal.ofReal (conj R ρ).trace.re := by
  calc _ ≤ ∑' i, ENNReal.ofReal (‖L‖ ^ 2) *
      ENNReal.ofReal (conj (P i) (conj R ρ)).trace.re := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [Matrix.mul_assoc, conj_mul, LinearMap.comp_apply, conj_mul,
          LinearMap.comp_apply, ← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (re_trace_conj_le L
          ((isCP_conj _).posSemidef ((isCP_conj _).posSemidef hρ)))
    _ = ENNReal.ofReal (‖L‖ ^ 2) *
        ∑' i, ENNReal.ofReal (conj (P i) (conj R ρ)).trace.re := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul_right (hP.tsum_ofReal_trace_re_le ((isCP_conj _).posSemidef hρ)) _

/-- The two checker replacements are compared while every intermediate measurement outcome
is retained. Their amplitudes add, with the input trace retained for subsequent leaf sums. -/
theorem measured_two_batches_distance_le [DecidableEq A] {ι : Type*}
    (P : ι → Matrix A A ℂ) (hP : IsCPTNIFamily (fun i ↦ conj (P i)))
    (Qa Qb Pa Pb : Matrix A A ℂ) (hQb : ‖Qb‖ ≤ 1) (hPa : ‖Pa‖ ≤ 1)
    {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    (∑' i, ENNReal.ofReal (conj (Qb * P i * Qa - Pb * P i * Pa) ρ).trace.re) ^
        (2⁻¹ : ℝ) ≤
      (ENNReal.ofReal (‖Qa - Pa‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (‖Qb - Pb‖ ^ 2) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
  have htrace (M : Matrix A A ℂ) : ENNReal.ofReal (conj M ρ).trace.re ≤
      ENNReal.ofReal (‖M‖ ^ 2) * ENNReal.ofReal ρ.trace.re := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (re_trace_conj_le M hρ)
  have hsq {M : Matrix A A ℂ} (hM : ‖M‖ ≤ 1) : ENNReal.ofReal (‖M‖ ^ 2) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    nlinarith [norm_nonneg M]
  have htriangle := rpow_inv_two_tsum_le_of_le_add (t := fun i ↦
    ENNReal.ofReal (conj (Qb * P i * Qa - Pb * P i * Pa) ρ).trace.re)
    (a := fun i ↦ ENNReal.ofReal (conj (Qb * P i * (Qa - Pa)) ρ).trace.re)
    (b := fun i ↦ ENNReal.ofReal (conj ((Qb - Pb) * P i * Pa) ρ).trace.re) (fun i ↦ ?_)
  · apply htriangle.trans
    apply add_le_add <;> apply ENNReal.rpow_le_rpow _ (by norm_num)
    · exact (measured_sandwich_weight_le P hP Qb (Qa - Pa) hρ).trans
        ((mul_le_of_le_one_left (by positivity) (hsq hQb)).trans (htrace _))
    · exact (measured_sandwich_weight_le P hP (Qb - Pb) Pa hρ).trans
        (mul_le_mul_right ((htrace Pa).trans
          (mul_le_of_le_one_left (by positivity) (hsq hPa))) _)
  · have he : Qb * P i * Qa - Pb * P i * Pa =
        Qb * P i * (Qa - Pa) + (Qb - Pb) * P i * Pa := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [he]
    exact ofReal_trace_conj_add_rpow_le hρ _ _

/-- Two checker replacements across a coherent contraction add their operator errors.
The intermediate response register is retained, so the estimate precedes its measurement. -/
theorem two_batches_distance_le [DecidableEq A]
    (Qa Qb Pa Pb U : Matrix A A ℂ) (hQ : ‖Qb‖ ≤ 1) (hP : ‖Pa‖ ≤ 1) (hU : ‖U‖ ≤ 1) :
    ‖Qb * U * Qa - Pb * U * Pa‖ ≤ ‖Qa - Pa‖ + ‖Qb - Pb‖ := by
  have he : Qb * U * Qa - Pb * U * Pa =
      Qb * U * (Qa - Pa) + (Qb - Pb) * U * Pa := by
    simp only [mul_sub, sub_mul]
    abel
  rw [he]
  calc _ ≤ ‖Qb * U * (Qa - Pa)‖ + ‖(Qb - Pb) * U * Pa‖ := norm_add_le _ _
    _ ≤ (‖Qb‖ * ‖U‖) * ‖Qa - Pa‖ + (‖Qb - Pb‖ * ‖U‖) * ‖Pa‖ := by
      apply add_le_add
      · exact (l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
      · exact (l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * 1) * ‖Qa - Pa‖ + (‖Qb - Pb‖ * 1) * 1 := by gcongr
    _ = _ := by simp

end Quantum.MatrixMap

namespace Quantum

variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z]
  [DecidableEq Z] [AddGroup Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  [∀ i, DecidableEq (DmOf ℓ Msg Td i)] [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).NonadaptiveCheck)
  (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (Fin k → Database X Y))
  (tdBot : ∀ i, Td i) (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]

/-- The outcome-preserving partial-database mismatch event is bounded by the original
bad-database weight. This includes randomized openings and arbitrary entangled input matrices. -/
theorem offlineFinish_partial_le_bad (hC : Conditions VC io ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    {ρ : Matrix (B × (Fin k → Database X Y)) (B × (Fin k → Database X Y)) ℂ}
    (hρ : ρ.PosSemidef) :
    let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
    let Pa := checkPassProjector io c.W c.idx c.cm c.ans c.pf
    let Pb := checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf
    let G := diagonal (fun D : Fin k → Database X Y ↦
      if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
    (∑' tdm, ENNReal.ofReal (((R.run₂ .instruments
      (offlineFinish VC (Z := Z) hk qs c B (true, some tdm, true))).branch true)
        (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
          (Pb * extractProj ME (TpIC.full hk c.idx c.cm) tdm * Pa)) ρ)).trace.re) ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ (1 - G)) ρ).trace.re := by
  classical
  let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
  let Pa := checkPassProjector io c.W c.idx c.cm c.ans c.pf
  let Pb := checkPassProjector io c.Wᶜ c.idx c.cm c.ans c.pf
  let G := diagonal (fun D : Fin k → Database X Y ↦
    if ∀ i, D i ∈ Pgood then (1 : ℂ) else 0)
  let Φ := fun tdm ↦ (R.run₂ .instruments
    (offlineFinish VC (Z := Z) hk qs c B (true, some tdm, true))).branch true
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
theorem offlineFinish_le_bad_add_distance (hC : Conditions VC io ME tdBot Pgood)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (hk : 1 ≤ k) (qs : ℕ)
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    {ρ : Matrix (B × (Fin k → Database X Y)) (B × (Fin k → Database X Y)) ℂ}
    (hρ : ρ.PosSemidef) :
    let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
    let P := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf
    let Q := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c
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
  let P := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf
  let Q := fun W ↦ (1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c
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
