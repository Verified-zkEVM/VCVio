/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.Proof.Extraction
public import VCVio.Quantum.Oracle.Compressed.Consistency

/-!
# Distances between checked and partial-table projectors

Flattening the oracle index and address identifies the family checker with the consistency
projector. Its distance depends on the number of distinct prescribed cells.
-/

public section

open Matrix
open scoped Matrix.Norms.L2Operator Kronecker

namespace Quantum.CompressedReplay

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]

/-- Flattening the private tables preserves the partial-database predicate. -/
theorem partialCheck_eq_checkProjector (io : List ((Fin k × X) × Y)) :
    partialCheck io = (checkProjector Y io).submatrix
      (Equiv.curry (Fin k) X (Option Y)).symm
      (Equiv.curry (Fin k) X (Option Y)).symm := by
  rw [partialCheck, checkProjector, submatrix_diagonal_equiv]
  congr 1

/-- The filled check is the same compressed consistency projector under table flattening. -/
theorem filledCheck_eq_compressedCheckProjector (io : List ((Fin k × X) × Y)) :
    filledCheck io = (compressedCheckProjector io).submatrix
      (Equiv.curry (Fin k) X (Option Y)).symm
      (Equiv.curry (Fin k) X (Option Y)).symm := by
  rw [filledCheck, compressDatabases_eq_flat, partialCheck_eq_checkProjector,
    compressedCheckProjector, submatrix_mul_equiv, submatrix_mul_equiv]

/-- Exact distinct-cell discrepancy for consistent prescriptions over any number of databases. -/
theorem filled_partial_distance_sq [Nonempty Y] (io : List ((Fin k × X) × Y))
    (h : ConsistentIO io) :
    ‖filledCheck io - partialCheck io‖ ^ 2 =
      1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (ioCells io).card) := by
  rw [filledCheck_eq_compressedCheckProjector, partialCheck_eq_checkProjector]
  change ‖(compressedCheckProjector io - checkProjector Y io).submatrix
    (Equiv.curry (Fin k) X (Option Y)).symm
    (Equiv.curry (Fin k) X (Option Y)).symm‖ ^ 2 = _
  rw [l2_opNorm_submatrix_equiv]
  exact l2_opNorm_compressedCheckProjector_sub_sq h

/-- The filled and partial checkers both vanish for conflicting prescriptions. -/
theorem filled_partial_eq_zero_of_conflict (io : List ((Fin k × X) × Y))
    (h : ¬ ConsistentIO io) : filledCheck io = 0 ∧ partialCheck io = 0 := by
  rw [filledCheck_eq_compressedCheckProjector, partialCheck_eq_checkProjector,
    compressedCheckProjector_eq_zero_of_not_consistentIO h,
    checkProjector_eq_zero_of_not_consistentIO h]
  simp

/-- The filled versus partial checker distance is at most `δN` of the number of distinct cells,
including conflicting prescriptions. Repeated equal prescriptions incur no additional cost. -/
theorem filled_partial_distance [Nonempty Y] (io : List ((Fin k × X) × Y)) :
    ‖filledCheck io - partialCheck io‖ ≤
      Real.sqrt (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (ioCells io).card)) := by
  by_cases h : ConsistentIO io
  · rw [← filled_partial_distance_sq io h, Real.sqrt_sq (norm_nonneg _)]
  · obtain ⟨hq, hp⟩ := filled_partial_eq_zero_of_conflict io h
    rw [hq, hp, sub_zero, norm_zero]
    exact Real.sqrt_nonneg _


/-- The raw list length bounds the discrepancy even when prescriptions conflict. -/
theorem filled_partial_distance_le_sqrt [Nonempty Y] (io : List ((Fin k × X) × Y)) :
    ‖filledCheck io - partialCheck io‖ ≤
      Real.sqrt (2 * io.length / (Fintype.card Y : ℝ)) := by
  rw [filledCheck_eq_compressedCheckProjector, partialCheck_eq_checkProjector]
  change ‖(compressedCheckProjector io - checkProjector Y io).submatrix
    (Equiv.curry (Fin k) X (Option Y)).symm
    (Equiv.curry (Fin k) X (Option Y)).symm‖ ≤ _
  rw [l2_opNorm_submatrix_equiv]
  apply Real.le_sqrt_of_sq_le
  exact (l2_opNorm_compressedCheckProjector_sub_sq_le io).trans (by
    gcongr
    exact_mod_cast card_ioCells_le_length io)

/-- Two lists around any contraction have discrepancy at most twice the square root
of their total raw query count divided by the alphabet size. -/
theorem two_list_distance [Nonempty Y]
    (L₀ L₁ : List ((Fin k × X) × Y)) (q : ℕ) (hq : L₀.length + L₁.length ≤ q)
    (U : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ) (hU : ‖U‖ ≤ 1) :
    ‖filledCheck L₁ * U * filledCheck L₀ - partialCheck L₁ * U * partialCheck L₀‖ ≤
      2 * Real.sqrt (q / (Fintype.card Y : ℝ)) := by
  have hp (L : List ((Fin k × X) × Y)) : ‖partialCheck L‖ ≤ 1 := by
    rw [partialCheck, l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro D
    split_ifs <;> norm_num
  have hf (L : List ((Fin k × X) × Y)) : ‖filledCheck L‖ ≤ 1 := by
    rw [filledCheck_eq_compressedCheckProjector, l2_opNorm_submatrix_equiv]
    have hC : (compressAll (Fin k × X) Y)ᴴ * compressAll (Fin k × X) Y = 1 := by
      rw [conjTranspose_compressAll, compressAll_mul_self]
    rw [compressedCheckProjector]
    conv_lhs => arg 1; arg 2; rw [← conjTranspose_compressAll (Fin k × X) Y]
    apply (l2_opNorm_mul_mul_conjTranspose_le hC _).trans
    rw [checkProjector, l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro D
    split_ifs <;> norm_num
  have he : filledCheck L₁ * U * filledCheck L₀ - partialCheck L₁ * U * partialCheck L₀ =
      filledCheck L₁ * U * (filledCheck L₀ - partialCheck L₀) +
        (filledCheck L₁ - partialCheck L₁) * U * partialCheck L₀ := by
    noncomm_ring
  have hnorm : ‖filledCheck L₁ * U * filledCheck L₀ -
      partialCheck L₁ * U * partialCheck L₀‖ ≤
        ‖filledCheck L₀ - partialCheck L₀‖ + ‖filledCheck L₁ - partialCheck L₁‖ := by
    rw [he]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_mul_le _ _).trans (by
        have hu := (norm_mul_le (filledCheck L₁) U).trans
          (mul_le_mul (hf _) hU (norm_nonneg _) (by norm_num))
        simpa using mul_le_mul_of_nonneg_right hu (norm_nonneg (filledCheck L₀ - partialCheck L₀)))
    · have hu := norm_mul_le (filledCheck L₁ - partialCheck L₁) U
      exact (norm_mul_le _ _).trans (by
        calc
          _ ≤ (‖filledCheck L₁ - partialCheck L₁‖ * 1) * 1 := by
            apply mul_le_mul (hu.trans (by gcongr)) (hp _)
              (norm_nonneg _) (by positivity)
          _ = _ := by ring)
  have h₀ := filled_partial_distance_le_sqrt L₀
  have h₁ := filled_partial_distance_le_sqrt L₁
  have hs₀ := Real.sq_sqrt (show 0 ≤ 2 * L₀.length / (Fintype.card Y : ℝ) by positivity)
  have hs₁ := Real.sq_sqrt (show 0 ≤ 2 * L₁.length / (Fintype.card Y : ℝ) by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ q / (Fintype.card Y : ℝ) by positivity)
  have hcount : (L₀.length : ℝ) / Fintype.card Y + L₁.length / Fintype.card Y ≤
      q / Fintype.card Y := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hq) (by positivity)
  have hd₀ := (pow_le_pow_left₀ (norm_nonneg _) h₀ 2).trans_eq hs₀
  have hd₁ := (pow_le_pow_left₀ (norm_nonneg _) h₁ 2).trans_eq hs₁
  simp only [mul_div_assoc] at hd₀ hd₁
  nlinarith [sq_nonneg (‖filledCheck L₀ - partialCheck L₀‖ -
    ‖filledCheck L₁ - partialCheck L₁‖), norm_nonneg (filledCheck L₀ - partialCheck L₀),
    norm_nonneg (filledCheck L₁ - partialCheck L₁),
    Real.sqrt_nonneg (q / (Fintype.card Y : ℝ)),
    Real.sqrt_nonneg (2 * L₀.length / (Fintype.card Y : ℝ)),
    Real.sqrt_nonneg (2 * L₁.length / (Fintype.card Y : ℝ))]

end Quantum.CompressedReplay

namespace Quantum

variable {k : ℕ} {X Y Msg Cm : Type} [DecidableEq Y] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).NonadaptiveCheck)

/-- Concatenation of the indexed prescriptions of a batch, in increasing position order.
Malformed component lists are empty here; the identification lemmas require well-formedness. -/
@[expose]
noncomputable def batchIO (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    List ((Fin k × X) × Y) :=
  (List.finRange k).flatMap fun i ↦ if i ∈ W then
    (((io i).pairs (c.cm i) (c.ans i) (c.pf i)).getD []).map
      (fun p ↦ ((c.idx i, p.1), p.2)) else []

/-- The concatenated list preserves the exact sum of component query counts. -/
theorem length_batchIO (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    (batchIO io W c).length =
      ∑ i ∈ W, (((io i).pairs (c.cm i) (c.ans i) (c.pf i)).getD []).length := by
  simp only [batchIO, List.length_flatMap, ← Fin.sum_univ_def, apply_ite List.length,
    List.length_map, List.length_nil, Finset.sum_ite_mem, Finset.univ_inter]

/-- Membership in the concatenated batch retains the originating claim position. -/
theorem mem_batchIO (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf)
    (p : (Fin k × X) × Y) :
    p ∈ batchIO io W c ↔ ∃ i ∈ W, ∃ z ∈
      ((io i).pairs (c.cm i) (c.ans i) (c.pf i)).getD [],
        ((c.idx i, z.1), z.2) = p := by
  simp only [batchIO, List.mem_flatMap, List.mem_finRange, true_and]
  refine exists_congr fun i ↦ ?_
  split_ifs with h <;> simp [h]

/-- A well-formed batch is exactly the consistency predicate of its concatenated list. -/
theorem checkOn_batchIO (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf)
    (hform : ∀ i ∈ W, ((io i).pairs (c.cm i) (c.ans i) (c.pf i)).isSome)
    (D : Fin k → Database X Y) :
    (∀ i ∈ W, (io i).checkOn (D (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true) ↔
      ∀ p ∈ batchIO io W c, D p.1.1 p.1.2 = some p.2 := by
  have hc (i : Fin k) (hi : i ∈ W) :
      (io i).checkOn (D (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true ↔
        ∀ p ∈ ((io i).pairs (c.cm i) (c.ans i) (c.pf i)).getD [],
          D (c.idx i) p.1 = some p.2 := by
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp (hform i hi)
    simp [VectorCommitment.NonadaptiveCheck.checkOn, hL, checkIOOn_eq_true_iff]
  constructor
  · intro h p hp
    obtain ⟨i, hi, z, hz, rfl⟩ := (mem_batchIO io W c p).mp hp
    exact (hc i hi).mp (h i hi) z hz
  · intro h i hi
    apply (hc i hi).mpr
    intro z hz
    exact h _ ((mem_batchIO io W c _).mpr ⟨i, hi, z, hz, rfl⟩)

variable [Fintype X] [DecidableEq X] [Fintype Y]

/-- Identification of the partial-database batch with its concrete indexed IO projector. -/
theorem checkPassProjector_eq_partialCheck (W : Finset (Fin k))
    (c : OpeningClaim k Cm Msg ℓ Pf)
    (hform : ∀ i ∈ W, ((io i).pairs (c.cm i) (c.ans i) (c.pf i)).isSome) :
    checkPassProjector io W c.idx c.cm c.ans c.pf =
      CompressedReplay.partialCheck (batchIO io W c) := by
  unfold checkPassProjector CompressedReplay.partialCheck
  congr 1
  funext D
  simp only [checkOn_batchIO io W c hform D]

omit [DecidableEq X] [Fintype Y] in
/-- A malformed component makes the partial batch reject. -/
theorem checkPassProjector_eq_zero_of_malformed (W : Finset (Fin k))
    (c : OpeningClaim k Cm Msg ℓ Pf) (i : Fin k) (hi : i ∈ W)
    (hbad : (io i).pairs (c.cm i) (c.ans i) (c.pf i) = none) :
    checkPassProjector io W c.idx c.cm c.ans c.pf = 0 := by
  have hn (D : Fin k → Database X Y) :
      ¬ ∀ j ∈ W, (io j).checkOn (D (c.idx j)) (c.cm j) (c.ans j) (c.pf j) = true := by
    intro h
    have hh := h i hi
    simp [VectorCommitment.NonadaptiveCheck.checkOn, hbad] at hh
  simp [checkPassProjector, hn]

variable [AddCommGroup Y]

omit [AddCommGroup Y] in
/-- The partial-database batch is a contraction, including malformed claims. -/
theorem norm_checkPassProjector_le_one (W : Finset (Fin k))
    (c : OpeningClaim k Cm Msg ℓ Pf) :
    ‖checkPassProjector io W c.idx c.cm c.ans c.pf‖ ≤ 1 := by
  rw [checkPassProjector, l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro D
  split_ifs <;> norm_num

/-- The filled-cell batch is a contraction, including malformed claims. -/
theorem norm_filledBatch_le_one (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    ‖filledBatch io W c‖ ≤ 1 := by
  have hC : (compressDatabases k X Y)ᴴ * compressDatabases k X Y = 1 := by
    rw [conjTranspose_compressDatabases, compressDatabases_mul_self]
  unfold filledBatch
  conv_lhs => arg 1; arg 2; rw [← conjTranspose_compressDatabases k X Y]
  exact (l2_opNorm_mul_mul_conjTranspose_le hC _).trans
    (norm_checkPassProjector_le_one io W c)

/-- A batch's filled-to-partial discrepancy is bounded using its original query count.
Malformed batches vanish, and conflicting repeated prescriptions are included. -/
theorem filledBatch_partial_distance (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    ‖filledBatch io W c - checkPassProjector io W c.idx c.cm c.ans c.pf‖ ≤
      Real.sqrt (2 * (batchIO io W c).length / (Fintype.card Y : ℝ)) := by
  classical
  by_cases hf : ∀ i ∈ W, ((io i).pairs (c.cm i) (c.ans i) (c.pf i)).isSome
  · have he : filledBatch io W c = CompressedReplay.filledCheck (batchIO io W c) := by
      rw [filledBatch, checkPassProjector_eq_partialCheck io W c hf]
      rfl
    rw [he, checkPassProjector_eq_partialCheck io W c hf]
    exact CompressedReplay.filled_partial_distance_le_sqrt _
  · obtain ⟨i, hn⟩ := not_forall.mp hf
    obtain ⟨hi, hn⟩ := not_imp.mp hn
    have hz : (io i).pairs (c.cm i) (c.ans i) (c.pf i) = none := by
      cases h : (io i).pairs (c.cm i) (c.ans i) (c.pf i) <;> simp_all
    have hp := checkPassProjector_eq_zero_of_malformed io W c i hi hz
    rw [filledBatch, hp, Matrix.mul_zero, Matrix.zero_mul, sub_zero, norm_zero]
    exact Real.sqrt_nonneg _

/-- The discrepancy bound survives an arbitrary finite entangled reference register. -/
theorem reference_filledBatch_partial_distance (W : Finset (Fin k))
    (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    ‖(1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c -
        (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf‖ ≤
      Real.sqrt (2 * (batchIO io W c).length / (Fintype.card Y : ℝ)) := by
  have he : (1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c -
      (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf =
      (1 : Matrix B B ℂ) ⊗ₖ
        (filledBatch io W c - checkPassProjector io W c.idx c.cm c.ans c.pf) := by
    ext a b
    simp only [Matrix.sub_apply, kroneckerMap_apply, mul_sub]
  rw [he]
  have hswap : ∀ M : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ,
      (1 : Matrix B B ℂ) ⊗ₖ M = (M ⊗ₖ (1 : Matrix B B ℂ)).submatrix
        (Equiv.prodComm B _) (Equiv.prodComm B _) := by
    intro M
    ext a b
    exact mul_comm _ _
  rw [hswap, l2_opNorm_submatrix_equiv]
  exact (l2_opNorm_kronecker_one_le _).trans (filledBatch_partial_distance io W c)

/-- The two batch discrepancy amplitudes cost at most twice the square root of the total
query count divided by the answer alphabet size. Repeated and conflicting cells are included. -/
theorem two_batch_reference_distance_le (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    let Δ := fun W ↦ ‖(1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c -
      (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf‖
    Δ c.W + Δ c.Wᶜ ≤ 2 * Real.sqrt
      (((batchIO io c.W c).length + (batchIO io c.Wᶜ c).length) / (Fintype.card Y : ℝ)) := by
  let Δ := fun W ↦ ‖(1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c -
    (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf‖
  have hsq (W) : Δ W ^ 2 ≤ 2 * (batchIO io W c).length / (Fintype.card Y : ℝ) := by
    have hh := reference_filledBatch_partial_distance io W c B
    have hn : 0 ≤ 2 * (batchIO io W c).length / (Fintype.card Y : ℝ) := by positivity
    have hs := Real.sq_sqrt hn
    change Δ W ≤ _ at hh
    nlinarith [Real.sqrt_nonneg (2 * (batchIO io W c).length / (Fintype.card Y : ℝ)),
      norm_nonneg ((1 : Matrix B B ℂ) ⊗ₖ filledBatch io W c -
        (1 : Matrix B B ℂ) ⊗ₖ checkPassProjector io W c.idx c.cm c.ans c.pf)]
  have h₁ := hsq c.W
  have h₂ := hsq c.Wᶜ
  have hroot := Real.sq_sqrt (show 0 ≤
    (((batchIO io c.W c).length + (batchIO io c.Wᶜ c).length) / (Fintype.card Y : ℝ))
      by positivity)
  have he : 2 * (batchIO io c.W c).length / (Fintype.card Y : ℝ) +
      2 * (batchIO io c.Wᶜ c).length / (Fintype.card Y : ℝ) =
        2 * (((batchIO io c.W c).length + (batchIO io c.Wᶜ c).length) /
          (Fintype.card Y : ℝ)) := by ring
  dsimp only
  change Δ c.W + Δ c.Wᶜ ≤ _
  nlinarith [sq_nonneg (Δ c.W - Δ c.Wᶜ),
    Real.sqrt_nonneg (((batchIO io c.W c).length + (batchIO io c.Wᶜ c).length) /
      (Fintype.card Y : ℝ))]

omit [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y] in
/-- The raw lists in complementary batches are bounded by the total checker budget. -/
theorem length_two_batches_le (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf)
    (hq : ∑ i, (c.ans i).dom.card ≤ qs) :
    (batchIO io c.W c).length + (batchIO io c.Wᶜ c).length ≤ q1 io qs := by
  classical
  rw [length_batchIO, length_batchIO, Finset.sum_add_sum_compl]
  calc
    _ ≤ ∑ i, (io i).qVC (c.ans i).dom.card := by
      apply Finset.sum_le_sum
      intro i _
      cases h : (io i).pairs (c.cm i) (c.ans i) (c.pf i) with
      | none => simp
      | some L => exact (io i).length_le _ _ _ _ h
    _ ≤ q1 io qs := sum_qVC_le_q1 io _ hq

end Quantum
