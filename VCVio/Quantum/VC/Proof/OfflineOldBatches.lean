/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.OfflineOldComparison
import all VCVio.Quantum.VC.Proof.CheckerComparison

/-!
# Concrete lists for the two offline checker batches

Well-formed batches have one concatenated list of indexed prescriptions. The list retains
repetitions and conflicts, and its length is the sum of the original check-list lengths.
Malformed batches are handled separately by their zero accepting projector.
-/

public section

open Matrix
open scoped ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace Quantum

variable {k : ℕ} {X Y Msg Cm : Type} [DecidableEq Y] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).CheckIOForm)

/-- Concatenation of the indexed prescriptions of a batch, in increasing position order.
Malformed component lists are empty here; the identification lemmas require well-formedness. -/
@[expose]
noncomputable def batchIO (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    List ((Fin k × X) × Y) :=
  (List.finRange k).flatMap fun i ↦ if i ∈ W then
    (((io i).outputIO (c.cm i) (c.ans i) (c.pf i)).getD []).map
      (fun p ↦ ((c.idx i, p.1), p.2)) else []

/-- The concatenated list preserves the exact sum of component query counts. -/
theorem length_batchIO (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    (batchIO io W c).length =
      ∑ i ∈ W, (((io i).outputIO (c.cm i) (c.ans i) (c.pf i)).getD []).length := by
  simp only [batchIO, List.length_flatMap, ← Fin.sum_univ_def, apply_ite List.length,
    List.length_map, List.length_nil, Finset.sum_ite_mem, Finset.univ_inter]

/-- Membership in the concatenated batch retains the originating claim position. -/
theorem mem_batchIO (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf)
    (p : (Fin k × X) × Y) :
    p ∈ batchIO io W c ↔ ∃ i ∈ W, ∃ z ∈
      ((io i).outputIO (c.cm i) (c.ans i) (c.pf i)).getD [],
        ((c.idx i, z.1), z.2) = p := by
  simp only [batchIO, List.mem_flatMap, List.mem_finRange, true_and]
  refine exists_congr fun i ↦ ?_
  split_ifs with h <;> simp [h]

/-- A well-formed batch is exactly the consistency predicate of its concatenated list. -/
theorem checkOn_batchIO (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf)
    (hform : ∀ i ∈ W, ((io i).outputIO (c.cm i) (c.ans i) (c.pf i)).isSome)
    (D : Fin k → Database X Y) :
    (∀ i ∈ W, (io i).checkOn (D (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true) ↔
      ∀ p ∈ batchIO io W c, D p.1.1 p.1.2 = some p.2 := by
  have hc (i : Fin k) (hi : i ∈ W) :
      (io i).checkOn (D (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true ↔
        ∀ p ∈ ((io i).outputIO (c.cm i) (c.ans i) (c.pf i)).getD [],
          D (c.idx i) p.1 = some p.2 := by
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp (hform i hi)
    simp [VectorCommitment.CheckIOForm.checkOn, hL, checkIOOn_eq_true_iff]
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
    (hform : ∀ i ∈ W, ((io i).outputIO (c.cm i) (c.ans i) (c.pf i)).isSome) :
    checkPassProjector io W c.idx c.cm c.ans c.pf =
      CompressedReplay.partialCheck (batchIO io W c) := by
  unfold checkPassProjector CompressedReplay.partialCheck
  congr 1
  funext D
  simp only [checkOn_batchIO io W c hform D]

variable [AddCommGroup Y]

/-- Identification of the actual old-oracle batch with its concrete indexed IO projector. -/
theorem actualBatch_eq_actualCheck (W : Finset (Fin k))
    (c : OpeningClaim k Cm Msg ℓ Pf)
    (hform : ∀ i ∈ W, ((io i).outputIO (c.cm i) (c.ans i) (c.pf i)).isSome) :
    actualBatch io W c = CompressedReplay.actualCheck (batchIO io W c) := by
  unfold actualBatch CompressedReplay.actualCheck
  congr 3
  funext D
  simp only [checkOn_batchIO io W c hform (fun j x ↦ some ((D j).lookup x)),
    Option.some.injEq]

/-- A malformed component makes both the partial and the actual batch reject. -/
theorem batch_eq_zero_of_malformed (W : Finset (Fin k))
    (c : OpeningClaim k Cm Msg ℓ Pf) (i : Fin k) (hi : i ∈ W)
    (hbad : (io i).outputIO (c.cm i) (c.ans i) (c.pf i) = none) :
    checkPassProjector io W c.idx c.cm c.ans c.pf = 0 ∧ actualBatch io W c = 0 := by
  have hn (D : Fin k → Database X Y) :
      ¬ ∀ j ∈ W, (io j).checkOn (D (c.idx j)) (c.cm j) (c.ans j) (c.pf j) = true := by
    intro h
    have hh := h i hi
    simp [VectorCommitment.CheckIOForm.checkOn, hbad] at hh
  constructor
  · simp [checkPassProjector, hn]
  · have ha (D : Fin k → Database X Y) := hn (fun j x ↦ some ((D j).lookup x))
    simp only [actualBatch, ha, ite_false, diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]

/-- The filled-cell comparison projector of a batch. -/
@[expose]
noncomputable def filledBatch (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y * checkPassProjector io W c.idx c.cm c.ans c.pf *
    compressDatabases k X Y

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
  by_cases hf : ∀ i ∈ W, ((io i).outputIO (c.cm i) (c.ans i) (c.pf i)).isSome
  · have he : filledBatch io W c = CompressedReplay.filledCheck (batchIO io W c) := by
      rw [filledBatch, checkPassProjector_eq_partialCheck io W c hf]
      rfl
    rw [he, checkPassProjector_eq_partialCheck io W c hf]
    apply (CompressedReplay.filled_partial_distance _).trans
    apply Real.sqrt_le_sqrt
    have hN : (Fintype.card Y : ℝ)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)
    have hb := one_add_mul_le_pow (a := -(Fintype.card Y : ℝ)⁻¹)
      (by linarith : (-2 : ℝ) ≤ -(Fintype.card Y : ℝ)⁻¹)
      (2 * (ioCells (batchIO io W c)).card)
    have hc : ((ioCells (batchIO io W c)).card : ℝ) ≤ (batchIO io W c).length :=
      Nat.cast_le.mpr (card_ioCells_le_length _)
    simp only [Nat.cast_mul, Nat.cast_ofNat, ← sub_eq_add_neg] at hb
    have hn : 0 ≤ (Fintype.card Y : ℝ)⁻¹ := by positivity
    rw [div_eq_mul_inv]
    nlinarith
  · obtain ⟨i, hn⟩ := not_forall.mp hf
    obtain ⟨hi, hn⟩ := not_imp.mp hn
    have hz : (io i).outputIO (c.cm i) (c.ans i) (c.pf i) = none := by
      cases h : (io i).outputIO (c.cm i) (c.ans i) (c.pf i) <;> simp_all
    have hp := (batch_eq_zero_of_malformed io W c i hi hz).1
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
  exact (MatrixMap.norm_one_kronecker_le _).trans (filledBatch_partial_distance io W c)

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

/-- Conjugated conjunctions over complementary position batches multiply to the full batch. -/
theorem conjugated_batches_compl {S : Type*} [Fintype S] [DecidableEq S]
    (C : Matrix S S ℂ) (hC : C * C = 1) (p : Fin k → S → Prop)
    [∀ i s, Decidable (p i s)] (W : Finset (Fin k)) :
    (C * diagonal (fun s ↦ if ∀ i ∈ W, p i s then (1 : ℂ) else 0) * C) *
      (C * diagonal (fun s ↦ if ∀ i ∈ Wᶜ, p i s then (1 : ℂ) else 0) * C) =
        C * diagonal (fun s ↦ if ∀ i, p i s then (1 : ℂ) else 0) * C := by
  rw [CompressedReplay.conjugate_mul C hC, diagonal_ite_mul_diagonal_ite]
  congr 3
  funext s
  have he : ((∀ i ∈ W, p i s) ∧ ∀ i ∈ Wᶜ, p i s) ↔ ∀ i, p i s := by
    constructor
    · intro h i
      by_cases hi : i ∈ W
      · exact h.1 i hi
      · exact h.2 i (Finset.mem_compl.mpr hi)
    · intro h
      exact ⟨fun i _ ↦ h i, fun i _ ↦ h i⟩
  simp only [he]

/-- Actual complementary checker batches multiply to the actual full batch. -/
theorem actualBatch_mul_compl (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    actualBatch io W c * actualBatch io Wᶜ c = actualBatch io Finset.univ c := by
  unfold actualBatch
  have hh := conjugated_batches_compl (compressDatabases k X Y)
    (compressDatabases_mul_self k X Y)
    (fun i D ↦ (io i).checkOn (fun x ↦ some ((D (c.idx i)).lookup x))
      (c.cm i) (c.ans i) (c.pf i) = true) W
  simpa only [Finset.mem_univ, forall_const] using hh

/-- Filled complementary checker batches multiply to the filled full batch. -/
theorem filledBatch_mul_compl (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    filledBatch io W c * filledBatch io Wᶜ c = filledBatch io Finset.univ c := by
  unfold filledBatch checkPassProjector
  have hh := conjugated_batches_compl (compressDatabases k X Y)
    (compressDatabases_mul_self k X Y)
    (fun i D ↦ (io i).checkOn (D (c.idx i)) (c.cm i) (c.ans i) (c.pf i) = true) W
  simpa only [Finset.mem_univ, forall_const] using hh

/-- The full actual-to-filled batch difference is bounded by the original invalid Gram matrix,
including malformed components. -/
theorem actualBatch_sub_filledBatch_gram_le (c : OpeningClaim k Cm Msg ℓ Pf) :
    ((CompressedReplay.invalidStack (k := k) (X := X) (Y := Y))ᴴ *
      CompressedReplay.invalidStack -
      (actualBatch io Finset.univ c - filledBatch io Finset.univ c)ᴴ *
        (actualBatch io Finset.univ c - filledBatch io Finset.univ c)).PosSemidef := by
  classical
  by_cases hf : ∀ i ∈ Finset.univ,
      ((io i).outputIO (c.cm i) (c.ans i) (c.pf i)).isSome
  · rw [actualBatch_eq_actualCheck io _ c hf, filledBatch,
      checkPassProjector_eq_partialCheck io _ c hf]
    exact CompressedReplay.actual_sub_filled_gram_le_invalidStack (batchIO io Finset.univ c)
  · obtain ⟨i, hn⟩ := not_forall.mp hf
    obtain ⟨hi, hn⟩ := not_imp.mp hn
    have hz : (io i).outputIO (c.cm i) (c.ans i) (c.pf i) = none := by
      cases h : (io i).outputIO (c.cm i) (c.ans i) (c.pf i) <;> simp_all
    obtain ⟨hp, ha⟩ := batch_eq_zero_of_malformed io Finset.univ c i hi hz
    rw [ha, filledBatch, hp, Matrix.mul_zero, Matrix.zero_mul, sub_zero,
      conjTranspose_zero, Matrix.zero_mul, sub_zero]
    exact posSemidef_conjTranspose_mul_self _

end Quantum
