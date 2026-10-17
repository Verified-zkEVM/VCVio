/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.Repeatability
public import VCVio.Quantum.Oracle.Compressed.CollisionRuntime
public import VCVio.Quantum.MatrixMap.Commutant
import all VCVio.Quantum.VC.Proof.Repeatability
import all VCVio.Quantum.VC.Compressed
import all VCVio.Quantum.Oracle.ClassicalRepeatability

/-!
# The actual checker of the old compressed oracle

The classical checker of ePrint 2025/2166, Definition 8.1, PDF page 52, has an accepting
projector that includes empty sectors for zero answers. The filled checker instead requires
`some y` at every prescribed cell before compression. Their difference is positive and supported
on invalid sectors, as in the repair note FIX (29), (31). The Gram matrix of the difference
is bounded by the sum of the invalid-cell projectors, represented by the rectangular operator
`invalidStack`. These are identities and inequalities on the entire
private space, with no population or reachable-state hypothesis.

The filled versus partial discrepancy uses the exact constant of the bounds note (26),
sharpening ePrint 2025/2166, Lemma 9.5, PDF page 61. Conflicting prescriptions are included.
The local invalid commutator is supported on occupied cells. Its context-dependent Gram
bound sums to `4 * s * a` on population at most `s`, provided at most the fraction `a`
of labels changes in each occupied-cell context. This is the operator estimate in FIX (27).
These operator statements alone do not establish the offline game of Lemma 9.6, PDF page 62.
-/

public section

open Matrix OracleComp
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder

namespace Quantum
namespace ProjectiveClassicalAnswers

variable {P : Type*} {In : P → QReg} {E : EmulatedOracle P In}
  {X Y : Type} [Fintype Y] [DecidableEq Y]
  (H : ProjectiveClassicalAnswers E X Y)

/-- The actual classical calls associated with a projective answer interface. -/
noncomputable def classicalCall (B : QReg) : QueryImpl (X →ₒ Y) (QComp (uSpec P In) B B) :=
  fun x ↦ QComp.callBasis (H.query x).1 B (H.query x).2 (fun o _ ↦ H.read x o)

/-- The accepting branch of the complete checker fold. Calls continue after a failed comparison;
all rejected answer histories have zero contribution to the accepting branch. -/
theorem actual_fold_accept (B : QReg) (io : List (X × Y)) (acc : Bool) :
    (E.toRuntime.run₂ .instruments
      ((io.foldlM checkIOStep acc).toQuantumAt (H.classicalCall B))).branch true =
        if acc then H.transcriptBranch B io else 0 := by
  induction io generalizing acc with
  | nil =>
    rw [List.foldlM_nil, toQuantumAt_pure, QuantumRuntime.run₂_pure]
    cases acc
    · exact SubInstrument.branch_pure_of_ne (by decide)
    · simp
  | cons p io ih =>
    have hp : ((p :: io).foldlM checkIOStep acc).toQuantumAt (H.classicalCall B) =
        (H.classicalCall B p.1).bind fun y ↦
          (io.foldlM checkIOStep (acc && decide (y = p.2))).toQuantumAt
            (H.classicalCall B) := by
      rw [List.foldlM_cons, checkIOStep, bind_assoc]
      simp only [pure_bind]
      exact toQuantumAt_query_bind (H.classicalCall B) p.1 _
    rw [hp, QuantumRuntime.run₂_bind, SubInstrument.branch_bind_apply_univ,
      Finset.sum_eq_single p.2]
    · rw [ih]
      simp only [decide_true, Bool.and_true]
      cases acc
      · simp
      · simp only [↓reduceIte]
        rw [classicalCall, H.branch_eq]
        exact (H.transcriptBranch_cons B p io).symm
    · intro y _ hy
      rw [ih]
      simp [hy]
    · simp

/-- The actual classical `checkIO` accepts on the product of its answer projectors, including
repeated and contradictory prescriptions, on any entangled reference/private input matrix. -/
theorem actual_accept_eq_projectorProduct (B : QReg) (io : List (X × Y)) :
    (E.toRuntime.run₂ .instruments
      ((checkIO io).toQuantumAt (H.classicalCall B))).branch true =
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ H.projector io) := by
  simpa only [checkIO, ↓reduceIte, transcriptBranch] using H.actual_fold_accept B io true

end ProjectiveClassicalAnswers

namespace CompressedReplay

section lookup

variable {k : ℕ} {X Y : Type} [AddCommGroup Y]

private theorem filled_implies_lookup (D : Fin k → Database X Y)
    (io : List ((Fin k × X) × Y)) (h : ∀ p ∈ io, D p.1.1 p.1.2 = some p.2) :
    ∀ p ∈ io, (D p.1.1).lookup p.1.2 = p.2 := by
  intro p hp
  simp [Database.lookup_apply, h p hp]

private theorem lookup_filled_of_valid (D : Fin k → Database X Y)
    (io : List ((Fin k × X) × Y)) (hv : ∀ j x, D j x ≠ none)
    (ha : ∀ p ∈ io, (D p.1.1).lookup p.1.2 = p.2) :
    ∀ p ∈ io, D p.1.1 p.1.2 = some p.2 := by
  intro p hp
  cases he : D p.1.1 p.1.2 with
  | none => exact False.elim (hv _ _ he)
  | some y => simpa [Database.lookup_apply, he] using ha p hp

private theorem indicator_bounds (A Q V : Prop) [Decidable A] [Decidable Q] [Decidable V]
    (hQA : Q → A) (hVAQ : V → A → Q) :
    (0 : ℂ) ≤ (if A then 1 else 0) - (if Q then 1 else 0) ∧
    (0 : ℂ) ≤ 1 - (if V then 1 else 0) -
      ((if A then 1 else 0) - (if Q then 1 else 0)) := by
  by_cases hA : A <;> by_cases hQ : Q <;> by_cases hV : V <;> simp_all

end lookup

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]

/-- The accepting projector of the old oracle's classical checker. Empty cells read zero. -/
noncomputable def actualCheck [AddCommGroup Y] (io : List ((Fin k × X) × Y)) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y *
    diagonal (fun D ↦ if ∀ p ∈ io, (D p.1.1).lookup p.1.2 = p.2 then 1 else 0) *
      compressDatabases k X Y

/-- The partial-database checker on a list spanning several oracle indices. -/
noncomputable def partialCheck (io : List ((Fin k × X) × Y)) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  diagonal fun D ↦ if ∀ p ∈ io, D p.1.1 p.1.2 = some p.2 then 1 else 0

/-- The filled checker is the compressed conjugate of the partial-database checker. -/
noncomputable def filledCheck (io : List ((Fin k × X) × Y)) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y * partialCheck io * compressDatabases k X Y

/-- Validity means every decompressed cell is filled, across all oracle indices. -/
noncomputable def validProjector (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y *
    diagonal (fun D ↦ if ∀ j x, D j x ≠ none then 1 else 0) * compressDatabases k X Y

/-- The product of actual answer projectors is a conjugated lookup predicate. -/
theorem actualCheck_eq_projector [AddCommGroup Y] (io : List ((Fin k × X) × Y)) :
    actualCheck io =
      (projectiveClassicalAnswers (k := k) (X := X) (Y := Y)).projector io := by
  change actualCheck io = (io.map fun p ↦ answer p.1 p.2).prod
  unfold actualCheck
  induction io with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.not_mem_nil, false_imp_iff,
      implies_true, ite_true, diagonal_one, Matrix.mul_one]
    exact compressDatabases_mul_self ..
  | cons p io ih =>
    rw [List.map_cons, List.prod_cons, ← ih, answer,
      conjugate_mul _ (compressDatabases_mul_self k X Y), diagonal_ite_mul_diagonal_ite]
    simp only [List.forall_mem_cons]

/-- In Loewner order, `0 ≤ Acheck - Qcheck ≤ 1 - Kvalid`. Positivity is expressed by
`PosSemidef`, so this statement does not use the entrywise order on matrices. The checked
lists may repeat cells or prescribe conflicting answers. -/
theorem actual_sub_filled_supported_invalid [AddCommGroup Y] (io : List ((Fin k × X) × Y)) :
    (actualCheck io - filledCheck io).PosSemidef ∧
    (1 - validProjector k X Y -
      (actualCheck io - filledCheck io)).PosSemidef := by
  let C := compressDatabases k X Y
  let a (D : Fin k → Database X Y) : ℂ :=
    if ∀ p ∈ io, (D p.1.1).lookup p.1.2 = p.2 then 1 else 0
  let q (D : Fin k → Database X Y) : ℂ :=
    if ∀ p ∈ io, D p.1.1 p.1.2 = some p.2 then 1 else 0
  let v (D : Fin k → Database X Y) : ℂ :=
    if ∀ j x, D j x ≠ none then 1 else 0
  have hlow : (diagonal (fun D ↦ a D - q D)).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro D
    exact (indicator_bounds _ _ _ (filled_implies_lookup D io)
      (lookup_filled_of_valid D io)).1
  have hupp : (diagonal (fun D ↦ 1 - v D - (a D - q D))).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro D
    exact (indicator_bounds _ _ _ (filled_implies_lookup D io)
      (lookup_filled_of_valid D io)).2
  constructor
  · convert hlow.mul_mul_conjTranspose_same C using 1
    simp only [actualCheck, filledCheck, partialCheck, C, a, q,
      conjTranspose_compressDatabases, ← diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
  · convert hupp.mul_mul_conjTranspose_same C using 1
    simp only [actualCheck, filledCheck, partialCheck, validProjector, C, a, q, v,
      conjTranspose_compressDatabases, ← diagonal_sub, diagonal_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, compressDatabases_mul_self]

/-- The actual-versus-filled difference is itself an orthogonal projector. This includes
contradictory lists, for which both accepting projectors vanish. -/
theorem actual_sub_filled_idempotent [AddCommGroup Y] (io : List ((Fin k × X) × Y)) :
    (actualCheck io - filledCheck io) * (actualCheck io - filledCheck io) =
      actualCheck io - filledCheck io := by
  let a (D : Fin k → Database X Y) : ℂ :=
    if ∀ p ∈ io, (D p.1.1).lookup p.1.2 = p.2 then 1 else 0
  let q (D : Fin k → Database X Y) : ℂ :=
    if ∀ p ∈ io, D p.1.1 p.1.2 = some p.2 then 1 else 0
  have hd : (diagonal fun D ↦ a D - q D) * (diagonal fun D ↦ a D - q D) =
      diagonal fun D ↦ a D - q D := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext D
    have h := filled_implies_lookup D io
    dsimp only [a, q]
    split_ifs <;> simp_all
  have he : actualCheck io - filledCheck io =
      compressDatabases k X Y * (diagonal fun D ↦ a D - q D) * compressDatabases k X Y := by
    simp only [actualCheck, filledCheck, partialCheck, a, q, ← diagonal_sub,
      Matrix.mul_sub, Matrix.sub_mul]
  rw [he, conjugate_mul _ (compressDatabases_mul_self k X Y), hd]

/-- The union of invalid cells is bounded by their sum, without a population hypothesis. -/
theorem invalid_union_le_sum [AddCommGroup Y] :
    ((∑ c : Fin k × X, invalid (Y := Y) c) - (1 - validProjector k X Y)).PosSemidef := by
  classical
  let v (D : Fin k → Database X Y) : ℂ := if ∀ j x, D j x ≠ none then 1 else 0
  let r (c : Fin k × X) (D : Fin k → Database X Y) : ℂ :=
    if D c.1 c.2 = none then 1 else 0
  have hd : (diagonal fun D ↦ (∑ c, r c D) - (1 - v D)).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro D
    have hr : ∀ c, (0 : ℂ) ≤ r c D := by intro c; dsimp [r]; split_ifs <;> simp
    by_cases hv : ∀ j x, D j x ≠ none
    · simpa [v, hv] using Finset.sum_nonneg (fun c _ ↦ hr c)
    · obtain ⟨j, x, hx⟩ : ∃ j x, D j x = none := by simpa using hv
      have hsingle := Finset.single_le_sum (fun c _ ↦ hr c) (Finset.mem_univ (j, x))
      apply sub_nonneg.mpr
      simpa [v, hv, r, hx] using hsingle
  convert hd.mul_mul_conjTranspose_same (compressDatabases k X Y) using 1
  simp only [invalid, validProjector, v, r, conjTranspose_compressDatabases,
    ← diagonal_sub, diagonal_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    compressDatabases_mul_self]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum]
  congr 3
  ext a b
  by_cases hab : a = b <;> simp [Matrix.sum_apply, hab]

/-- FIX (29) as a positive-operator inequality: the squared actual-check error is bounded
by the sum of the cellwise invalid projectors. It applies to any input state, before or after
other operations, and does not assert that checking preserves population. -/
theorem actual_sub_filled_gram_le_invalid_sum [AddCommGroup Y]
    (io : List ((Fin k × X) × Y)) :
    ((∑ c : Fin k × X, invalid (Y := Y) c) -
      (actualCheck io - filledCheck io)ᴴ * (actualCheck io - filledCheck io)).PosSemidef := by
  have h := actual_sub_filled_supported_invalid io
  rw [h.1.isHermitian.eq, actual_sub_filled_idempotent]
  have hh := (invalid_union_le_sum (k := k) (X := X) (Y := Y)).add h.2
  convert hh using 1
  abel

/-- Each cellwise invalid-sector operator is an orthogonal projector. -/
theorem invalid_idempotent [AddCommGroup Y] (c : Fin k × X) :
    invalid (Y := Y) c * invalid c = invalid c := by
  rw [invalid, conjugate_mul _ (compressDatabases_mul_self k X Y),
    diagonal_ite_mul_diagonal_ite]
  simp only [and_self]

/-- The cellwise invalid-sector projectors are Hermitian. -/
theorem invalid_hermitian (c : Fin k × X) :
    (invalid (Y := Y) c)ᴴ = invalid c := by
  simp only [invalid, conjTranspose_mul, conjTranspose_compressDatabases,
    conjTranspose_diagonal_ite, Matrix.mul_assoc]

/-- Stack all invalid projectors into a rectangular operator. Its squared norm on a state
is the sum of the cellwise invalid weights, not a union-event probability. -/
noncomputable def invalidStack :
    Matrix ((Fin k × X) × (Fin k → Database X Y)) (Fin k → Database X Y) ℂ :=
  Matrix.of fun a b ↦ invalid a.1 a.2 b

/-- The Gram matrix of the rectangular invalid operator is the sum of invalid projectors. -/
theorem invalidStack_gram [AddCommGroup Y] :
    (invalidStack (k := k) (X := X) (Y := Y))ᴴ * invalidStack =
      ∑ c : Fin k × X, invalid (Y := Y) c := by
  have hs : (invalidStack (k := k) (X := X) (Y := Y))ᴴ * invalidStack =
      ∑ c : Fin k × X, (invalid (Y := Y) c)ᴴ * invalid c := by
    ext D D'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      Fintype.sum_prod_type, invalidStack, Matrix.of_apply]
  simp only [invalid_hermitian, invalid_idempotent] at hs
  exact hs

/-- The rectangular invalid operator bounds the actual checker error in Gram order, as
required by the trace-potential formulation of FIX (29). -/
theorem actual_sub_filled_gram_le_invalidStack [AddCommGroup Y]
    (io : List ((Fin k × X) × Y)) :
    ((invalidStack (k := k) (X := X) (Y := Y))ᴴ * invalidStack -
      (actualCheck io - filledCheck io)ᴴ * (actualCheck io - filledCheck io)).PosSemidef := by
  rw [invalidStack_gram]
  exact actual_sub_filled_gram_le_invalid_sum io

omit [DecidableEq X] in
/-- Flattening oracle indices and addresses preserves the compression matrix. -/
theorem compressDatabases_eq_flat :
    compressDatabases k X Y =
      (compressAll (Fin k × X) Y).submatrix
        (Equiv.curry (Fin k) X (Option Y)).symm
        (Equiv.curry (Fin k) X (Option Y)).symm := by
  ext D D'
  simp only [compressDatabases, compressAll, piKron_apply, submatrix_apply,
    Equiv.curry_symm_apply]
  exact (Fintype.prod_prod_type fun p : Fin k × X ↦
    cellCompress Y (D p.1 p.2) (D' p.1 p.2)).symm

/-- Flattening the private tables preserves the partial-database predicate. -/
theorem partialCheck_eq_flat (io : List ((Fin k × X) × Y)) :
    partialCheck io = (checkProjector Y io).submatrix
      (Equiv.curry (Fin k) X (Option Y)).symm
      (Equiv.curry (Fin k) X (Option Y)).symm := by
  rw [partialCheck, checkProjector, submatrix_diagonal_equiv]
  congr 1
  funext D
  simp only [Function.comp_apply, Equiv.curry_symm_apply, Function.uncurry]
  congr 1

/-- The filled check is the same compressed consistency projector under table flattening. -/
theorem filledCheck_eq_flat (io : List ((Fin k × X) × Y)) :
    filledCheck io = (compressedCheckProjector io).submatrix
      (Equiv.curry (Fin k) X (Option Y)).symm
      (Equiv.curry (Fin k) X (Option Y)).symm := by
  rw [filledCheck, compressDatabases_eq_flat, partialCheck_eq_flat,
    compressedCheckProjector, submatrix_mul_equiv, submatrix_mul_equiv]

/-- Exact distinct-cell discrepancy for consistent prescriptions over any number of databases.
The constant is the bounds note (26), not the larger constant in the paper's Lemma 9.5. -/
theorem filled_partial_distance_sq [Nonempty Y] (io : List ((Fin k × X) × Y))
    (h : ConsistentIO io) :
    ‖filledCheck io - partialCheck io‖ ^ 2 =
      1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (2 * (ioCells io).card) := by
  rw [filledCheck_eq_flat, partialCheck_eq_flat]
  change ‖(compressedCheckProjector io - checkProjector Y io).submatrix
    (Equiv.curry (Fin k) X (Option Y)).symm
    (Equiv.curry (Fin k) X (Option Y)).symm‖ ^ 2 = _
  rw [l2_opNorm_submatrix_equiv]
  exact l2_opNorm_compressedCheckProjector_sub_sq h

/-- The filled and partial checkers both vanish for conflicting prescriptions. -/
theorem filled_partial_eq_zero_of_conflict (io : List ((Fin k × X) × Y))
    (h : ¬ ConsistentIO io) : filledCheck io = 0 ∧ partialCheck io = 0 := by
  rw [filledCheck_eq_flat, partialCheck_eq_flat,
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

end CompressedReplay

/-! ## Local invalid-sector commutators -/

section uniformProjector

variable {Y : Type*} [DecidableEq Y]

private def subsetVector (s : Finset Y) : Y → ℂ := fun y ↦ if y ∈ s then 1 else 0

/-- The orthogonal projector onto the uniform vector on a subset, or zero for the empty subset. -/
noncomputable def uniformSubsetProjector (s : Finset Y) : Matrix Y Y ℂ :=
  (s.card : ℂ)⁻¹ • vecMulVec (subsetVector s) (subsetVector s)

private theorem subsetVector_star (s : Finset Y) : star (subsetVector s) = subsetVector s := by
  ext y
  simp [subsetVector]

/-- The uniform subset projector is Hermitian. -/
theorem uniformSubsetProjector_hermitian (s : Finset Y) :
    (uniformSubsetProjector s)ᴴ = uniformSubsetProjector s := by
  simp [uniformSubsetProjector, subsetVector_star]

variable [Fintype Y]

private theorem subsetVector_dot (s t : Finset Y) :
    subsetVector s ⬝ᵥ subsetVector t = ((s ∩ t).card : ℂ) := by
  classical
  calc
    _ = ∑ y : Y, if y ∈ s ∩ t then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [subsetVector, Finset.mem_inter]
      split_ifs <;> simp_all
    _ = _ := by
      rw [Finset.sum_boole]
      congr 2
      ext y
      simp

/-- Multiplication of two uniform subset projectors. -/
private theorem uniformSubsetProjector_mul (s t : Finset Y) :
    uniformSubsetProjector s * uniformSubsetProjector t =
      ((s.card : ℂ)⁻¹ * (t.card : ℂ)⁻¹ * (s ∩ t).card) •
        vecMulVec (subsetVector s) (subsetVector t) := by
  simp only [uniformSubsetProjector, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec,
    subsetVector_dot, vecMulVec_smul, smul_smul]
  congr 1
  ring

/-- Uniform subset projectors are idempotent, including the empty subset. -/
theorem uniformSubsetProjector_idempotent (s : Finset Y) :
    uniformSubsetProjector s * uniformSubsetProjector s = uniformSubsetProjector s := by
  rw [uniformSubsetProjector_mul, Finset.inter_self, uniformSubsetProjector]
  congr 1
  by_cases hs : (s.card : ℂ) = 0
  · simp [hs]
  · field_simp

/-- Sandwiching a uniform subset projector by the whole-space uniform projector. -/
theorem uniformSubsetProjector_sandwich_univ (s : Finset Y) :
    uniformSubsetProjector Finset.univ * uniformSubsetProjector s *
        uniformSubsetProjector Finset.univ =
      ((s.card : ℂ) / Fintype.card Y) • uniformSubsetProjector Finset.univ := by
  simp only [uniformSubsetProjector, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, vecMulVec_smul, subsetVector_dot, Finset.univ_inter,
    Finset.inter_univ, smul_smul, Finset.card_univ]
  congr 1
  by_cases hs : (s.card : ℂ) = 0
  · simp [hs]
  · field_simp

/-- Sandwiching the whole-space uniform projector by a subset projector. -/
theorem uniformSubsetProjector_univ_sandwich (s : Finset Y) :
    uniformSubsetProjector s * uniformSubsetProjector Finset.univ * uniformSubsetProjector s =
      ((s.card : ℂ) / Fintype.card Y) • uniformSubsetProjector s := by
  simp only [uniformSubsetProjector, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, vecMulVec_smul, subsetVector_dot, Finset.univ_inter,
    Finset.inter_univ, smul_smul, Finset.card_univ]
  congr 1
  by_cases hs : (s.card : ℂ) = 0
  · simp [hs]
  · field_simp

/-- The distance to a uniform subset projector is the square root of the omitted fraction,
including the empty subset. -/
theorem uniformSubsetProjector_distance_sq [Nonempty Y] (s : Finset Y) :
    ‖uniformSubsetProjector Finset.univ - uniformSubsetProjector s‖ ^ 2 =
      1 - (s.card : ℝ) / Fintype.card Y := by
  apply l2_opNorm_sub_sq_eq_one_sub_of_mul_mul_eq
    (uniformSubsetProjector_hermitian _) (uniformSubsetProjector_idempotent _)
    (uniformSubsetProjector_hermitian _) (uniformSubsetProjector_idempotent _)
  · exact (div_le_one (by positivity)).mpr (by exact_mod_cast Finset.card_le_univ s)
  · simpa using uniformSubsetProjector_sandwich_univ s
  · simpa using uniformSubsetProjector_univ_sandwich s
  · intro h
    obtain ⟨y⟩ := ‹Nonempty Y›
    have hh := congrArg (fun M : Matrix Y Y ℂ ↦ M y y) h
    have hN : (Fintype.card Y : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [uniformSubsetProjector, vecMulVec_apply, subsetVector, hN] at hh

omit [Fintype Y] in
/-- A subset of one label class gives a label-preserving uniform projector. -/
theorem uniformSubsetProjector_pinch {κ : Type*} [DecidableEq κ] (β : Y → κ)
    (s : Finset Y) (h : ∀ a ∈ s, ∀ b ∈ s, β a = β b) :
    pinch β (uniformSubsetProjector s) = uniformSubsetProjector s := by
  apply pinch_eq_self_iff.mpr
  intro a b hab
  have ha : a ∈ s := by
    by_contra ha
    exact hab (by simp [uniformSubsetProjector, vecMulVec_apply, subsetVector, ha])
  have hb : b ∈ s := by
    by_contra hb
    exact hab (by simp [uniformSubsetProjector, vecMulVec_apply, subsetVector, hb])
  exact h a ha b hb

/-- A coherent label-controlled operation has uniform-projector commutator at most twice
the square root of the fraction outside any one label class, with an arbitrary ancilla.
This is the single filled-cell estimate used in the repair note FIX (27). -/
theorem uniformSubsetProjector_commutator_le [Nonempty Y]
    {κ Z : Type*} [Fintype Z] [DecidableEq Z]
    (β : Y → κ) (s : Finset Y) (hs : ∀ a ∈ s, ∀ b ∈ s, β a = β b)
    (U : κ → Matrix Z Z ℂ) (hU : ∀ k, U k ∈ unitaryGroup Z ℂ) :
    ‖labelControlled (fun a : Y × Z ↦ β a.1) (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k) *
        (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) -
      (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) *
        labelControlled (fun a : Y × Z ↦ β a.1) (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k)‖ ≤
      2 * Real.sqrt (1 - (s.card : ℝ) / Fintype.card Y) := by
  classical
  have hh := l2_opNorm_commutator_labelControlled_one_kronecker_le
    (uniformSubsetProjector_pinch β s hs) hU
    (A := uniformSubsetProjector Finset.univ)
  have hd : ‖uniformSubsetProjector Finset.univ - uniformSubsetProjector s‖ =
      Real.sqrt (1 - (s.card : ℝ) / Fintype.card Y) := by
    rw [← uniformSubsetProjector_distance_sq s, Real.sqrt_sq (norm_nonneg _)]
  rwa [hd] at hh

/-- On the filled labels, the compressed empty-sector projector is the uniform projector.
This identifies the single-cell operator in FIX (27) with the old oracle's invalid sector. -/
theorem uniformSubsetProjector_univ_eq_cellInvalid :
    uniformSubsetProjector (Finset.univ : Finset Y) =
      (cellCompress Y * diagonal (fun a : Option Y ↦ if a = none then 1 else 0) *
        cellCompress Y).submatrix some some := by
  ext a b
  simp [uniformSubsetProjector, subsetVector, vecMulVec_apply, Matrix.mul_apply,
    submatrix_apply, diagonal_apply, cellAmp_mul_self]

/-- Counting changed labels bounds the coherent uniform-projector commutator. The comparison
label may be the extraction result on the absent cell. -/
theorem uniformProjector_commutator_le [Nonempty Y]
    {κ Z : Type*} [DecidableEq κ] [Fintype Z] [DecidableEq Z]
    (β : Y → κ) (baseline : κ) (U : κ → Matrix Z Z ℂ)
    (hU : ∀ k, U k ∈ unitaryGroup Z ℂ) :
    ‖labelControlled (fun a : Y × Z ↦ β a.1) (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k) *
        (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) -
      (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) *
        labelControlled (fun a : Y × Z ↦ β a.1) (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k)‖ ≤
      2 * Real.sqrt ((Finset.univ.filter fun y ↦ β y ≠ baseline).card /
        (Fintype.card Y : ℝ)) := by
  have hh := uniformSubsetProjector_commutator_le β
    (Finset.univ.filter fun y ↦ β y = baseline)
    (fun a ha b hb ↦ (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) U hU
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun y ↦ β y = baseline)
  have hc' : ((Finset.univ.filter fun y ↦ β y = baseline).card : ℝ) +
      (Finset.univ.filter fun y ↦ β y ≠ baseline).card = Fintype.card Y := by
    exact_mod_cast hc
  have he : 1 - ((Finset.univ.filter fun y ↦ β y = baseline).card : ℝ) / Fintype.card Y =
      (Finset.univ.filter fun y ↦ β y ≠ baseline).card / (Fintype.card Y : ℝ) := by
    apply (sub_eq_iff_eq_add).mpr
    rw [← add_div, add_comm, hc', div_self (by positivity)]
  rwa [he] at hh

end uniformProjector

section cellOccupancy

variable {Y Z κ : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- The isometric inclusion of filled cell labels, with an arbitrary ancilla. -/
@[expose]
noncomputable def filledCellInclusion : Matrix (Option Y × Z) (Y × Z) ℂ :=
  basisMatrix fun a : Y × Z ↦ (some a.1, a.2)

/-- The inclusion of filled labels preserves inner products. -/
theorem filledCellInclusion_isometry :
    (filledCellInclusion (Y := Y) (Z := Z))ᴴ * (filledCellInclusion (Y := Y) (Z := Z)) = 1 := by
  change (basisMatrix (fun a : Y × Z ↦ (some a.1, a.2)))ᴴ *
    basisMatrix (fun a : Y × Z ↦ (some a.1, a.2)) = 1
  apply conjTranspose_basisMatrix_mul_self
  intro a b h
  simpa only [Prod.mk.injEq, Option.some.injEq, ← Prod.ext_iff] using h

/-- The old oracle’s one-cell invalid projector in compressed coordinates. -/
@[expose]
noncomputable def oldInvalidCell : Matrix (Option Y) (Option Y) ℂ :=
  cellCompress Y * cellEmpty * cellCompress Y

/-- The invalid projector is the outer product of the filled uniform vector. -/
theorem oldInvalidCell_apply (a b : Option Y) :
    oldInvalidCell a b = cellUniform Y a * cellUniform Y b := by
  cases a <;> cases b <;>
    simp [oldInvalidCell, cellEmpty, Matrix.mul_apply, diagonal_apply, cellAmp_mul_self]

/-- A response unitary controlled by the label of a possibly empty cell. -/
@[expose]
noncomputable def filledCellControl (β : Option Y → κ) (U : κ → Matrix Z Z ℂ) :
    Matrix (Option Y × Z) (Option Y × Z) ℂ :=
  labelControlled (fun a ↦ β a.1) fun k ↦ (1 : Matrix (Option Y) (Option Y) ℂ) ⊗ₖ U k

omit [Fintype Y] [Fintype Z] [DecidableEq Z] in
/-- The cell label is unchanged by its controlled response operation. -/
theorem filledCellControl_apply (β : Option Y → κ) (U : κ → Matrix Z Z ℂ)
    (a b : Option Y × Z) :
    filledCellControl β U a b = if a.1 = b.1 then U (β a.1) a.2 b.2 else 0 := by
  simp [filledCellControl, labelControlled_apply, kroneckerMap_apply, one_apply]

/-- Embedding a filled-label operator extends it by zero on the empty cell. -/
theorem filledCellInclusion_conj (M : Matrix (Y × Z) (Y × Z) ℂ)
    (a b : Option Y × Z) :
    ((filledCellInclusion (Y := Y) (Z := Z)) * M * (filledCellInclusion (Y := Y) (Z := Z))ᴴ) a b =
      match a.1, b.1 with
      | some y, some y' => M (y, a.2) (y', b.2)
      | _, _ => 0 := by
  rcases a with ⟨a, z⟩
  rcases b with ⟨b, z'⟩
  cases a <;> cases b <;>
    simp [filledCellInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply,
      basisMatrix_apply, Fintype.sum_prod_type, ite_and, apply_ite]

/-- The old invalid projector is the embedded filled uniform projector. -/
theorem oldInvalidCell_kronecker_eq :
    oldInvalidCell (Y := Y) ⊗ₖ (1 : Matrix Z Z ℂ) =
      (filledCellInclusion (Y := Y) (Z := Z)) *
        (uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)) *
        (filledCellInclusion (Y := Y) (Z := Z))ᴴ := by
  ext ⟨a, z⟩ ⟨b, z'⟩
  rw [filledCellInclusion_conj]
  cases a <;> cases b <;>
    simp [kroneckerMap_apply, oldInvalidCell_apply,
      uniformSubsetProjector_univ_eq_cellInvalid, submatrix_apply, Matrix.mul_apply,
      diagonal_apply, cellAmp_mul_self]

/-- A cell-controlled unitary restricts to the corresponding filled-label control. -/
theorem filledCellControl_mul_inclusion (β : Option Y → κ) (U : κ → Matrix Z Z ℂ) :
    filledCellControl β U * filledCellInclusion (Y := Y) (Z := Z) =
      filledCellInclusion (Y := Y) (Z := Z) *
        labelControlled (fun a : Y × Z ↦ β (some a.1))
          (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k) := by
  ext ⟨a, z⟩ ⟨b, z'⟩
  cases a <;>
    simp [filledCellControl, filledCellInclusion, Matrix.mul_apply,
      labelControlled_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type,
      basisMatrix_apply, ite_and, eq_comm]
  split_ifs with h <;> simp_all

/-- Restricting a cell-controlled unitary to filled labels commutes with inclusion. -/
theorem inclusion_adjoint_mul_filledCellControl (β : Option Y → κ)
    (U : κ → Matrix Z Z ℂ) :
    (filledCellInclusion (Y := Y) (Z := Z))ᴴ * filledCellControl β U =
      labelControlled (fun a : Y × Z ↦ β (some a.1))
        (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k) *
          (filledCellInclusion (Y := Y) (Z := Z))ᴴ := by
  ext ⟨a, z⟩ ⟨b, z'⟩
  cases b <;>
    simp [filledCellControl, filledCellInclusion, Matrix.mul_apply,
      labelControlled_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type,
      basisMatrix_apply, Matrix.conjTranspose_apply, ite_and, eq_comm, apply_ite]
  split_ifs with h <;> simp_all

/-- The full-cell invalid commutator is supported entirely on filled labels. -/
theorem oldInvalidCell_commutator_eq (β : Option Y → κ) (U : κ → Matrix Z Z ℂ) :
    let V := filledCellControl β U
    let P := oldInvalidCell (Y := Y) ⊗ₖ (1 : Matrix Z Z ℂ)
    let V' := labelControlled (fun a : Y × Z ↦ β (some a.1))
      (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k)
    let P' := uniformSubsetProjector Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)
    V * P - P * V = filledCellInclusion (Y := Y) (Z := Z) * (V' * P' - P' * V') *
      (filledCellInclusion (Y := Y) (Z := Z))ᴴ := by
  dsimp only
  rw [oldInvalidCell_kronecker_eq]
  let J := filledCellInclusion (Y := Y) (Z := Z)
  let V := filledCellControl β U
  let P := uniformSubsetProjector (Y := Y) Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)
  let V' := labelControlled (fun a : Y × Z ↦ β (some a.1))
    (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k)
  change V * (J * P * Jᴴ) - (J * P * Jᴴ) * V = J * (V' * P - P * V') * Jᴴ
  calc
    _ = (V * J) * P * Jᴴ - J * P * (Jᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = (J * V') * P * Jᴴ - J * P * (V' * Jᴴ) := by
      rw [filledCellControl_mul_inclusion, inclusion_adjoint_mul_filledCellControl]
    _ = _ := by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- The range projection of the filled inclusion is the occupancy projector. -/
theorem filledCellInclusion_range :
    filledCellInclusion (Y := Y) (Z := Z) *
      (filledCellInclusion (Y := Y) (Z := Z))ᴴ =
        (1 - cellEmpty (Y := Y)) ⊗ₖ (1 : Matrix Z Z ℂ) := by
  have h := filledCellInclusion_conj (1 : Matrix (Y × Z) (Y × Z) ℂ)
  ext ⟨a, z⟩ ⟨b, z'⟩
  specialize h (a, z) (b, z')
  rw [Matrix.mul_one] at h
  rw [h]
  cases a <;> cases b <;>
    simp [cellEmpty, kroneckerMap_apply, diagonal_apply, one_apply, ite_and]
  split_ifs <;> rfl

/-- The invalid commutator Gram matrix is bounded by the changing-label fraction times
four times the occupancy projector. This is the occupancy-sensitive form of FIX (27). -/
theorem oldInvalidCell_commutator_gram_le [Nonempty Y] [DecidableEq κ]
    (β : Option Y → κ) (U : κ → Matrix Z Z ℂ)
    (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) :
    let V := filledCellControl β U
    let P := oldInvalidCell (Y := Y) ⊗ₖ (1 : Matrix Z Z ℂ)
    let a := ((Finset.univ.filter fun y : Y ↦ β (some y) ≠ β none).card : ℝ) /
      Fintype.card Y
    ((4 * a) • ((1 - cellEmpty (Y := Y)) ⊗ₖ (1 : Matrix Z Z ℂ)) -
      (V * P - P * V)ᴴ * (V * P - P * V)).PosSemidef := by
  dsimp only
  let J := filledCellInclusion (Y := Y) (Z := Z)
  let V := labelControlled (fun a : Y × Z ↦ β (some a.1))
    (fun k ↦ (1 : Matrix Y Y ℂ) ⊗ₖ U k)
  let P := uniformSubsetProjector (Y := Y) Finset.univ ⊗ₖ (1 : Matrix Z Z ℂ)
  let E := V * P - P * V
  let a := ((Finset.univ.filter fun y : Y ↦ β (some y) ≠ β none).card : ℝ) /
    Fintype.card Y
  have ha : 0 ≤ a := by positivity
  have hn : ‖E‖ ≤ 2 * Real.sqrt a :=
    uniformProjector_commutator_le (fun y ↦ β (some y)) (β none) U hU
  have hn' : ‖E‖ ^ 2 ≤ 4 * a := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
    simpa only [mul_pow, Real.sq_sqrt ha, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
  have hE : ((4 * a) • (1 : Matrix (Y × Z) (Y × Z) ℂ) - Eᴴ * E).PosSemidef := by
    have hI : (1 : Matrix (Y × Z) (Y × Z) ℂ).PosSemidef := PosSemidef.one
    have hh := hI.smul (sub_nonneg.mpr hn')
    have hh' := hh.add (MatrixMap.posSemidef_l2_opNorm_sq_smul_one_sub E)
    convert hh' using 1
    module
  have hJ : Jᴴ * J = 1 := filledCellInclusion_isometry
  have hp := hE.mul_mul_conjTranspose_same J
  rw [oldInvalidCell_commutator_eq, ← filledCellInclusion_range]
  change ((4 * a) • (J * Jᴴ) - (J * E * Jᴴ)ᴴ * (J * E * Jᴴ)).PosSemidef
  convert hp using 1
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ J, hJ, Matrix.one_mul]

section databaseControl
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- An ancilla unitary controlled by a function of the compressed database. -/
@[expose]
noncomputable def databaseControl (β : Database C Y → κ) (U : κ → Matrix Z Z ℂ) :
    Matrix (Database C Y × Z) (Database C Y × Z) ℂ :=
  labelControlled (fun a ↦ β a.1) fun k ↦
    (1 : Matrix (Database C Y) (Database C Y) ℂ) ⊗ₖ U k

/-- Separate one database cell and the response register from the remaining cells. -/
@[expose]
def extractionCellSplit (c : C) :
    (Database C Y × Z) ≃ (Option Y × Z) × ({i // i ≠ c} → Option Y) :=
  (Equiv.prodCongr (Equiv.funSplitAt c (Option Y)) (Equiv.refl Z)).trans
    ((Equiv.prodAssoc _ _ _).trans
      ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans
        (Equiv.prodAssoc _ _ _).symm))

omit [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] [Fintype C] in
/-- The cell splitting reads the selected cell and leaves the remaining database as context. -/
theorem extractionCellSplit_apply (c : C) (a : Database C Y × Z) :
    extractionCellSplit c a = ((a.1 c, a.2), fun i ↦ a.1 i.1) := rfl

omit [Fintype Y] [Fintype Z] [DecidableEq Z] in
/-- A database-controlled operation decomposes into one-cell operations in each context. -/
theorem databaseControl_blocks (c : C) (β : Database C Y → κ)
    (U : κ → Matrix Z Z ℂ) :
    databaseControl β U = liftBlocks (extractionCellSplit c)
      (fun r ↦ filledCellControl
        (fun a ↦ β ((Equiv.funSplitAt c (Option Y)).symm (a, r))) U) := by
  ext ⟨D, z⟩ ⟨D', z'⟩
  simp only [databaseControl, labelControlled_apply, kroneckerMap_apply, one_apply,
    liftBlocks, submatrix_apply, blockDiagonal_apply, extractionCellSplit_apply,
    filledCellControl_apply]
  by_cases h : D = D'
  · subst D'
    simp only [ite_true, one_mul]
    change U (β D) z z' = U (β ((Equiv.funSplitAt c (Option Y)).symm
      ((Equiv.funSplitAt c (Option Y)) D))) z z'
    rw [Equiv.symm_apply_apply]
  · have hn : ¬ (D c = D' c ∧ (fun i : {i // i ≠ c} ↦ D i.1) = fun i ↦ D' i.1) := by
      intro hh
      apply h
      apply (Equiv.funSplitAt c (Option Y)).injective
      exact Prod.ext hh.1 hh.2
    split_ifs <;> simp_all

/-- The invalid projector of one database cell, tensored with an ancilla identity. -/
@[expose]
noncomputable def databaseInvalidCell (c : C) :
    Matrix (Database C Y × Z) (Database C Y × Z) ℂ :=
  liftBlocks (extractionCellSplit c) fun _ ↦
    oldInvalidCell (Y := Y) ⊗ₖ (1 : Matrix Z Z ℂ)

/-- The fraction of filled labels changing the control value relative to the empty cell. -/
@[expose]
noncomputable def changingFraction [DecidableEq κ] (β : Database C Y → κ)
    (c : C) (r : {i // i ≠ c} → Option Y) : ℝ :=
  ((Finset.univ.filter fun y : Y ↦
    β ((Equiv.funSplitAt c (Option Y)).symm (some y, r)) ≠
      β ((Equiv.funSplitAt c (Option Y)).symm (none, r))).card : ℝ) / Fintype.card Y

/-- The changing-label fraction weighted by occupancy of the selected cell. -/
@[expose]
noncomputable def changingWeight [DecidableEq κ] (β : Database C Y → κ)
    (c : C) (D : Database C Y) : ℝ :=
  if (D c).isSome then changingFraction β c (fun i ↦ D i.1) else 0

omit [Fintype Z] in
/-- Lifting the local occupancy bound gives a diagonal context-dependent weight. -/
theorem changingWeight_block [DecidableEq κ] (β : Database C Y → κ) (c : C) :
    liftBlocks (extractionCellSplit (Z := Z) c)
      (fun r ↦ (4 * changingFraction β c r) •
        ((1 - cellEmpty (Y := Y)) ⊗ₖ (1 : Matrix Z Z ℂ))) =
      diagonal (fun a : Database C Y × Z ↦ ((4 * changingWeight β c a.1 : ℝ) : ℂ)) := by
  ext ⟨D, z⟩ ⟨D', z'⟩
  simp only [liftBlocks, submatrix_apply, blockDiagonal_apply, extractionCellSplit_apply,
    Matrix.smul_apply, kroneckerMap_apply, Matrix.sub_apply, one_apply, cellEmpty, diagonal_apply,
    changingWeight]
  by_cases hD : D = D'
  · subst D'
    cases h : D c <;> simp [Complex.real_smul, mul_ite]
  · have hn : ¬ (D c = D' c ∧ (fun i : {i // i ≠ c} ↦ D i.1) = fun i ↦ D' i.1) := by
      intro hh
      apply hD
      apply (Equiv.funSplitAt c (Option Y)).injective
      exact Prod.ext hh.1 hh.2
    split_ifs <;> simp_all

/-- The one-cell invalid commutator obeys the context-dependent occupancy bound. -/
theorem databaseControl_commutator_gram_le [Nonempty Y] [DecidableEq κ]
    (β : Database C Y → κ) (U : κ → Matrix Z Z ℂ)
    (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) (c : C) :
    let V := databaseControl β U
    let P := databaseInvalidCell (Y := Y) (Z := Z) c
    (diagonal (fun a : Database C Y × Z ↦ ((4 * changingWeight β c a.1 : ℝ) : ℂ)) -
      (V * P - P * V)ᴴ * (V * P - P * V)).PosSemidef := by
  dsimp only
  let V := fun r : {i // i ≠ c} → Option Y ↦ filledCellControl
    (fun a ↦ β ((Equiv.funSplitAt c (Option Y)).symm (a, r))) U
  let P := fun _ : {i // i ≠ c} → Option Y ↦
    oldInvalidCell (Y := Y) ⊗ₖ (1 : Matrix Z Z ℂ)
  let B := fun r : {i // i ≠ c} → Option Y ↦ (4 * changingFraction β c r) •
    ((1 - cellEmpty (Y := Y)) ⊗ₖ (1 : Matrix Z Z ℂ))
  have hlocal : ∀ r, (B r - ((V * P - P * V) r)ᴴ * ((V * P - P * V) r)).PosSemidef :=
    fun r ↦ oldInvalidCell_commutator_gram_le
      (fun a ↦ β ((Equiv.funSplitAt c (Option Y)).symm (a, r))) U hU
  have h := posSemidef_liftBlocks (extractionCellSplit (Z := Z) c) hlocal
  change (liftBlocks (extractionCellSplit c)
    (B - (fun r ↦ ((V * P - P * V) r)ᴴ) * (V * P - P * V))).PosSemidef at h
  rw [liftBlocks_sub, liftBlocks_mul, liftBlocks_adjoint] at h
  simp only [liftBlocks_sub, liftBlocks_mul] at h
  have hv : liftBlocks (extractionCellSplit c) V = databaseControl β U :=
    (databaseControl_blocks c β U).symm
  have hb : liftBlocks (extractionCellSplit c) B =
      diagonal (fun a : Database C Y × Z ↦ ((4 * changingWeight β c a.1 : ℝ) : ℂ)) :=
    changingWeight_block β c
  rw [hv, hb] at h
  exact h

omit [DecidableEq Y] in
/-- A uniform bound on occupied-cell fractions sums to that bound times population. -/
theorem sum_changingWeight_le [DecidableEq κ] (β : Database C Y → κ)
    (D : Database C Y) {a : ℝ}
    (h : ∀ c, (D c).isSome → changingFraction β c (fun i ↦ D i.1) ≤ a) :
    ∑ c, changingWeight β c D ≤ a * D.size := by
  calc
    _ ≤ ∑ c : C, if (D c).isSome then a else 0 := by
      apply Finset.sum_le_sum
      intro c _
      dsimp only [changingWeight]
      split_ifs with hc
      · exact h c hc
      · rfl
    _ = _ := by simp [Database.size, mul_comm]

/-- The projector onto databases with at most the specified number of populated cells. -/
@[expose]
noncomputable def populationCut (s : ℕ) :
    Matrix (Database C Y × Z) (Database C Y × Z) ℂ :=
  diagonal fun a ↦ if a.1.size ≤ s then 1 else 0

/-- On the original population-restricted subspace, the summed invalid commutator Gram
matrix is bounded by four times population times the changing fraction, as in FIX (27).
The hypothesis is a combinatorial bound on changing labels; no checker preservation is assumed. -/
theorem databaseControl_sum_commutator_gram_le [Nonempty Y] [DecidableEq κ]
    (β : Database C Y → κ) (U : κ → Matrix Z Z ℂ)
    (hU : ∀ a, U a ∈ unitaryGroup Z ℂ) (s : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hβ : ∀ D : Database C Y, D.size ≤ s → ∀ c, (D c).isSome →
      changingFraction β c (fun i ↦ D i.1) ≤ a) :
    let V := databaseControl β U
    let K := populationCut (C := C) (Y := Y) (Z := Z) s
    let E := fun c ↦ V * databaseInvalidCell c - databaseInvalidCell c * V
    ((4 * s * a) • K - K * (∑ c, (E c)ᴴ * E c) * K).PosSemidef := by
  dsimp only
  let K := populationCut (C := C) (Y := Y) (Z := Z) s
  let V := databaseControl β U
  let E := fun c ↦ V * databaseInvalidCell c - databaseInvalidCell c * V
  let B := diagonal (fun d : Database C Y × Z ↦ ((4 * ∑ c, changingWeight β c d.1 : ℝ) : ℂ))
  have hsum : (B - ∑ c, (E c)ᴴ * E c).PosSemidef := by
    have h := posSemidef_sum Finset.univ fun c _ ↦ databaseControl_commutator_gram_le β U hU c
    convert h using 1
    rw [Finset.sum_sub_distrib]
    congr 1
    ext d d'
    by_cases hd : d = d' <;> simp [B, hd, Finset.mul_sum, Matrix.sum_apply]
  have hK : Kᴴ = K := by simp [K, populationCut, diagonal_conjTranspose]
  have hrestrict := hsum.mul_mul_conjTranspose_same K
  rw [hK, Matrix.mul_sub, Matrix.sub_mul] at hrestrict
  have hbound : ((4 * s * a) • K - K * B * K).PosSemidef := by
    simp only [K, populationCut, B, ← diagonal_smul, diagonal_mul_diagonal]
    rw [diagonal_sub]
    apply posSemidef_diagonal_iff.mpr
    intro d
    dsimp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply]
    split_ifs with hd
    · have hh := (sum_changingWeight_le β d.1 (hβ d.1 hd)).trans
        (mul_le_mul_of_nonneg_left (show (d.1.size : ℝ) ≤ s by exact_mod_cast hd) ha)
      simp only [one_mul, mul_one, Complex.real_smul, mul_one]
      exact_mod_cast (show 0 ≤ 4 * (s : ℝ) * a - 4 * ∑ c, changingWeight β c d.1 by nlinarith)
    · simp
  convert hbound.add hrestrict using 1
  abel

omit [Fintype Z] in
/-- The block-defined invalid operator is the tensor product with a single invalid cell. -/
theorem databaseInvalidCell_eq_piKron (c : C) :
    databaseInvalidCell (Y := Y) (Z := Z) c =
      piKron (Pi.mulSingle c (oldInvalidCell (Y := Y))) ⊗ₖ (1 : Matrix Z Z ℂ) := by
  ext ⟨D, z⟩ ⟨D', z'⟩
  simp only [databaseInvalidCell, liftBlocks, submatrix_apply, blockDiagonal_apply,
    extractionCellSplit_apply, kroneckerMap_apply, piKron_apply]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ c, Pi.mulSingle_eq_same]
  have hr : (∏ j : {j // j ≠ c},
      (Pi.mulSingle c (oldInvalidCell (Y := Y)) : C → Matrix (Option Y) (Option Y) ℂ)
        j.1 (D j) (D' j)) =
        if (fun i : {i // i ≠ c} ↦ D i.1) = (fun i ↦ D' i.1) then 1 else 0 := by
    have h1 (j : {j // j ≠ c}) :
        (Pi.mulSingle c (oldInvalidCell (Y := Y)) : C → Matrix (Option Y) (Option Y) ℂ) j.1 = 1 :=
      Pi.mulSingle_eq_of_ne j.2 _
    simp only [h1, one_apply, funext_iff]
    exact Fintype.prod_boole
  rw [hr]
  split_ifs <;> simp

omit [Fintype Z] in
/-- The block-defined invalid operator is the compressed empty-cell projector. -/
theorem databaseInvalidCell_eq_compress [Nonempty Y] (c : C) :
    databaseInvalidCell (Y := Y) (Z := Z) c =
      (compressAll C Y * diagonal (fun D ↦ if D c = none then 1 else 0) *
        compressAll C Y) ⊗ₖ (1 : Matrix Z Z ℂ) := by
  rw [databaseInvalidCell_eq_piKron]
  congr 1
  ext D D'
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, compressAll]
  have he : (∑ D₁ : Database C Y, (piKron (fun _ : C ↦ cellCompress Y) D D₁ *
      (if D₁ c = none then 1 else 0)) * piKron (fun _ : C ↦ cellCompress Y) D₁ D') =
      ∑ D₁ : Database C Y, (if D₁ c = none then 1 else 0) *
        (piKron (fun _ : C ↦ cellCompress Y) D D₁ *
          piKron (fun _ : C ↦ cellCompress Y) D₁ D') := by
    apply Finset.sum_congr rfl
    intro D₁ _
    ring
  rw [he, sum_mul_piKron_mul_piKron (fun _ : C ↦ cellCompress Y)
    (fun _ : C ↦ cellCompress Y) c (fun u ↦ if u = none then 1 else 0), piKron_apply]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = c
  · subst j
    simp [oldInvalidCell, Matrix.mul_apply, cellEmpty, diagonal_apply]
  · simp only [hj, Pi.mulSingle_eq_of_ne hj, ite_false, one_mul]
    exact (congrArg (fun A : Matrix (Option Y) (Option Y) ℂ ↦ A (D j) (D' j))
      (cellCompress_mul_self Y)).symm

end databaseControl

end cellOccupancy

section blocks
variable {J M B ι : Type*} [DecidableEq B]

/-- Lifting context-dependent blocks commutes with finite sums. -/
theorem liftBlocks_sum (e : J ≃ M × B) (s : Finset ι) (A : ι → B → Matrix M M ℂ) :
    liftBlocks e (∑ i ∈ s, A i) = ∑ i ∈ s, liftBlocks e (A i) := by
  ext j j'
  simp only [liftBlocks, submatrix_apply, blockDiagonal_apply, Matrix.sum_apply,
    Finset.sum_apply]
  split_ifs <;> simp

/-- A common summed Gram bound lifts over orthogonal context blocks. -/
theorem liftBlocks_sum_gram_le [Fintype J] [Fintype M] [Finite B] [Fintype ι]
    (e : J ≃ M × B) (V K : B → Matrix M M ℂ) (R : ι → B → Matrix M M ℂ) (a : ℝ)
    (h : ∀ b, (a • K b - K b * (∑ c,
      (V b * R c b - R c b * V b)ᴴ * (V b * R c b - R c b * V b)) * K b).PosSemidef) :
    let V' := liftBlocks e V
    let K' := liftBlocks e K
    let R' := fun c ↦ liftBlocks e (R c)
    (a • K' - K' * (∑ c, (V' * R' c - R' c * V')ᴴ *
      (V' * R' c - R' c * V')) * K').PosSemidef := by
  let F := fun c ↦ V * R c - R c * V
  have hh : (liftBlocks e (a • K - K *
      (∑ c : ι, (fun b ↦ (F c b)ᴴ) * F c) * K)).PosSemidef :=
    posSemidef_liftBlocks e fun b ↦ by
      simpa only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, Finset.sum_apply, F] using h b
  rw [liftBlocks_sub, liftBlocks_smul, liftBlocks_mul, liftBlocks_mul, liftBlocks_sum] at hh
  simp only [liftBlocks_mul, liftBlocks_adjoint, F, liftBlocks_sub] at hh
  exact hh

end blocks

namespace CompressedReplay
variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Flattening indexed databases preserves the compressed empty-cell projector. -/
theorem invalid_eq_flat (c : Fin k × X) :
    invalid (Y := Y) c =
      (compressAll (Fin k × X) Y *
        diagonal (fun D : Database (Fin k × X) Y ↦ if D c = none then 1 else 0) *
        compressAll (Fin k × X) Y).submatrix
          (Equiv.curry (Fin k) X (Option Y)).symm
          (Equiv.curry (Fin k) X (Option Y)).symm := by
  have hd : (diagonal fun D : Fin k → Database X Y ↦
      if D c.1 c.2 = none then (1 : ℂ) else 0) =
      (diagonal fun D : Database (Fin k × X) Y ↦ if D c = none then (1 : ℂ) else 0).submatrix
        (Equiv.curry (Fin k) X (Option Y)).symm
        (Equiv.curry (Fin k) X (Option Y)).symm := by
    rw [submatrix_diagonal_equiv]
    rfl
  rw [invalid, compressDatabases_eq_flat, hd, submatrix_mul_equiv, submatrix_mul_equiv]

/-- The cellwise invalid operator agrees with the indexed-database projector under flattening. -/
theorem databaseInvalidCell_flat [Nonempty Y] {Z : Type*} [DecidableEq Z] (c : Fin k × X) :
    (databaseInvalidCell (Y := Y) (Z := Z) c).submatrix
      (Equiv.prodCongr (Equiv.curry (Fin k) X (Option Y)).symm (Equiv.refl Z))
      (Equiv.prodCongr (Equiv.curry (Fin k) X (Option Y)).symm (Equiv.refl Z)) =
        invalid (Y := Y) c ⊗ₖ (1 : Matrix Z Z ℂ) := by
  rw [databaseInvalidCell_eq_compress, invalid_eq_flat]
  ext ⟨D, z⟩ ⟨D', z'⟩
  rfl

end CompressedReplay

end Quantum

namespace Quantum
namespace CompressedReplay
variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Every invalid-cell projector commutes with every ordinary port of the old oracle. -/
theorem invalid_commute_ordinary (p : Fin k) (x : Fin k × X) :
    (show Matrix ((X × Y) × (Fin k → Database X Y))
      ((X × Y) × (Fin k → Database X Y)) ℂ from (compressedVCOracle k X Y).U p) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ invalid x) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ invalid x) *
        (show Matrix ((X × Y) × (Fin k → Database X Y))
          ((X × Y) × (Fin k → Database X Y)) ℂ from (compressedVCOracle k X Y).U p) := by
  let C := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y
  let D : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
    diagonal fun d ↦ if d x.1 x.2 = none then 1 else 0
  have hCC : C * C = 1 := by
    simp [C, ← mul_kronecker_mul, compressDatabases_mul_self]
  have hT : tableOracle (fun d : Fin k → Database X Y ↦ (d p).lookup) *
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ D) =
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ D) *
          tableOracle (fun d : Fin k → Database X Y ↦ (d p).lookup) := by
    apply tableOracle_mul_one_kronecker_comm
    intro d d' h
    have he : d = d' := by
      by_contra hn
      exact h (by simp [D, diagonal_apply_ne _ hn])
    rw [he]
  have hA : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ invalid x =
      C * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ D) * C := by
    simp [C, D, invalid, ← mul_kronecker_mul]
  rw [compressedVCOracle_U_eq_conj, hA]
  change (C * _ * C) * (C * _ * C) = (C * _ * C) * (C * _ * C)
  rw [conjugate_mul C hCC, conjugate_mul C hCC, hT]

/-- The rectangular invalid potential equals the sum of all cell-invalid weights. -/
theorem invalidStack_potential_eq {A : Type*} [Fintype A] [DecidableEq A]
    {ρ : Matrix (A × (Fin k → Database X Y)) (A × (Fin k → Database X Y)) ℂ}
    (hρ : ρ.PosSemidef) :
    QuantumRuntime.potential (invalidStack (k := k) (X := X) (Y := Y)) ρ =
      ∑' c : Fin k × X, ENNReal.ofReal
        (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ invalid c) ρ).trace.re := by
  have hn (c : Fin k × X) :
      0 ≤ (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ invalid c) ρ).trace.re :=
    (hρ.mul_mul_conjTranspose_same _).trace_re_nonneg
  rw [QuantumRuntime.potential_eq, invalidStack_gram, tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg (fun c _ ↦ hn c)]
  congr 1
  simp only [MatrixMap.trace_conj_apply, conjTranspose_kronecker, conjTranspose_one,
    invalid_hermitian, ← mul_kronecker_mul, Matrix.one_mul, invalid_idempotent]
  have hs : (1 : Matrix A A ℂ) ⊗ₖ (∑ c : Fin k × X, invalid (Y := Y) c) =
      ∑ c : Fin k × X, (1 : Matrix A A ℂ) ⊗ₖ invalid (Y := Y) c := by
    ext a b
    simp only [kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]
  rw [hs, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

/-- The compressed invalid-cell projector annihilates the empty database basis vector. -/
theorem invalid_empty_column (c : Fin k × X) (D : Fin k → Database X Y) :
    invalid (Y := Y) c D (fun _ ↦ Database.empty) = 0 := by
  have h := congrArg (fun M : Matrix ((Fin k → Database X Y) × Unit)
      ((Fin k → Database X Y) × Unit) ℂ ↦ M (D, ()) ((fun _ ↦ Database.empty), ()))
    (databaseInvalidCell_flat (Y := Y) (Z := Unit) c)
  rw [databaseInvalidCell_eq_piKron] at h
  simp only [submatrix_apply, kroneckerMap_apply, Equiv.prodCongr_apply,
    Equiv.curry_symm_apply, Prod.map_apply, Equiv.refl_apply, one_apply_eq, mul_one,
    piKron_apply] at h
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ c, Pi.mulSingle_eq_same] at h
  simpa only [oldInvalidCell_apply, Function.uncurry, Database.empty_apply,
    cellUniform_none, mul_zero, zero_mul] using h.symm

/-- The old oracle starts with zero invalid potential, for any workspace matrix. -/
theorem invalidStack_initial_potential_zero {A : Type*} [Fintype A]
    (ρ : Matrix A A ℂ) :
    QuantumRuntime.potential (invalidStack (k := k) (X := X) (Y := Y))
      (ρ ⊗ₖ (compressedVCOracle k X Y).init.matrix) = 0 := by
  classical
  have hzero : MatrixMap.conj (invalidStack (k := k) (X := X) (Y := Y))
      (compressedVCOracle k X Y).init.matrix = 0 := by
    change MatrixMap.conj (invalidStack (k := k) (X := X) (Y := Y))
      (single (fun _ : Fin k ↦ (Database.empty : Database X Y))
        (fun _ : Fin k ↦ (Database.empty : Database X Y)) (1 : ℂ)) = 0
    rw [MatrixMap.conj_apply]
    have hh : invalidStack (k := k) (X := X) (Y := Y) *
        single (fun _ : Fin k ↦ (Database.empty : Database X Y))
        (fun _ : Fin k ↦ (Database.empty : Database X Y)) (1 : ℂ) = 0 := by
      ext a b
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j = (fun _ : Fin k ↦ (Database.empty : Database X Y))
      · subst j
        simp only [invalidStack, Matrix.of_apply, invalid_empty_column, zero_mul]
      · simp [Ne.symm hj]
    rw [hh, Matrix.zero_mul]
  have hh := MatrixMap.amplifyLeft_kronecker
    (MatrixMap.conj (invalidStack (k := k) (X := X) (Y := Y))) ρ
    (compressedVCOracle k X Y).init.matrix
  rw [hzero, kronecker_zero] at hh
  simpa only [QuantumRuntime.potential, Matrix.trace_zero, Complex.zero_re,
    ENNReal.ofReal_zero] using
    congrArg (fun M ↦ ENNReal.ofReal (Matrix.trace M).re) hh

end CompressedReplay

section gramTrace
variable {C S : Type*} [Fintype C] [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
/-- A population-restricted Gram inequality bounds the total observable weight on a positive
input supported by that population cutoff. No trace normalization is required. -/
theorem sum_conj_trace_le_of_gram (F : C → Matrix S S ℂ) (K Θ : Matrix S S ℂ)
    (hK : Kᴴ = K) (h : (Θ - K * (∑ c, (F c)ᴴ * F c) * K).PosSemidef)
    {ρ : Matrix S S ℂ} (hρ : ρ.PosSemidef) (hpop : K * ρ = ρ) :
    (∑' c, ENNReal.ofReal (MatrixMap.conj (F c) ρ).trace.re) ≤
      ENNReal.ofReal (Θ * ρ).trace.re := by
  let B := ∑ c, (F c)ᴴ * F c
  have hright : ρ * K = ρ := by
    have hh := congrArg conjTranspose hpop
    simpa only [conjTranspose_mul, hρ.isHermitian.eq, hK] using hh
  have htrace : ((K * B * K) * ρ).trace = (B * ρ).trace := by
    rw [Matrix.mul_assoc, hpop, Matrix.mul_assoc, Matrix.trace_mul_comm K,
      Matrix.mul_assoc, hright]
  have hh := h.trace_mul_re_nonneg hρ
  change 0 ≤ ((Θ - K * B * K) * ρ).trace.re at hh
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, htrace] at hh
  have hn (c : C) : 0 ≤ (MatrixMap.conj (F c) ρ).trace.re :=
    (hρ.mul_mul_conjTranspose_same _).trace_re_nonneg
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun c _ ↦ hn c)]
  apply ENNReal.ofReal_le_ofReal
  have he : (∑ c, (MatrixMap.conj (F c) ρ).trace.re) = (B * ρ).trace.re := by
    simp only [B, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, MatrixMap.trace_conj_apply]
  rw [he]
  linarith

end gramTrace
end Quantum

namespace Quantum.EmulatedOracle
section coherentGram
variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} {D : QReg}
  {C : Type*} [Fintype C]

omit [Fintype C] in
/-- A finite sum of portwise operators lifts to the sum of their coherent block operators. -/
theorem coherentBlocks_sum (s : Finset C)
    (A : C → ∀ p, Matrix (In p × D) (In p × D) ℂ) :
    coherentBlocks (∑ c ∈ s, A c) = ∑ c ∈ s, coherentBlocks (A c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coherentBlocks]
  | @insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, coherentBlocks_add, ih]

/-- Portwise commutator Gram bounds combine coherently, charged only to selected ports.
The population cutoff acts on the private register and the observables may form a family. -/
theorem coherent_sum_commutator_gram_le (E : EmulatedOracle P In)
    (R : C → Matrix E.S E.S ℂ) (K : Matrix E.S E.S ℂ) (selected : P → Bool) (θ : ℝ)
    (h : ∀ p, let Kp := (1 : Matrix (In p) (In p) ℂ) ⊗ₖ K
      let Rp := fun c ↦ (1 : Matrix (In p) (In p) ℂ) ⊗ₖ R c
      ((if selected p then θ else 0) • Kp - Kp *
        (∑ c, (E.U p * Rp c - Rp c * E.U p)ᴴ * (E.U p * Rp c - Rp c * E.U p)) * Kp).PosSemidef) :
    let U := E.coherent.U ()
    let K' := (1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ K
    let R' := fun c ↦ (1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ R c
    (selectedCharge selected θ * K' - K' *
      (∑ c, (U * R' c - R' c * U)ᴴ * (U * R' c - R' c * U)) * K').PosSemidef := by
  let Kp := fun p ↦ (1 : Matrix (In p) (In p) ℂ) ⊗ₖ K
  let Rp := fun c : C ↦ fun p ↦ (1 : Matrix (In p) (In p) ℂ) ⊗ₖ R c
  let B := fun p ↦ (if selected p then θ else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ)
  let F := fun c ↦ E.U * Rp c - Rp c * E.U
  have hh : (coherentBlocks (B * Kp - Kp *
      (∑ c : C, (fun p ↦ (F c p)ᴴ) * F c) * Kp)).PosSemidef :=
    posSemidef_coherentBlocks fun p ↦ by
      simpa only [B, Pi.mul_apply, Pi.sub_apply, Finset.sum_apply, F,
        Matrix.smul_mul, Matrix.one_mul] using h p
  rw [coherentBlocks_sub, coherentBlocks_mul, coherentBlocks_mul, coherentBlocks_mul,
    coherentBlocks_sum] at hh
  simp only [coherentBlocks_mul, coherentBlocks_adjoint, F, coherentBlocks_sub] at hh
  have hK : coherentBlocks Kp = (1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ K :=
    coherentBlocks_database K
  have hR (c : C) : coherentBlocks (Rp c) =
      (1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ R c := coherentBlocks_database (R c)
  simp only [hK, hR, coherentBlocks_unitary] at hh
  exact hh

end coherentGram
end Quantum.EmulatedOracle

namespace Quantum
universe u₁ v₁
namespace QuantumRuntime
variable {L : LocalSig.{u₁, v₁}} {spec : QuantumOracleSpec} (R : QuantumRuntime spec)
  (I : L.Interp) {A B C : QReg} {α β : Type*}

/-- Recording both outcomes identifies a composite instrument branch with the composition
of its two branches. The input, intermediate, and output registers may differ. -/
theorem run₂_bind_record (f : QuantumComp₂ L spec A B α)
    (g : α → QuantumComp₂ L spec B C β) (a : α) (b : β) :
    (R.run₂ I (f.bind fun a ↦ (g a).map (fun b ↦ (a, b)))).branch (a, b) =
      (R.run₂ I (g a)).branch b ∘ₗ (R.run₂ I f).branch a := by
  classical
  ext ρ : 1
  rw [run₂_bind, SubInstrument.branch_bind_apply]
  simp only [run₂_map, SubInstrument.map_eq_bind_pure, SubInstrument.branch_bind_apply]
  rw [tsum_eq_single a]
  · rw [tsum_eq_single b]
    · simp
    · intro b' hb
      rw [SubInstrument.branch_pure_of_ne (by simp [Ne.symm hb]), LinearMap.zero_apply]
  · intro a' ha
    have hz : ∀ b' : β,
        (SubInstrument.pure (a', b') :
          SubInstrument (C × R.D) (C × R.D) (α × β)).branch (a, b) = 0 :=
      fun _ ↦ SubInstrument.branch_pure_of_ne (by simp [Ne.symm ha])
    simp only [hz, LinearMap.zero_apply, tsum_zero]

/-- Forgetting the first recorded outcome recovers ordinary sequencing. -/
theorem bind_record_map_snd (f : QuantumComp₂ L spec A B α)
    (g : α → QuantumComp₂ L spec B C β) :
    (f.bind fun a ↦ (g a).map (fun b ↦ (a, b))).map Prod.snd = f.bind g := by
  simp only [QuantumComp₂.map, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind,
    QuantumComp₂.bind_pure]

end QuantumRuntime

/-- Three private Kraus operators compose in execution order while preserving a reference. -/
theorem conj_kronecker_three {A S : Type*} [Fintype A] [DecidableEq A]
    [Fintype S] (a p b : Matrix S S ℂ) :
    (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ b) ∘ₗ
      MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ p)) ∘ₗ
        MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ a) =
      MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ (b * p * a)) := by
  rw [← MatrixMap.conj_mul, ← MatrixMap.conj_mul, ← mul_kronecker_mul,
    ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]

section identification
variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z]
  [DecidableEq Z] [AddGroup Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).CheckIOForm)

/-- The accepting projector for a batch of old-oracle checks on a classical opening claim.
Empty cells are read as zero; malformed check transcripts are rejected. -/
noncomputable def actualBatch (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y * diagonal (fun D : Fin k → Database X Y ↦
    if ∀ i ∈ W, (io i).checkOn (fun x ↦ some ((D (c.idx i)).lookup x))
      (c.cm i) (c.ans i) (c.pf i) = true then 1 else 0) * compressDatabases k X Y

variable {Dm : Fin k → Type} (ME : MultiExtractor k Cm Dm (compressedVCOracle k X Y).S)
  (code : TpDCode k Dm Z)

/-- The actual batch-check accepting branch is conjugation by its accepting projector,
on every reference/private input matrix. -/
theorem run₂_actualBatch (W : Finset (Fin k)) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    (((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.run₂ .instruments
      (QComp.allIn W fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i))).branch
        true = MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ actualBatch io W c) := by
  exact branch_run₂_allIn _ W _ (compressDatabases_mul_self ..) _
    (fun i _ ↦ branch_run₂_checkAt_compressedVCOracle io ME code B i (c.idx i)
      (c.cm i) (c.ans i) (c.pf i))

end identification

section retained
variable {k : ℕ} {X Y Msg Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z]
  [DecidableEq Z] [AddGroup Z] {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  {VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i)}
  (io : ∀ i, (VC i).CheckIOForm)
  (code : TpDCode k (DmOf ℓ Msg Td) Z)

/-- The check/extract/check prefix of the P4 challenger with all three classical results
retained, including the decoded extraction tuple and both acceptance bits. -/
noncomputable def offlineChecks (hk : 1 ≤ k) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    QComp (EmulatedOracle.cohSpec (extIn k X Y Cm Z)) B B
      (Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) :=
  (QComp.allIn c.W fun i ↦ checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)).bind fun b₁ ↦
    ((extractQuery code B (TpIC.full hk c.idx c.cm)).bind fun tdm ↦
      (QComp.allIn c.Wᶜ fun i ↦
        checkAt VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)).map
          (fun b₂ ↦ (tdm, b₂))).map (fun r ↦ (b₁, r))

/-- The accepted prefix branch with extraction outcome `tdm` is exactly
`conj(1 ⊗ A_b Π_tdm A_a)`. Here `Π_tdm` is the measured response block of the coherent
extraction unitary. No extraction outcome is summed out in this identity. -/
theorem run₂_offlineChecks_accept [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
    (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (compressedVCOracle k X Y).S)
    (hk : 1 ≤ k) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) :
    (((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime.run₂ .instruments
      (offlineChecks (VC := VC) code hk c B)).branch (true, some tdm, true) =
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
          (actualBatch io c.Wᶜ c * (show Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ from
            extractProj ME (TpIC.full hk c.idx c.cm) tdm) *
            actualBatch io c.W c)) := by
  let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
  let checks := fun W ↦ QComp.allIn W fun i ↦
    checkAt (Z := Z) VC B i (c.idx i) (c.cm i) (c.ans i) (c.pf i)
  have h₁ := R.run₂_bind_record .instruments (checks c.W)
    (fun _ ↦ (extractQuery code B (TpIC.full hk c.idx c.cm)).bind fun tdm ↦
      (checks c.Wᶜ).map (fun b₂ ↦ (tdm, b₂))) true (some tdm, true)
  have h₂ := R.run₂_bind_record .instruments
    (extractQuery code B (TpIC.full hk c.idx c.cm)) (fun _ ↦ checks c.Wᶜ) (some tdm) true
  refine h₁.trans ?_
  rw [h₂]
  rw [run₂_actualBatch io ME code, run₂_actualBatch io ME code]
  erw [run₂_extractQuery_branch (compressedVCOracle k X Y) ME code B]
  exact conj_kronecker_three (actualBatch io c.W c)
    (show Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ from
      extractProj ME (TpIC.full hk c.idx c.cm) tdm) (actualBatch io c.Wᶜ c)

/-- The opening and mismatch decision of the P4 challenger, conditional on the retained
check/extract/check transcript. Randomized openings and both budget checks are preserved. -/
noncomputable def offlineFinish [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (r : Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) :
    QComp (EmulatedOracle.cohSpec (extIn k X Y Cm Z)) B B Bool :=
  match r.2.1 with
  | none => QuantumComp₂.pure false
  | some tdm => (QComp.pi fun i : Fin k ↦
      openAt VC B i (c.ans i).dom (tdm i).2).bind fun pf' ↦
        QuantumComp₂.pure (r.1 && r.2.2 &&
          decide (∃ i : Fin k, ¬ PartialVec.Agrees (tdm i).1 (c.ans i) ∨ pf' i ≠ c.pf i) &&
          decide (∑ i, (c.ans i).dom.card ≤ qs) && decide (Function.Injective c.idx))

/-- The actual P4 challenger is the retained prefix followed by its opening/mismatch decision.
This is an equality of programs, including rejected checks and decoding failure. -/
theorem offlineChallenger_eq_bind_offlineChecks [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    offlineChallenger VC code hk qs c B =
      QuantumComp₂.bind (offlineChecks (VC := VC) code hk c B)
        (offlineFinish (VC := VC) (Z := Z) hk qs c B) := by
  simp only [offlineChallenger, offlineChecks, QuantumComp₂.map,
    QuantumComp₂.bind_assoc]
  congr 1
  funext b₁
  erw [QuantumComp₂.bind_assoc, QuantumComp₂.bind_assoc]
  simp only [QuantumComp₂.pure_bind]
  congr 1
  funext tdm
  erw [QuantumComp₂.bind_assoc]
  congr 1
  funext b₂
  erw [QuantumComp₂.pure_bind]
  cases tdm <;> rfl

/-- The actual P4 challenger instrument retaining its check/extraction transcript alongside
the final mismatch-event bit. Forgetting the transcript recovers `offlineChallenger`. -/
noncomputable def offlineInstrument [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    QComp (EmulatedOracle.cohSpec (extIn k X Y Cm Z)) B B
      ((Bool × Option (TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) × Bool) × Bool) :=
  (offlineChecks (VC := VC) code hk c B).bind fun r ↦
    (offlineFinish (VC := VC) (Z := Z) hk qs c B r).map fun b ↦ (r, b)

/-- Forgetting the retained transcript gives exactly the original P4 challenger. -/
theorem offlineInstrument_map_snd [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg) :
    (offlineInstrument (VC := VC) code hk qs c B).map Prod.snd =
      offlineChallenger VC code hk qs c B := by
  rw [offlineInstrument, QuantumRuntime.bind_record_map_snd,
    offlineChallenger_eq_bind_offlineChecks code]

/-- The retained P4 branch equals its opening/mismatch decision after
`conj(1 ⊗ A_b Π_tdm A_a)`. This instrument equality keeps the extraction outcome and final
event bit, allows randomized openings, and holds on arbitrary entangled input matrices. -/
theorem run₂_offlineInstrument_accept [DecidableEq Msg] [∀ i, DecidableEq (Pf i)]
    [∀ i, DecidableEq (DmOf ℓ Msg Td i)]
    (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (compressedVCOracle k X Y).S)
    (hk : 1 ≤ k) (qs : ℕ) (c : OpeningClaim k Cm Msg ℓ Pf) (B : QReg)
    (tdm : TpDLen k (DmOf ℓ Msg Td) (TupleLen.full hk)) (b : Bool) :
    let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
    (R.run₂ .instruments (offlineInstrument (VC := VC) code hk qs c B)).branch
      ((true, some tdm, true), b) =
      (R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z) hk qs c B
        (true, some tdm, true))).branch b ∘ₗ
          MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
            (actualBatch io c.Wᶜ c *
              (show Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ from
                extractProj ME (TpIC.full hk c.idx c.cm) tdm) * actualBatch io c.W c)) := by
  let R := ((compressedVCOracle k X Y).withExtract ME code).coherent.toRuntime
  have hh := R.run₂_bind_record .instruments (offlineChecks (VC := VC) code hk c B)
    (offlineFinish (VC := VC) (Z := Z) hk qs c B) (true, some tdm, true) b
  exact hh.trans (congrArg (fun F ↦
    (R.run₂ .instruments (offlineFinish (VC := VC) (Z := Z) hk qs c B
      (true, some tdm, true))).branch b ∘ₗ F)
        (run₂_offlineChecks_accept io code ME hk c B tdm))

end retained
end Quantum

namespace Quantum
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]

omit [Fintype S] in
/-- Conjunctions of coordinate predicates factor into diagonal coordinate operators. -/
theorem diagonal_batch_piKron (p : ι → S → Prop) [∀ i s, Decidable (p i s)]
    (idx : ι → ι) (W : Finset ι) :
    diagonal (fun D : ι → S ↦ if ∀ i ∈ W, p i (D (idx i)) then (1 : ℂ) else 0) =
      piKron (fun j ↦ diagonal fun s ↦ if ∀ i ∈ W, idx i = j → p i s then 1 else 0) := by
  classical
  ext D D'
  by_cases h : D = D'
  · subst D'
    simp only [diagonal_apply_eq, piKron_apply, Finset.prod_boole,
      Finset.mem_univ, forall_const]
    congr 1
    exact propext ⟨fun h j i hi he ↦ he ▸ h i hi, fun h i hi ↦ h (idx i) i hi rfl⟩
  · rw [diagonal_apply_ne _ h, piKron_apply]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [diagonal_apply_ne _ hj])).symm

/-- A conjugated batch has zero entries between tables differing outside its indices. -/
theorem conjugated_batch_support (p : ι → S → Prop) [∀ i s, Decidable (p i s)]
    (idx : ι → ι) (W : Finset ι) (C : Matrix S S ℂ) (hC : C * C = 1)
    (D D' : ι → S)
    (h : (piKron (fun _ : ι ↦ C) * diagonal
      (fun D : ι → S ↦ if ∀ i ∈ W, p i (D (idx i)) then (1 : ℂ) else 0) *
        piKron (fun _ : ι ↦ C)) D D' ≠ 0) (j : ι) (hj : j ∉ W.image idx) :
    D j = D' j := by
  classical
  rw [diagonal_batch_piKron, piKron_mul, piKron_mul, piKron_apply] at h
  have hp : (diagonal (fun s : S ↦ if ∀ i ∈ W, idx i = j → p i s then (1 : ℂ) else 0)) = 1 := by
    have he : ∀ i ∈ W, idx i ≠ j := by simpa using hj
    have hx : ∀ s, ∀ i ∈ W, idx i = j → p i s :=
      fun _ i hi hh ↦ (he i hi hh).elim
    ext a b
    simp only [diagonal_apply, one_apply, ite_eq_left (hx a)]
  have hh := (Finset.prod_ne_zero_iff.mp h) j (Finset.mem_univ j)
  rw [hp, Matrix.mul_one, hC, one_apply] at hh
  split_ifs at hh with he
  · exact he
  · exact (hh rfl).elim

/-- A label-controlled response commutes with a matrix preserving its database label. -/
theorem response_commute_of_support {Z κ : Type*} [Fintype Z] [DecidableEq Z]
    (β : S → κ) (U : κ → Matrix Z Z ℂ) (K : Matrix S S ℂ)
    (hK : ∀ a b, K a b ≠ 0 → β a = β b) :
    Commute (labelControlled (fun a : S × Z ↦ β a.1)
      (fun r ↦ (1 : Matrix S S ℂ) ⊗ₖ U r)) (K ⊗ₖ (1 : Matrix Z Z ℂ)) := by
  classical
  have hp : pinch (fun a : S × Z ↦ β a.1) (K ⊗ₖ (1 : Matrix Z Z ℂ)) = K ⊗ₖ 1 := by
    rw [pinch_kronecker_one, pinch_eq_self_iff.mpr hK]
  change _ * _ = _ * _
  rw [← hp]
  apply labelControlled_mul_pinch
  · intro r a b hab
    have h : a.1 = b.1 := by
      by_contra hh
      exact hab (by simp [kroneckerMap_apply, one_apply_ne hh])
    exact congrArg β h
  · intro r
    simp only [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
end Quantum
