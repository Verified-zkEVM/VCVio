/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.ClassicalRepeatability
public import VCVio.Quantum.VC.Proof.Extraction

/-!
# Exact replay for the compressed oracle

The old compressed oracle satisfies Definition 10.3(2) of Chiesa, Di, Hu and Zheng,
ePrint 2025/2166, on every state. Its classical answer projector includes the bottom
sector for answer zero, as in FIX.md §10, equation (31). The projectors are conjugated
diagonal lookup events; this proves completeness, orthogonality, commutation and exact
replay without a validity hypothesis. The independent finite matrix example at the end
checks the nonprojectivity of the Hadamard extension discussed in FIX.md (14), (32).
-/

public section

open Matrix
open scoped Kronecker

universe uL vL w

namespace Quantum
namespace ProjectiveClassicalAnswers

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  {E : EmulatedOracle P In} {X Y : Type} [Fintype Y] [DecidableEq Y]
  (H : ProjectiveClassicalAnswers E X Y)

/-- Transcript projectors commute through general quantum programs that coherently choose
ordinary ports. This lifts portwise commutation without assuming a classical port schedule. -/
theorem commute_coherent_run {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {B : QReg} (prog : QuantumComp L (EmulatedOracle.cohSpec In) W B)
    (leaf : Σ u, W u) (tr : List (X × Y)) :
    (E.coherent.toRuntime.run I prog).branch leaf ∘ₗ H.transcriptBranch B tr =
      H.transcriptBranch leaf.1 tr ∘ₗ (E.coherent.toRuntime.run I prog).branch leaf := by
  have hs := QuantumRuntime.simulation (R₁ := E.coherent.toRuntime)
    (R₂ := E.coherent.toRuntime) (V := MatrixMap.conj (H.projector tr)) I
    (fun p r ↦ ?_) prog leaf
  · simpa only [MatrixMap.amplifyLeft_conj, transcriptBranch] using hs
  · cases p
    rw [E.coherent.toRuntime_step_branch, MatrixMap.amplifyLeft_conj]
    simp only [← MatrixMap.conj_mul]
    rw [EmulatedOracle.coherent_U_mul_one_kronecker E E (H.projector tr)
      (fun p ↦ H.ordinary_commute_projector p tr)]

/-- Exact replay after any quantum program using coherent ordinary ports. The full joint
subnormalized branch is preserved on each possibly register-dependent final leaf. -/
theorem replay_after_coherent_run {L : LocalSig.{uL, vL}} (I : L.Interp)
    {W : QReg → Type w} {B : QReg} (prog : QuantumComp L (EmulatedOracle.cohSpec In) W B)
    (leaf : Σ u, W u) (tr : List (X × Y)) :
    H.transcriptBranch leaf.1 tr ∘ₗ (E.coherent.toRuntime.run I prog).branch leaf ∘ₗ
        H.transcriptBranch B tr =
      (E.coherent.toRuntime.run I prog).branch leaf ∘ₗ H.transcriptBranch B tr := by
  rw [← LinearMap.comp_assoc, ← H.commute_coherent_run I prog leaf tr,
    LinearMap.comp_assoc, H.replay_transcript]

end ProjectiveClassicalAnswers

namespace CompressedReplay

section conjugation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Multiplication of operators conjugated by an involution. -/
theorem conjugate_mul (C : Matrix S S ℂ) (hC : C * C = 1) (D F : Matrix S S ℂ) :
    (C * D * C) * (C * F * C) = C * (D * F) * C := by
  calc
    _ = C * D * (C * C) * F * C := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hC, Matrix.mul_one]; simp only [Matrix.mul_assoc]

end conjugation

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The old answer projector, expressed by lookup in the decompressed basis. -/
noncomputable def answer (x : Fin k × X) (y : Y) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y *
    diagonal (fun D ↦ if (D x.1).lookup x.2 = y then 1 else 0) * compressDatabases k X Y

/-- Filled-label projector in the compressed basis, the `Q` term of FIX (31). -/
noncomputable def filled (x : Fin k × X) (y : Y) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y *
    diagonal (fun D ↦ if D x.1 x.2 = some y then 1 else 0) * compressDatabases k X Y

/-- Bottom-sector projector in the compressed basis, the `R` term of FIX (31). -/
noncomputable def invalid (x : Fin k × X) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y *
    diagonal (fun D ↦ if D x.1 x.2 = none then 1 else 0) * compressDatabases k X Y

/-- FIX (31): the zero answer includes the invalid sector on all private states. -/
theorem old_answer_projector (x : Fin k × X) (y : Y) :
    answer x y = filled x y + if y = 0 then invalid x else 0 := by
  have hd : (diagonal fun D : Fin k → Database X Y ↦
        if (D x.1).lookup x.2 = y then (1 : ℂ) else 0) =
      (diagonal fun D ↦ if D x.1 x.2 = some y then 1 else 0) +
        if y = 0 then (diagonal fun D ↦ if D x.1 x.2 = none then 1 else 0) else 0 := by
    ext D D'
    by_cases h : D = D'
    · subst D'
      simp only [diagonal_apply_eq, Matrix.add_apply]
      cases he : D x.1 x.2 <;> by_cases hy : y = 0 <;>
        simp [Database.lookup_apply, he, hy, eq_comm]
    · by_cases hy : y = 0 <;> simp [hy, h]
  unfold answer filled invalid
  rw [hd]
  split_ifs
  · rw [Matrix.mul_add, Matrix.add_mul]
  · simp only [add_zero]

/-- Every old answer projector is Hermitian. -/
theorem answer_hermitian (x : Fin k × X) (y : Y) : (answer x y)ᴴ = answer x y := by
  simp only [answer, conjTranspose_mul, conjTranspose_compressDatabases,
    conjTranspose_diagonal_ite, Matrix.mul_assoc]

/-- Orthogonality of distinct old answers, with idempotency for equal answers. -/
theorem answer_orthogonal (x : Fin k × X) (z y : Y) :
    answer x z * answer x y = if z = y then answer x y else 0 := by
  rw [answer, answer, conjugate_mul _ (compressDatabases_mul_self ..),
    diagonal_ite_mul_diagonal_ite]
  by_cases h : z = y
  · subst z
    simp only [and_self, ↓reduceIte]
  · have hd : (diagonal fun D : Fin k → Database X Y ↦
        if (D x.1).lookup x.2 = z ∧ (D x.1).lookup x.2 = y then (1 : ℂ) else 0) = 0 := by
      ext D D'
      simp only [diagonal_apply, Matrix.zero_apply]
      split_ifs with hD hc
      · exact False.elim (h (hc.1.symm.trans hc.2))
      all_goals rfl
    rw [hd]
    simp [h]

/-- Old classical answers resolve the identity, with no reachable-state restriction. -/
theorem answer_complete (x : Fin k × X) : ∑ y : Y, answer x y = 1 := by
  have hd : (∑ y : Y, diagonal fun D : Fin k → Database X Y ↦
      if (D x.1).lookup x.2 = y then (1 : ℂ) else 0) = 1 := by
    ext D D'
    by_cases h : D = D'
    · subst D'
      simp [Matrix.sum_apply, eq_comm]
    · simp [Matrix.sum_apply, h]
  simp only [answer, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hd, Matrix.mul_one, compressDatabases_mul_self]

/-- All old answer projectors commute, including at different oracle indices. -/
theorem answer_commute (x x' : Fin k × X) (y y' : Y) :
    answer x y * answer x' y' = answer x' y' * answer x y := by
  simp only [answer, conjugate_mul _ (compressDatabases_mul_self ..),
    diagonal_ite_mul_diagonal_ite]
  simp only [and_comm]

/-- The classical basis-call branch of the old oracle on an arbitrary reference register. -/
theorem branch_eq (B : QReg) (x : Fin k × X) (y : Y) :
    ((compressedVCOracle k X Y).toRuntime.run₂ .instruments
      (QComp.callBasis x.1 B (x.2, 0) (fun o _ ↦ o.2))).branch y =
        MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ answer x y) := by
  have hb (t : X) (z : Y) :
      (compressedVCOracle k X Y).block x.1 (t, z) (x.2, 0) =
        compressDatabases k X Y *
          diagonal (fun D : Fin k → Database X Y ↦
            if t = x.2 ∧ (D x.1).lookup x.2 = z then 1 else 0) *
          compressDatabases k X Y := by
    ext d d'
    have h := congrFun (congrFun (submatrix_one_kronecker_mul_mul_one_kronecker
      (compressDatabases k X Y) (tableOracle fun D : Fin k → Database X Y ↦ (D x.1).lookup)
      ((t, z) : X × Y) ((x.2, 0) : X × Y)) d) d'
    rw [submatrix_tableOracle] at h
    exact (congrFun (congrFun (compressedVCOracle_U_eq_conj x.1) _) _).trans h
  rw [EmulatedOracle.branch_run₂_callBasis, Finset.sum_eq_single (x.2, y)]
  · simp only [↓reduceIte, hb, true_and]
    rfl
  · rintro ⟨t, z⟩ _ hne
    by_cases hz : z = y
    · subst z
      have ht : t ≠ x.2 := fun h ↦ hne (by simp [h])
      have hzero : (compressedVCOracle k X Y).block x.1 (t, y) (x.2, 0) = 0 := by
        rw [hb]
        change (compressDatabases k X Y *
          diagonal (fun D : Fin k → Database X Y ↦
            if t = x.2 ∧ (D x.1).lookup x.2 = y then 1 else 0) *
          compressDatabases k X Y : Matrix (Fin k → Database X Y) _ ℂ) = 0
        simp [ht]
      simp only [↓reduceIte, hzero, kronecker_zero, MatrixMap.conj_zero]
    · simp [hz]
  · simp

/-- An old answer projector commutes with every ordinary query on a separate call register. -/
theorem answer_commute_ordinary (p : Fin k) (x : Fin k × X) (y : Y) :
    (show Matrix ((X × Y) × (Fin k → Database X Y))
      ((X × Y) × (Fin k → Database X Y)) ℂ from (compressedVCOracle k X Y).U p) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ answer x y) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ answer x y) *
        (show Matrix ((X × Y) × (Fin k → Database X Y))
          ((X × Y) × (Fin k → Database X Y)) ℂ from (compressedVCOracle k X Y).U p) := by
  let C := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressDatabases k X Y
  let D : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
    diagonal fun d ↦ if (d x.1).lookup x.2 = y then 1 else 0
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
  have hA : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ answer x y =
      C * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ D) * C := by
    simp [C, D, answer, ← mul_kronecker_mul]
  rw [compressedVCOracle_U_eq_conj, hA]
  change (C * _ * C) * (C * _ * C) = (C * _ * C) * (C * _ * C)
  rw [conjugate_mul C hCC, conjugate_mul C hCC, hT]

/-- The old compressed oracle has complete projective classical answers on all states.
The generic API supplies fixed-coin adaptive replay and rejection of contradictory lists. -/
noncomputable def projectiveClassicalAnswers :
    ProjectiveClassicalAnswers (compressedVCOracle k X Y) (Fin k × X) Y where
  query x := ⟨x.1, (x.2, 0)⟩
  read _ o := o.2
  A := answer
  branch_eq := branch_eq
  hermitian := answer_hermitian
  orthogonal := answer_orthogonal
  complete := answer_complete
  commute_cells x y x' y' := answer_commute x x' y y'
  commute_ordinary := answer_commute_ordinary

end CompressedReplay

/-! ## An independent Hadamard counterexample -/

namespace HadamardReplayCounterexample

/-- A four-answer Hadamard branch in the decompressed five-sector basis. The first four
coordinates are the filled labels and the last is bottom. FIX (14) gives coefficient
`1 / sqrt 4 = 1/2` on bottom for each answer, whereas the old port assigns it only to zero. -/
noncomputable def kraus (y : Fin 4) : Matrix (Fin 5) (Fin 5) ℂ :=
  diagonal fun i ↦ if i = 4 then 1 / 2 else if i.val = y.val then 1 else 0

/-- These four branch matrices form a complete quantum instrument. -/
theorem kraus_complete : ∑ y : Fin 4, (kraus y)ᴴ * kraus y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kraus, Matrix.sum_apply, Fin.sum_univ_succ, diagonal_conjTranspose,
      diagonal_mul_diagonal, Matrix.one_apply, map_ofNat]

/-- The four-answer Hadamard instrument on the filled and bottom sectors. -/
noncomputable def instrument : SubInstrument (Fin 5) (Fin 5) (Fin 4) :=
  SubInstrument.ofKraus kraus kraus_complete

/-- The Hadamard branch matrix is not idempotent, hence is not a projector. -/
theorem kraus_not_projective (y : Fin 4) : kraus y * kraus y ≠ kraus y := by
  intro h
  have he := congrFun (congrFun h 4) 4
  norm_num [kraus, diagonal_mul_diagonal] at he

/-- Its Kraus map is not idempotent either: the bottom matrix has weights `1/4` then `1/16`.
This rules out projective-answer certificates even if a different Kraus representation is used. -/
theorem branch_not_repeatable (y : Fin 4) :
    MatrixMap.conj (kraus y) ∘ₗ MatrixMap.conj (kraus y) ≠ MatrixMap.conj (kraus y) := by
  intro h
  have he := congrFun (congrFun (LinearMap.congr_fun h
    (diagonal fun i : Fin 5 ↦ if i = 4 then (1 : ℂ) else 0)) 4) 4
  norm_num [MatrixMap.conj_apply, LinearMap.comp_apply, kraus, diagonal_mul_diagonal,
    diagonal_conjTranspose, map_ofNat] at he

/-- The complete Hadamard instrument fails the necessary branch identity of the
projective-answer API, independently of any compressed-oracle implementation. -/
theorem instrument_not_repeatable (y : Fin 4) :
    instrument.branch y ∘ₗ instrument.branch y ≠ instrument.branch y := by
  have hb : instrument.branch y = MatrixMap.conj (kraus y) :=
    SubInstrument.branch_ofKraus_apply _ _ _
  rw [hb]
  exact branch_not_repeatable y

end HadamardReplayCounterexample
end Quantum
