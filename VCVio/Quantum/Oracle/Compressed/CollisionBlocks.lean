/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.Collision

/-!
# Lifting the collision potential through query blocks

This file assembles the one-cell inequalities of bounds-note (NOTE) equations (77), (78),
(87)–(89), (91), formalizing NOTE's refinement of ePrint 2025/2166 §9.3's collision-event
argument (Lemma 9.6, p. 61; event bound, pp. 64–65).
The population counts database entries only.
-/

public section

open Matrix
open scoped Kronecker ComplexOrder

namespace Quantum

section blockAlgebra

variable {J M B : Type*} [DecidableEq B]

/-- Lift context-dependent blocks to the original register through an equivalence. -/
@[expose]
def liftBlocks (e : J ≃ M × B) (A : B → Matrix M M ℂ) : Matrix J J ℂ :=
  (blockDiagonal A).submatrix e e

/-- Lifting blocks preserves addition. -/
theorem liftBlocks_add (e : J ≃ M × B) (A C : B → Matrix M M ℂ) :
    liftBlocks e (A + C) = liftBlocks e A + liftBlocks e C := by
  simp only [liftBlocks, blockDiagonal_add, submatrix_add]
  rfl

/-- Lifting blocks preserves subtraction. -/
theorem liftBlocks_sub (e : J ≃ M × B) (A C : B → Matrix M M ℂ) :
    liftBlocks e (A - C) = liftBlocks e A - liftBlocks e C := by
  simp only [liftBlocks, blockDiagonal_sub, submatrix_sub]
  rfl

/-- Lifting blocks preserves real scalar multiplication. -/
theorem liftBlocks_smul (e : J ≃ M × B) (r : ℝ) (A : B → Matrix M M ℂ) :
    liftBlocks e (r • A) = r • liftBlocks e A := by
  simp only [liftBlocks, blockDiagonal_smul, submatrix_smul]
  rfl

/-- Lifting blocks preserves multiplication. -/
theorem liftBlocks_mul [Fintype J] [Fintype M] [Finite B] (e : J ≃ M × B) (A C : B → Matrix M M ℂ) :
    liftBlocks e (A * C) = liftBlocks e A * liftBlocks e C := by
  let := Fintype.ofFinite B
  change (blockDiagonal (fun b ↦ A b * C b)).submatrix e e = _
  rw [blockDiagonal_mul, submatrix_mul _ _ e e e e.bijective]
  rfl

/-- Lifting constant identity blocks gives the identity. -/
theorem liftBlocks_one [DecidableEq J] [DecidableEq M] (e : J ≃ M × B) : liftBlocks e 1 = 1 := by
  simp only [liftBlocks, blockDiagonal_one, submatrix_one_equiv]

/-- Lifting blocks preserves adjoints. -/
theorem liftBlocks_adjoint (e : J ≃ M × B) (A : B → Matrix M M ℂ) :
    liftBlocks e (fun b ↦ (A b)ᴴ) = (liftBlocks e A)ᴴ := by
  simp only [liftBlocks, ← blockDiagonal_conjTranspose, conjTranspose_submatrix]

/-- Positive semidefinite blocks give a positive semidefinite lifted matrix. -/
theorem posSemidef_liftBlocks [Finite M] [Finite B] (e : J ≃ M × B) {A : B → Matrix M M ℂ}
    (hA : ∀ b, (A b).PosSemidef) : (liftBlocks e A).PosSemidef :=
  (posSemidef_blockDiagonal hA).submatrix e

end blockAlgebra

section pullback

variable {J M : Type*} [Fintype M]

/-- Pull back an operator along a change of orthonormal coordinates. -/
@[expose]
def operatorPullback (V : Matrix M J ℂ) (A : Matrix M M ℂ) : Matrix J J ℂ :=
  Vᴴ * A * V

/-- Operator pullback preserves addition. -/
theorem operatorPullback_add (V : Matrix M J ℂ) (A B : Matrix M M ℂ) :
    operatorPullback V (A + B) = operatorPullback V A + operatorPullback V B := by
  simp only [operatorPullback, Matrix.mul_add, Matrix.add_mul]

/-- Operator pullback preserves subtraction. -/
theorem operatorPullback_sub (V : Matrix M J ℂ) (A B : Matrix M M ℂ) :
    operatorPullback V (A - B) = operatorPullback V A - operatorPullback V B := by
  simp only [operatorPullback, Matrix.mul_sub, Matrix.sub_mul]

/-- Operator pullback preserves real scalar multiplication. -/
theorem operatorPullback_smul (V : Matrix M J ℂ) (r : ℝ) (A : Matrix M M ℂ) :
    operatorPullback V (r • A) = r • operatorPullback V A := by
  simp only [operatorPullback, Matrix.mul_smul, Matrix.smul_mul]

/-- Pullback along a coisometry preserves products. -/
theorem operatorPullback_mul [Fintype J] [DecidableEq M] (V : Matrix M J ℂ) (hV : V * Vᴴ = 1)
    (A B : Matrix M M ℂ) :
    operatorPullback V (A * B) = operatorPullback V A * operatorPullback V B := by
  unfold operatorPullback
  symm
  calc _ = Vᴴ * A * (V * Vᴴ) * B * V := by simp only [Matrix.mul_assoc]
    _ = _ := by simp only [hV, Matrix.mul_one, Matrix.mul_assoc]

/-- Pullback preserves adjoints. -/
theorem operatorPullback_adjoint (V : Matrix M J ℂ) (A : Matrix M M ℂ) :
    operatorPullback V Aᴴ = (operatorPullback V A)ᴴ := by
  simp only [operatorPullback, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Pullback along an isometry preserves the identity. -/
theorem operatorPullback_one [DecidableEq J] [DecidableEq M]
    (V : Matrix M J ℂ) (hV : Vᴴ * V = 1) : operatorPullback V 1 = 1 := by
  simpa only [operatorPullback, Matrix.mul_one] using hV

end pullback

section scalarPotential

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The charged drop of a potential across a unitary call. -/
@[expose]
noncomputable def chargedDrop (U A B : Matrix J J ℂ) (θ : ℝ) : Matrix J J ℂ :=
  A + θ • 1 - Uᴴ * B * U

/-- Adding scalar potentials adds their scalar decrease to the charged drop. -/
theorem chargedDrop_add_scalar (U A B : Matrix J J ℂ) (hU : Uᴴ * U = 1)
    (θ a b : ℝ) :
    chargedDrop U (A + a • 1) (B + b • 1) θ = chargedDrop U A B θ + (a - b) • 1 := by
  simp only [chargedDrop, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hU, sub_smul]
  abel

/-- A nonincreasing spectator scalar preserves a charged drop and its leak bound. -/
theorem posSemidef_chargedDrop_add_scalar {U A B C : Matrix J J ℂ} (hU : Uᴴ * U = 1)
    {θ a b r : ℝ} (hab : b ≤ a) (hr : 0 ≤ r)
    (hd : (chargedDrop U A B θ).PosSemidef)
    (hl : (r • chargedDrop U A B θ - Cᴴ * C).PosSemidef) :
    (chargedDrop U (A + a • 1) (B + b • 1) θ).PosSemidef ∧
    (r • chargedDrop U (A + a • 1) (B + b • 1) θ - Cᴴ * C).PosSemidef := by
  rw [chargedDrop_add_scalar U A B hU]
  have hs : ((a - b) • (1 : Matrix J J ℂ)).PosSemidef :=
    PosSemidef.one.smul (sub_nonneg.mpr hab)
  refine ⟨hd.add hs, ?_⟩
  convert hl.add (hs.smul hr) using 1
  rw [smul_add]
  abel

end scalarPotential

section split

variable {X Q Y : Type*} [DecidableEq X]

/-- The query, its phase, and the database outside the queried cell. -/
abbrev CellContext (X Q Y : Type*) :=
  Σ q : X × Q, {j // j ≠ q.1} → Option Y

/-- Separate the queried cell from the query and the remaining database. -/
@[expose]
def phaseCellSplit : (X × Q) × Database X Y ≃ Option Y × CellContext X Q Y where
  toFun m := (m.2 m.1.1, ⟨m.1, fun j ↦ m.2 j.1⟩)
  invFun a := (a.2.1, (Equiv.funSplitAt a.2.1.1 (Option Y)).symm (a.1, a.2.2))
  left_inv m := by
    refine Prod.ext ?_ ?_
    · rfl
    exact (Equiv.funSplitAt m.1.1 (Option Y)).symm_apply_apply m.2
  right_inv a := by
    obtain ⟨a, q, r⟩ := a
    have h := (Equiv.funSplitAt q.1 (Option Y)).apply_symm_apply (a, r)
    exact congrArg (fun z ↦ (z.1, (⟨q, z.2⟩ : CellContext X Q Y))) h

/-- Restore a cell context with the queried entry empty. -/
@[expose]
def CellContext.emptyDatabase (c : CellContext X Q Y) : Database X Y :=
  (Equiv.funSplitAt c.1.1 (Option Y)).symm (none, c.2)

/-- The restored empty context has an empty queried entry. -/
@[simp]
theorem CellContext.emptyDatabase_apply (c : CellContext X Q Y) :
    c.emptyDatabase c.1.1 = none := by simp [CellContext.emptyDatabase]

/-- Reconstructing a database from its cell and context is a single update. -/
theorem phaseCellSplit_symm_eq_update (a : Option Y) (c : CellContext X Q Y) :
    phaseCellSplit.symm (a, c) = (c.1, Function.update c.emptyDatabase c.1.1 a) := by
  refine Prod.ext ?_ ?_
  · rfl
  ext x
  by_cases hx : x = c.1.1
  · subst x
    simp [phaseCellSplit]
  · simp [phaseCellSplit, CellContext.emptyDatabase, Equiv.funSplitAt_symm_apply, hx]

end split

section phase

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- The phase oracle is the direct sum of its cell operators, indexed by cell contexts. -/
theorem phaseOracle_eq_cellBlocks :
    phaseOracle X Y = (blockDiagonal
      (fun c : CellContext X (AddChar Y ℂ) Y ↦ phaseCell Y c.1.2)).submatrix
        phaseCellSplit phaseCellSplit := by
  ext ⟨q', D'⟩ ⟨q, D⟩
  rw [phaseOracle_apply, submatrix_apply, blockDiagonal_apply]
  change (if q' = q ∧ ∀ j ≠ q.1, D' j = D j then _ else 0) =
    if (⟨q', fun j ↦ D' j.1⟩ : CellContext X (AddChar Y ℂ) Y) =
        ⟨q, fun j ↦ D j.1⟩ then _ else 0
  by_cases hq : q' = q
  · subst q'
    have he : (fun j : {j // j ≠ q.1} ↦ D' j.1) = (fun j ↦ D j.1) ↔
        ∀ j ≠ q.1, D' j = D j := by
      simp only [funext_iff, Subtype.forall]
    simp only [true_and, Sigma.mk.inj_iff, heq_eq_eq, true_and, he]
    rfl
  · have he : (⟨q', fun j ↦ D' j.1⟩ : CellContext X (AddChar Y ℂ) Y) ≠
        ⟨q, fun j ↦ D j.1⟩ := fun h ↦ hq (congrArg Sigma.fst h)
    simp [hq, he]

omit [Fintype Y] in
/-- A database-diagonal operator decomposes into the corresponding cell-diagonal blocks. -/
theorem one_kronecker_diagonal_eq_cellBlocks (f : Database X Y → ℂ) :
    (1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ diagonal f =
      (blockDiagonal (fun c : CellContext X (AddChar Y ℂ) Y ↦
        diagonal fun a ↦ f (Function.update c.emptyDatabase c.1.1 a))).submatrix
          phaseCellSplit phaseCellSplit := by
  rw [blockDiagonal_diagonal, submatrix_diagonal_equiv, ← diagonal_one,
    diagonal_kronecker_diagonal]
  apply congrArg diagonal
  funext m
  simp only [Function.comp_apply, one_mul]
  have h := phaseCellSplit_symm_eq_update (phaseCellSplit m).1 (phaseCellSplit m).2
  rw [phaseCellSplit.symm_apply_apply] at h
  exact congrArg (fun z ↦ f z.2) h

/-- The diagonal population potential, with an offset for the other databases. -/
@[expose]
noncomputable def populationMatrix (t n offset : ℕ) : Matrix (Database X Y) (Database X Y) ℂ :=
  diagonal fun D ↦ (collisionPotential t n (offset + D.size) : ℂ)

omit [Fintype Y] in
/-- The global population potential restricts to the two-level cell potential. -/
theorem populationMatrix_eq_cellBlocks (t n offset : ℕ) :
    (1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ
        populationMatrix (X := X) (Y := Y) t n offset =
      (blockDiagonal (fun c : CellContext X (AddChar Y ℂ) Y ↦
        collisionCellPotential Y t n (offset + c.emptyDatabase.size))).submatrix
          phaseCellSplit phaseCellSplit := by
  rw [populationMatrix, one_kronecker_diagonal_eq_cellBlocks]
  congr 2
  funext c
  apply congrArg diagonal
  funext a
  cases a with
  | none => simp [Database.update_none_of_eq_none]
  | some y =>
    simp [Database.size_update_some_of_eq_none c.emptyDatabase_apply, Nat.add_assoc]

/-- The population drop of one ordinary phase query is nonnegative after its charge. -/
theorem posSemidef_phasePopulationDrop {t n : ℕ} (hn : n < t) (offset : ℕ) :
    ((1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ
        populationMatrix (X := X) (Y := Y) t n offset + ((t : ℝ) / 2) • 1 -
      (phaseOracle X Y)ᴴ * (1 ⊗ₖ populationMatrix t (n + 1) offset) *
        phaseOracle X Y).PosSemidef := by
  let C := CellContext X (AddChar Y ℂ) Y
  let P (j : ℕ) (c : C) := collisionCellPotential Y t j (offset + c.emptyDatabase.size)
  let U (c : C) := phaseCell Y c.1.2
  have h (c : C) : (P n c + ((t : ℝ) / 2) • 1 - (U c)ᴴ * P (n + 1) c * U c).PosSemidef := by
    have h := posSemidef_collisionCellDrop c.1.2 hn (offset + c.emptyDatabase.size)
    have hp := posSemidef_cellDiag (Y := Y)
      (show (0 : ℝ) ≤ offset + c.emptyDatabase.size by positivity)
      (show (0 : ℝ) ≤ (t : ℝ) / (n + 1) * (offset + c.emptyDatabase.size + 1) by positivity)
    convert h.add hp using 1
    simp [P, U, C]
  let e := phaseCellSplit (X := X) (Q := AddChar Y ℂ) (Y := Y)
  have hb : (liftBlocks e (P n + ((t : ℝ) / 2) • 1 -
      (fun c ↦ (U c)ᴴ) * P (n + 1) * U)).PosSemidef :=
    posSemidef_liftBlocks e h
  rw [liftBlocks_sub, liftBlocks_add, liftBlocks_smul, liftBlocks_one,
    liftBlocks_mul, liftBlocks_mul, liftBlocks_adjoint] at hb
  rw [populationMatrix_eq_cellBlocks, populationMatrix_eq_cellBlocks, phaseOracle_eq_cellBlocks]
  exact hb

/-- The cell leak inequalities assemble into an operator inequality for the phase oracle.
The only event hypothesis is the combinatorial count of changing answers. -/
theorem posSemidef_phasePopulationLeak {t n : ℕ} (hn : n < t) (offset : ℕ)
    (q : Database X Y → Bool)
    (hq : ∀ (x : X) (r : Database X Y), r x = none →
      (binaryFlipSet (fun a ↦ q (Function.update r x a))).card ≤ offset + r.size) :
    (collisionRate t n (Fintype.card Y) •
        ((1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ
          populationMatrix (X := X) (Y := Y) t n offset + ((t : ℝ) / 2) • 1 -
          (phaseOracle X Y)ᴴ * (1 ⊗ₖ populationMatrix t (n + 1) offset) * phaseOracle X Y) -
      ((1 ⊗ₖ labelProjector q true) * phaseOracle X Y -
        phaseOracle X Y * (1 ⊗ₖ labelProjector q true))ᴴ *
      ((1 ⊗ₖ labelProjector q true) * phaseOracle X Y -
        phaseOracle X Y * (1 ⊗ₖ labelProjector q true))).PosSemidef := by
  let C := CellContext X (AddChar Y ℂ) Y
  let P (j : ℕ) (c : C) := collisionCellPotential Y t j (offset + c.emptyDatabase.size)
  let U (c : C) := phaseCell Y c.1.2
  let Q (c : C) : Matrix (Option Y) (Option Y) ℂ :=
    labelProjector (fun a ↦ q (Function.update c.emptyDatabase c.1.1 a)) true
  let r := collisionRate t n (Fintype.card Y)
  have hr : 0 ≤ r := collisionRate_nonneg t n (by positivity)
  have h (c : C) : (r • (P n c + ((t : ℝ) / 2) • 1 - (U c)ᴴ * P (n + 1) c * U c) -
      (Q c * U c - U c * Q c)ᴴ * (Q c * U c - U c * Q c)).PosSemidef := by
    have hd := (posSemidef_collisionCellDrop c.1.2 hn
      (offset + c.emptyDatabase.size)).smul hr
    have hl := posSemidef_collisionCellLeak c.1.2
      (binaryFlipSet (fun a ↦ q (Function.update c.emptyDatabase c.1.1 a))) hn
      (hq c.1.1 c.emptyDatabase c.emptyDatabase_apply)
    rw [show (Q c * U c - U c * Q c)ᴴ * (Q c * U c - U c * Q c) = _ from
      binaryCell_commutator_gram _ _]
    convert hd.add hl using 1
    simp only [smul_sub, P, U, r]
    abel
  let e := phaseCellSplit (X := X) (Q := AddChar Y ℂ) (Y := Y)
  have hb : (liftBlocks e (r • (P n + ((t : ℝ) / 2) • 1 -
      (fun c ↦ (U c)ᴴ) * P (n + 1) * U) -
      (fun c ↦ ((Q * U - U * Q) c)ᴴ) * (Q * U - U * Q))).PosSemidef :=
    posSemidef_liftBlocks e h
  simp only [liftBlocks_sub, liftBlocks_add, liftBlocks_smul, liftBlocks_one,
    liftBlocks_mul] at hb
  rw [liftBlocks_adjoint e U, liftBlocks_adjoint e (Q * U - U * Q)] at hb
  simp only [liftBlocks_sub, liftBlocks_mul] at hb
  have hQ : (1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ
      labelProjector q true = (blockDiagonal Q).submatrix phaseCellSplit phaseCellSplit :=
    one_kronecker_diagonal_eq_cellBlocks _
  rw [populationMatrix_eq_cellBlocks, populationMatrix_eq_cellBlocks,
    phaseOracle_eq_cellBlocks, hQ]
  exact hb

/-- The response Fourier transform leaves database operators unchanged under pullback. -/
theorem operatorPullback_queryFourier_database (A : Matrix (Database X Y) (Database X Y) ℂ) :
    operatorPullback (queryFourier X Y)
        ((1 : Matrix (X × AddChar Y ℂ) (X × AddChar Y ℂ) ℂ) ⊗ₖ A) =
      (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ A := by
  rw [operatorPullback, Matrix.mul_assoc, ← queryFourier_mul_one_kronecker,
    ← Matrix.mul_assoc, conjTranspose_queryFourier_mul, Matrix.one_mul]

/-- Pulling the phase oracle back gives the standard compressed oracle. -/
theorem operatorPullback_queryFourier_phaseOracle :
    operatorPullback (queryFourier X Y) (phaseOracle X Y) = compressedOracle X Y := by
  rw [operatorPullback, phaseOracle]
  simp only [Matrix.mul_assoc, conjTranspose_queryFourier_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, conjTranspose_queryFourier_mul, Matrix.one_mul]

/-- The charged population drop for the standard compressed oracle is positive semidefinite. -/
theorem posSemidef_compressedPopulationDrop {t n : ℕ} (hn : n < t) (offset : ℕ) :
    ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        populationMatrix (X := X) (Y := Y) t n offset + ((t : ℝ) / 2) • 1 -
      (compressedOracle X Y)ᴴ * (1 ⊗ₖ populationMatrix t (n + 1) offset) *
        compressedOracle X Y).PosSemidef := by
  have h := (posSemidef_phasePopulationDrop (X := X) (Y := Y) hn offset)
    |>.conjTranspose_mul_mul_same (queryFourier X Y)
  change (operatorPullback (queryFourier X Y) _).PosSemidef at h
  simp only [operatorPullback_sub, operatorPullback_add, operatorPullback_smul,
    operatorPullback_one _ (conjTranspose_queryFourier_mul X Y),
    operatorPullback_mul _ (queryFourier_mul_conjTranspose X Y), operatorPullback_adjoint,
    operatorPullback_queryFourier_database, operatorPullback_queryFourier_phaseOracle] at h
  exact h

/-- The population drop dominates collision leakage for the standard compressed oracle.
This supports NOTE's refinement of the paper's §9.3 collision-event argument
(Lemma 9.6, p. 61; event bound, pp. 64–65). -/
theorem posSemidef_compressedPopulationLeak {t n : ℕ} (hn : n < t) (offset : ℕ)
    (q : Database X Y → Bool)
    (hq : ∀ (x : X) (r : Database X Y), r x = none →
      (binaryFlipSet (fun a ↦ q (Function.update r x a))).card ≤ offset + r.size) :
    (collisionRate t n (Fintype.card Y) •
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
          populationMatrix (X := X) (Y := Y) t n offset + ((t : ℝ) / 2) • 1 -
          (compressedOracle X Y)ᴴ * (1 ⊗ₖ populationMatrix t (n + 1) offset) *
            compressedOracle X Y) -
      ((1 ⊗ₖ labelProjector q true) * compressedOracle X Y -
        compressedOracle X Y * (1 ⊗ₖ labelProjector q true))ᴴ *
      ((1 ⊗ₖ labelProjector q true) * compressedOracle X Y -
        compressedOracle X Y * (1 ⊗ₖ labelProjector q true))).PosSemidef := by
  have h := (posSemidef_phasePopulationLeak hn offset q hq)
    |>.conjTranspose_mul_mul_same (queryFourier X Y)
  change (operatorPullback (queryFourier X Y) _).PosSemidef at h
  simp only [operatorPullback_sub, operatorPullback_add, operatorPullback_smul,
    operatorPullback_one _ (conjTranspose_queryFourier_mul X Y),
    operatorPullback_mul _ (queryFourier_mul_conjTranspose X Y), operatorPullback_adjoint,
    operatorPullback_queryFourier_database, operatorPullback_queryFourier_phaseOracle] at h
  exact h

end phase

end Quantum
