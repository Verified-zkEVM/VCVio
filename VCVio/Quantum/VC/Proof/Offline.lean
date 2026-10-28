/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.CollisionRuntime
public import VCVio.Quantum.VC.Proof.Commutativity

/-!
# Collision potentials for families of compressed oracles

The collision event in Chiesa, Di, Hu and Zheng, ePrint 2025/2166, §9.3,
Lemma 9.6 (pp. 61–65), admits a bound with coefficient `7/4` using a charged quadratic
population potential. Extraction and recording preserve the databases and incur no charge.

`collisionEvent_compressedVCOracle_le` bounds the final event that at least one database
contains two distinct keys with the same answer by `(7t+5)t min(w,t)/(4|Y|)`.
`collisionEvent_compressedWithExtract_le` gives the same bound without a recording port.
In each execution, `w` is its actual ordinary query mass and `t` counts all calls.
Both statements allow arbitrary local instruments, coherent port superpositions,
zero queries, and subnormalized initial workspace states.

`familyPopulation` sums the per-database potentials. Each ordinary-query block isolates
one database; the other potentials are nonincreasing spectator scalars. The local
operator inequalities and the empty-database initialization supply the runtime certificate.
-/

public section

open Matrix Quantum.EmulatedOracle
open scoped Kronecker ComplexOrder ENNReal

namespace Quantum

section algebra

variable {J M B : Type*} [DecidableEq J] [DecidableEq M] [DecidableEq B]

/-- A diagonal operator decomposes into diagonal blocks along any register splitting. -/
theorem liftBlocks_diagonal (e : J ≃ M × B) (f : J → ℂ) :
    liftBlocks e (fun b ↦ diagonal fun m ↦ f (e.symm (m, b))) = diagonal f := by
  rw [liftBlocks, blockDiagonal_diagonal, submatrix_diagonal_equiv]
  congr 1
  funext j
  exact congrArg f (e.symm_apply_apply j)

omit [DecidableEq J] [DecidableEq M] in
/-- A constant lifted block is the operator on the selected factor. -/
theorem liftBlocks_const (e : J ≃ M × B) (A : Matrix M M ℂ) :
    liftBlocks e (fun _ ↦ A) = onFactor e A := by
  ext j j'
  simp only [liftBlocks, submatrix_apply, blockDiagonal_apply, onFactor_apply]


variable [Fintype J] [Fintype M] [Finite B]

private theorem liftBlocks_certificate (e : J ≃ M × B) (U P P' Q : Matrix M M ℂ)
    (θ r : ℝ)
    (h : (chargedDrop U P P' θ).PosSemidef ∧
      (r • chargedDrop U P P' θ - (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef) :
    let F := fun A : Matrix M M ℂ ↦ liftBlocks e (fun _ ↦ A)
    (chargedDrop (F U) (F P) (F P') θ).PosSemidef ∧
      (r • chargedDrop (F U) (F P) (F P') θ -
        (F Q * F U - F U * F Q)ᴴ * (F Q * F U - F U * F Q)).PosSemidef := by
  let u := fun _ : B ↦ U
  let p := fun _ : B ↦ P
  let p' := fun _ : B ↦ P'
  let q := fun _ : B ↦ Q
  have hd : (liftBlocks e (p + θ • 1 - (fun b ↦ (u b)ᴴ) * p' * u)).PosSemidef :=
    posSemidef_liftBlocks e (fun _ ↦ h.1)
  have hl : (liftBlocks e (r • (p + θ • 1 - (fun b ↦ (u b)ᴴ) * p' * u) -
      (fun b ↦ ((q * u - u * q) b)ᴴ) * (q * u - u * q))).PosSemidef :=
    posSemidef_liftBlocks e (fun _ ↦ h.2)
  simp only [liftBlocks_sub, liftBlocks_add, liftBlocks_smul, liftBlocks_one,
    liftBlocks_mul] at hd hl
  rw [liftBlocks_adjoint e u] at hd hl
  rw [liftBlocks_adjoint e (q * u - u * q)] at hl
  simp only [liftBlocks_sub, liftBlocks_mul] at hl
  exact ⟨hd, hl⟩

private theorem frame_database {A D R : Type*} [DecidableEq A] [DecidableEq R]
    (P : Matrix D D ℂ) :
    liftBlocks (Equiv.prodAssoc A D R).symm (fun _ ↦ (1 : Matrix A A ℂ) ⊗ₖ P) =
      (1 : Matrix A A ℂ) ⊗ₖ (P ⊗ₖ (1 : Matrix R R ℂ)) := by
  ext ⟨a, d, r⟩ ⟨a', d', r'⟩
  simp only [liftBlocks, submatrix_apply, blockDiagonal_apply, kroneckerMap_apply,
    Equiv.prodAssoc_symm_apply, one_apply]
  split_ifs <;> simp_all

private theorem diagonalIdle_bounds {A S : Type*} [Fintype A] [Fintype S]
    [DecidableEq A] [DecidableEq S] (U : Matrix (A × S) (A × S) ℂ)
    (hunit : Uᴴ * U = 1) (f g : S → ℝ) (q : S → ℂ)
    (hfg : ∀ s, g s ≤ f s)
    (hp : (1 ⊗ₖ diagonal (fun s ↦ (g s : ℂ))) * U =
      U * (1 ⊗ₖ diagonal (fun s ↦ (g s : ℂ))))
    (hq : (1 ⊗ₖ diagonal q) * U = U * (1 ⊗ₖ diagonal q)) :
    (chargedDrop U (1 ⊗ₖ diagonal (fun s ↦ (f s : ℂ)))
      (1 ⊗ₖ diagonal (fun s ↦ (g s : ℂ))) 0).PosSemidef ∧
      (1 ⊗ₖ diagonal q) * U - U * (1 ⊗ₖ diagonal q) = 0 := by
  refine ⟨?_, sub_eq_zero.mpr hq⟩
  rw [chargedDrop, zero_smul, add_zero, conjTranspose_mul_mul_eq_of_commute hunit hp]
  simp only [← diagonal_one, diagonal_kronecker_diagonal, diagonal_sub, one_mul]
  apply PosSemidef.diagonal
  intro a
  simpa only [Pi.zero_apply, ← Complex.ofReal_sub, Complex.zero_le_real] using
    sub_nonneg.mpr (hfg a.2)

private theorem diagonal_basis_zero {S : Type*} [Fintype S] [DecidableEq S]
    (s : S) (f : S → ℂ) (hf : f s = 0) :
    diagonal f * (SubState.basis s).matrix = 0 := by
  rw [SubState.matrix_basis]
  ext a b
  rw [diagonal_mul, Matrix.single_apply]
  split_ifs with h
  · rw [← h.1, hf, zero_mul]
    rfl
  · simp

private theorem initial_zero_of_gram {S A : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] (K Q P : Matrix S S ℂ) (hgram : Kᴴ * K = P)
    (s : S) (hq : Q * (SubState.basis s).matrix = 0)
    (hp : P * (SubState.basis s).matrix = 0) (ρ : Matrix A A ℂ) :
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) (ρ ⊗ₖ (SubState.basis s).matrix) = 0 ∧
      QuantumRuntime.potential K (ρ ⊗ₖ (SubState.basis s).matrix) = 0 := by
  constructor
  · rw [MatrixMap.conj_apply, ← mul_kronecker_mul, hq, kronecker_zero, Matrix.zero_mul]
  · rw [QuantumRuntime.potential_eq, hgram, ← mul_kronecker_mul, hp,
      kronecker_zero, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]

end algebra

section family

variable {k : ℕ} {X Y : Type} [Fintype X]

/-- Sum of the charged potentials of the individual databases; records are excluded. -/
@[expose]
noncomputable def familyPopulation (t n : ℕ) (D : Fin k → Database X Y) : ℝ :=
  ∑ i, collisionPotential t n (D i).size

/-- The family potential is nonnegative. -/
theorem familyPopulation_nonneg (t n : ℕ) (D : Fin k → Database X Y) :
    0 ≤ familyPopulation t n D :=
  Finset.sum_nonneg fun _ _ ↦ collisionPotential_nonneg _ _ _

/-- Idle operations can only decrease the family potential. -/
theorem familyPopulation_idle {t n : ℕ} (hn : n < t) (D : Fin k → Database X Y) :
    familyPopulation t (n + 1) D ≤ familyPopulation t n D :=
  Finset.sum_le_sum fun _ _ ↦ collisionPotential_idle hn _

/-- Splitting the family potential isolates the selected database and a spectator scalar. -/
theorem familyPopulation_split (t n : ℕ) (i : Fin k) (d : Database X Y)
    (r : {j // j ≠ i} → Database X Y) :
    familyPopulation t n ((Equiv.funSplitAt i (Database X Y)).symm (d, r)) =
      collisionPotential t n d.size + ∑ j, collisionPotential t n (r j).size := by
  rw [familyPopulation, Fintype.sum_eq_add_sum_subtype_ne _ i]
  simp only [Equiv.funSplitAt_symm_apply, dite_true]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by simp [j.property]

section baseOperators

variable [DecidableEq Y]

/-- The family collision event on the ordinary/extraction private register. -/
@[expose]
noncomputable def familyCollisionProjector :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  labelProjector Database.allCollisionLabel true

/-- The charged family population schedule on the ordinary/extraction private register. -/
@[expose]
noncomputable def extractPopulationMatrix (t n : ℕ) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  diagonal (fun D ↦ (familyPopulation t n D : ℂ))

/-- Square root of the charged population schedule without a recording register. -/
@[expose]
noncomputable def extractPotentialFactor (t n : ℕ) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  diagonal (fun D ↦ (Real.sqrt (familyPopulation t n D) : ℂ))

variable [DecidableEq X] [Fintype Y]

/-- The square-root schedule has the prescribed population Gram matrix. -/
private theorem extractPotentialFactor_gram (t n : ℕ) :
    (extractPotentialFactor (k := k) (X := X) (Y := Y) t n)ᴴ * extractPotentialFactor t n =
      extractPopulationMatrix t n := by
  rw [extractPotentialFactor, diagonal_conjTranspose, diagonal_mul_diagonal,
    extractPopulationMatrix]
  congr 1
  funext D
  change star (Real.sqrt (familyPopulation t n D) : ℂ) *
    (Real.sqrt (familyPopulation t n D) : ℂ) = (familyPopulation t n D : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (familyPopulation_nonneg t n D)]

end baseOperators

variable {R : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq R]

/-- Split an ordinary query, one database, and all the spectator registers. -/
@[expose]
def recordSplit (i : Fin k) :
    (X × Y) × ((Fin k → Database X Y) × R) ≃
      ((X × Y) × Database X Y) × (({j // j ≠ i} → Database X Y) × R) :=
  (Equiv.prodAssoc _ _ _).symm.trans
    ((Equiv.prodCongr (splitAt (X × Y) (Database X Y) i) (Equiv.refl R)).trans
      (Equiv.prodAssoc _ _ _))

/-- The operator of the family potential on the database and recording registers. -/
@[expose]
noncomputable def familyPopulationMatrix (t n : ℕ) :
    Matrix ((Fin k → Database X Y) × R) ((Fin k → Database X Y) × R) ℂ :=
  extractPopulationMatrix (k := k) (X := X) (Y := Y) t n ⊗ₖ (1 : Matrix R R ℂ)

/-- The event that some database has a collision, ignoring the recording registers. -/
@[expose]
noncomputable def familyCollisionMatrix :
    Matrix ((Fin k → Database X Y) × R) ((Fin k → Database X Y) × R) ℂ :=
  familyCollisionProjector (k := k) (X := X) (Y := Y) ⊗ₖ (1 : Matrix R R ℂ)

omit [DecidableEq X] in
private theorem familyPopulationMatrix_diagonal (t n : ℕ) :
    familyPopulationMatrix (k := k) (X := X) (Y := Y) (R := R) t n =
      diagonal (fun d ↦ (familyPopulation t n d.1 : ℂ)) := by
  simp only [familyPopulationMatrix, extractPopulationMatrix, ← diagonal_one,
    diagonal_kronecker_diagonal, mul_one]

omit [DecidableEq X] in
private theorem familyCollisionMatrix_diagonal :
    familyCollisionMatrix (k := k) (X := X) (Y := Y) (R := R) =
      labelProjector (fun d ↦ Database.allCollisionLabel d.1) true := by
  simp only [familyCollisionMatrix, familyCollisionProjector, labelProjector, ← diagonal_one,
    diagonal_kronecker_diagonal, mul_one]

omit [DecidableEq X] in
/-- Recording registers are spectators to the canonical family collision event. -/
theorem familyCollisionMatrix_eq_kronecker {R : Type} [DecidableEq R] :
    familyCollisionMatrix (k := k) (X := X) (Y := Y) (R := R) =
      familyCollisionProjector (k := k) (X := X) (Y := Y) ⊗ₖ (1 : Matrix R R ℂ) := rfl

/-- The blocks of the family potential are a database potential plus an idle scalar. -/
theorem familyPopulationMatrix_blocks (t n : ℕ) (i : Fin k) :
    (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        familyPopulationMatrix (k := k) (X := X) (Y := Y) (R := R) t n =
      liftBlocks (recordSplit i) (fun r ↦
        (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ populationMatrix t n 0 +
        (∑ j, collisionPotential t n (r.1 j).size) • 1) := by
  rw [familyPopulationMatrix_diagonal, ← diagonal_one, diagonal_kronecker_diagonal]
  simp only [one_mul]
  rw [← liftBlocks_diagonal (recordSplit i)]
  congr 1
  funext r
  rw [populationMatrix, diagonal_kronecker_diagonal, ← diagonal_one,
    ← diagonal_smul, diagonal_add]
  congr 1
  funext m
  change (familyPopulation t n ((Equiv.funSplitAt i (Database X Y)).symm (m.2, r.1)) : ℂ) = _
  rw [familyPopulation_split]
  simp [Complex.real_smul]

/-- The family collision projector has one database-label projector in each spectator block. -/
theorem familyCollisionMatrix_blocks (i : Fin k) :
    (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        familyCollisionMatrix (k := k) (X := X) (Y := Y) (R := R) =
      liftBlocks (recordSplit i) (fun r ↦ (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        labelProjector (fun d ↦ Database.allCollisionLabel
          ((Equiv.funSplitAt i (Database X Y)).symm (d, r.1))) true) := by
  rw [familyCollisionMatrix_diagonal, labelProjector, ← diagonal_one, diagonal_kronecker_diagonal]
  simp only [one_mul]
  rw [← liftBlocks_diagonal (recordSplit i)]
  congr 1
  funext r
  rw [labelProjector, diagonal_kronecker_diagonal]
  congr 1
  funext m
  simp only [one_mul]
  rfl

omit [Fintype X] [DecidableEq X] [DecidableEq Y] [DecidableEq R] in
/-- The register splitting selects the queried database and leaves all spectators together. -/
@[simp]
theorem recordSplit_apply (i : Fin k) (xy : X × Y) (d : Fin k → Database X Y) (r : R) :
    recordSplit i (xy, (d, r)) = ((xy, d i), ((fun j ↦ d j.1), r)) := rfl

variable [Fintype Y] [AddCommGroup Y] [Fintype R]

omit [Fintype R] in
/-- The ordinary port with an added recording register has constant compressed-oracle blocks. -/
theorem ordinaryRecordUnitary_blocks (i : Fin k) :
    Matrix.reindex (Equiv.prodAssoc _ _ R) (Equiv.prodAssoc _ _ R)
        ((compressedVCOracle k X Y).U i ⊗ₖ (1 : Matrix R R ℂ)) =
      liftBlocks (recordSplit i) (fun _ ↦ compressedOracle X Y) := by
  rw [liftBlocks_const]
  change Matrix.reindex (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) R)
    (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) R)
    (onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y) ⊗ₖ
      (1 : Matrix R R ℂ)) = _
  ext ⟨xy', d', r'⟩ ⟨xy, d, r⟩
  change onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)
      (xy', d') (xy, d) * (1 : Matrix R R ℂ) r' r =
    onFactor (recordSplit i) (compressedOracle X Y) (xy', (d', r')) (xy, (d, r))
  rw [onFactor_apply, onFactor_apply, one_apply]
  simp only [splitAt_apply, recordSplit_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

omit [DecidableEq Y] [AddCommGroup Y] in
/-- The collision label in a spectator block has the required changing-answer bound. -/
theorem familyCollision_block_count (i : Fin k) (r : {j // j ≠ i} → Database X Y)
    (x : X) (d : Database X Y) (hd : d x = none) :
    (binaryFlipSet (fun a ↦ Database.allCollisionLabel
      ((Equiv.funSplitAt i (Database X Y)).symm (Function.update d x a, r)))).card ≤
      0 + d.size := by
  have he (a : Option Y) := (update_funSplitAt_symm i (Function.update d x a) d r).symm
  simp_rw [he]
  simpa only [zero_add] using Database.card_allCollisionFlipSet_le
    ((Equiv.funSplitAt i (Database X Y)).symm (d, r)) i hd

omit [DecidableEq R] [Fintype R] in
private theorem familyOrdinaryBlock_bounds {t n : ℕ} (hn : n < t) (i : Fin k)
    (r : ({j // j ≠ i} → Database X Y) × R) :
    let P := fun j ↦ (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ populationMatrix j.1 j.2 0 +
      (∑ l, collisionPotential j.1 j.2 (r.1 l).size) • 1
    let Q := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ labelProjector
      (fun d ↦ Database.allCollisionLabel
        ((Equiv.funSplitAt i (Database X Y)).symm (d, r.1))) true
    let U := compressedOracle X Y
    (chargedDrop U (P (t, n)) (P (t, n + 1)) ((t : ℝ) / 2)).PosSemidef ∧
      (collisionRate t n (Fintype.card Y) • chargedDrop U (P (t, n))
        (P (t, n + 1)) ((t : ℝ) / 2) - (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef := by
  apply posSemidef_chargedDrop_add_scalar
    (Matrix.mem_unitaryGroup_iff'.mp (compressedOracle_mem_unitaryGroup (X := X) (Y := Y)))
  · exact Finset.sum_le_sum fun j _ ↦ collisionPotential_idle hn _
  · exact collisionRate_nonneg t n (by positivity)
  · exact posSemidef_compressedPopulationDrop hn 0
  · exact posSemidef_compressedPopulationLeak hn 0 _ (familyCollision_block_count i r.1)

omit [DecidableEq R] [Fintype R] in
private theorem baseOrdinary_bounds {t n : ℕ} (hn : n < t) (i : Fin k) :
    let U : Matrix ((X × Y) × (Fin k → Database X Y))
      ((X × Y) × (Fin k → Database X Y)) ℂ := (compressedVCOracle k X Y).U i
    let P := fun j ↦ (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      extractPopulationMatrix (k := k) (X := X) (Y := Y) t j
    let Q := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ familyCollisionProjector (k := k) (X := X) (Y := Y)
    let Δ := chargedDrop U (P n) (P (n + 1)) ((t : ℝ) / 2)
    Δ.PosSemidef ∧ (collisionRate t n (Fintype.card Y) • Δ -
      (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef := by
  classical
  let e := splitAt (X × Y) (Database X Y) i
  let P (j : ℕ) (r : {l // l ≠ i} → Database X Y) :=
    (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      populationMatrix (X := X) (Y := Y) t j 0 +
        (∑ l, collisionPotential t j (r l).size) • 1
  let U (_ : {l // l ≠ i} → Database X Y) := compressedOracle X Y
  let Q (r : {l // l ≠ i} → Database X Y) :=
    (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ labelProjector
      (fun d ↦ Database.allCollisionLabel
        ((Equiv.funSplitAt i (Database X Y)).symm (d, r))) true
  have hp (j : ℕ) : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      extractPopulationMatrix (k := k) (X := X) (Y := Y) t j = liftBlocks e (P j) := by
    rw [extractPopulationMatrix, ← diagonal_one, diagonal_kronecker_diagonal]
    simp only [one_mul]
    rw [← liftBlocks_diagonal e]
    congr 1
    funext r
    simp only [P, populationMatrix, ← diagonal_one, diagonal_kronecker_diagonal,
      ← diagonal_smul, diagonal_add]
    congr 1
    funext a
    change (familyPopulation t j
        ((Equiv.funSplitAt i (Database X Y)).symm (a.2, r)) : ℂ) =
      1 * (collisionPotential t j (0 + a.2.size) : ℂ) +
        (∑ l, collisionPotential t j (r l).size) • (1 : ℂ)
    rw [familyPopulation_split]
    simp only [one_mul, zero_add, Complex.ofReal_add, Complex.real_smul, mul_one]
  have hq : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      familyCollisionProjector (k := k) (X := X) (Y := Y) = liftBlocks e Q := by
    change (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      labelProjector Database.allCollisionLabel true = _
    rw [labelProjector, ← diagonal_one,
      diagonal_kronecker_diagonal]
    simp only [one_mul]
    rw [← liftBlocks_diagonal e]
    congr 1
    funext r
    simp only [Q, labelProjector, ← diagonal_one, diagonal_kronecker_diagonal, one_mul]
    rfl
  have hu : (compressedVCOracle k X Y).U i =
      liftBlocks e U := by
    rw [liftBlocks_const]
    rfl
  have hb (r : {l // l ≠ i} → Database X Y) :=
    familyOrdinaryBlock_bounds (R := Unit) hn i (r, ())
  have hd : (liftBlocks e (P n + ((t : ℝ) / 2) • 1 -
      (fun r ↦ (U r)ᴴ) * P (n + 1) * U)).PosSemidef :=
    posSemidef_liftBlocks e (fun r ↦ (hb r).1)
  have hl : (liftBlocks e (collisionRate t n (Fintype.card Y) •
      (P n + ((t : ℝ) / 2) • 1 - (fun r ↦ (U r)ᴴ) * P (n + 1) * U) -
        (fun r ↦ ((Q * U - U * Q) r)ᴴ) * (Q * U - U * Q))).PosSemidef :=
    posSemidef_liftBlocks e (fun r ↦ (hb r).2)
  simp only [liftBlocks_sub, liftBlocks_add, liftBlocks_smul, liftBlocks_one,
    liftBlocks_mul] at hd hl
  rw [liftBlocks_adjoint e U] at hd hl
  rw [liftBlocks_adjoint e (Q * U - U * Q)] at hl
  simp only [liftBlocks_sub, liftBlocks_mul] at hl
  dsimp only
  rw [hu]
  rw [← hp, ← hp] at hd hl
  rw [← hq] at hl
  exact ⟨hd, hl⟩

private theorem recordedOrdinary_bounds {t n : ℕ} (hn : n < t) (i : Fin k) :
    let U := liftBlocks (recordSplit (X := X) (Y := Y) (R := R) i)
      (fun _ ↦ compressedOracle X Y)
    let P := fun j ↦ (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      familyPopulationMatrix (k := k) (X := X) (Y := Y) (R := R) t j
    let Q := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ familyCollisionMatrix
    let Δ := chargedDrop U (P n) (P (n + 1)) ((t : ℝ) / 2)
    Δ.PosSemidef ∧ (collisionRate t n (Fintype.card Y) • Δ -
      (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef := by
  have h := liftBlocks_certificate (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) R).symm
    _ _ _ _ ((t : ℝ) / 2) (collisionRate t n (Fintype.card Y)) (baseOrdinary_bounds hn i)
  dsimp only at h
  rw [frame_database, frame_database, frame_database] at h
  have hu : liftBlocks (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) R).symm
      (fun _ ↦ (compressedVCOracle k X Y).U i) =
      liftBlocks (recordSplit i) (fun _ ↦ compressedOracle X Y) := by
    calc
      _ = Matrix.reindex (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) R)
          (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) R)
          ((compressedVCOracle k X Y).U i ⊗ₖ (1 : Matrix R R ℂ)) := by
        ext ⟨a, d, r⟩ ⟨a', d', r'⟩
        change (if r = r' then (compressedVCOracle k X Y).U i (a, d) (a', d') else 0) =
          (compressedVCOracle k X Y).U i (a, d) (a', d') * (if r = r' then 1 else 0)
        split_ifs <;> simp
      _ = _ := ordinaryRecordUnitary_blocks (X := X) (Y := Y) (R := R) i
  rw [hu] at h
  exact h

/-- The charged drop on the family of databases is nonnegative for every ordinary selector. -/
theorem posSemidef_familyOrdinaryDrop {t n : ℕ} (hn : n < t) (i : Fin k) :
    (chargedDrop (liftBlocks (recordSplit (X := X) (Y := Y) (R := R) i)
      (fun _ ↦ compressedOracle X Y))
      (1 ⊗ₖ familyPopulationMatrix t n) (1 ⊗ₖ familyPopulationMatrix t (n + 1))
      ((t : ℝ) / 2)).PosSemidef := by
  exact (recordedOrdinary_bounds (R := R) hn i).1

/-- The family collision leak is dominated by the charged drop on an ordinary selector. -/
theorem posSemidef_familyOrdinaryLeak {t n : ℕ} (hn : n < t) (i : Fin k) :
    let U := liftBlocks (recordSplit (X := X) (Y := Y) (R := R) i)
      (fun _ ↦ compressedOracle X Y)
    let Q := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ familyCollisionMatrix
    (collisionRate t n (Fintype.card Y) • chargedDrop U
      (1 ⊗ₖ familyPopulationMatrix t n) (1 ⊗ₖ familyPopulationMatrix t (n + 1))
      ((t : ℝ) / 2) - (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef := by
  exact (recordedOrdinary_bounds (R := R) hn i).2

omit [AddCommGroup Y] in
/-- Any interface preserving the databases commutes with database-diagonal operators. -/
theorem commute_familyDiagonal {A : Type*} [Fintype A] [DecidableEq A]
    (U : Matrix (A × ((Fin k → Database X Y) × R))
      (A × ((Fin k → Database X Y) × R)) ℂ)
    (hU : ∀ a b, U a b ≠ 0 → a.2.1 = b.2.1) (f : (Fin k → Database X Y) → ℂ) :
    ((1 : Matrix A A ℂ) ⊗ₖ diagonal (fun d ↦ f d.1)) * U =
      U * ((1 : Matrix A A ℂ) ⊗ₖ diagonal (fun d ↦ f d.1)) := by
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  ext a b
  rw [diagonal_mul, mul_diagonal]
  by_cases hab : U a b = 0
  · simp [hab]
  · rw [hU a b hab]
    ring

omit [AddCommGroup Y] in
/-- An interface preserving databases has nonnegative uncharged drop and zero collision leak. -/
theorem familyIdle_bounds {A : Type*} [Fintype A] [DecidableEq A]
    (U : Matrix (A × ((Fin k → Database X Y) × R))
      (A × ((Fin k → Database X Y) × R)) ℂ) (hunit : Uᴴ * U = 1)
    (hU : ∀ a b, U a b ≠ 0 → a.2.1 = b.2.1) {t n : ℕ} (hn : n < t) :
    (chargedDrop U (1 ⊗ₖ familyPopulationMatrix t n)
      (1 ⊗ₖ familyPopulationMatrix t (n + 1)) 0).PosSemidef ∧
    (1 ⊗ₖ familyCollisionMatrix) * U - U * (1 ⊗ₖ familyCollisionMatrix) = 0 := by
  rw [familyPopulationMatrix_diagonal, familyPopulationMatrix_diagonal,
    familyCollisionMatrix_diagonal]
  exact diagonalIdle_bounds U hunit
    (fun d ↦ familyPopulation t n d.1) (fun d ↦ familyPopulation t (n + 1) d.1)
    (fun d ↦ if Database.allCollisionLabel d.1 = true then 1 else 0)
    (fun d ↦ familyPopulation_idle hn d.1)
    (commute_familyDiagonal U hU (fun d ↦ (familyPopulation t (n + 1) d : ℂ)))
    (commute_familyDiagonal U hU (fun d ↦ if Database.allCollisionLabel d = true then 1 else 0))

/-- The diagonal square root factors the family population operator. -/
@[expose]
noncomputable def familyPotentialFactor (t n : ℕ) :
    Matrix ((Fin k → Database X Y) × R) ((Fin k → Database X Y) × R) ℂ :=
  extractPotentialFactor (k := k) (X := X) (Y := Y) t n ⊗ₖ (1 : Matrix R R ℂ)

omit [AddCommGroup Y] in
/-- The Gram matrix of the population factor is the population operator. -/
theorem familyPotentialFactor_gram (t n : ℕ) :
    (familyPotentialFactor (k := k) (X := X) (Y := Y) (R := R) t n)ᴴ *
      familyPotentialFactor t n = familyPopulationMatrix t n := by
  rw [familyPotentialFactor, conjTranspose_kronecker, ← mul_kronecker_mul,
    extractPotentialFactor_gram, conjTranspose_one, Matrix.one_mul]
  rfl

omit [DecidableEq X] [DecidableEq Y] [Fintype Y] [AddCommGroup Y] in
/-- The empty family has zero initial potential. -/
theorem familyPopulation_empty (t : ℕ) :
    familyPopulation (k := k) (X := X) (Y := Y) t 0 (fun _ ↦ Database.empty) = 0 := by
  simp [familyPopulation, collisionPotential]

end family

section extractionAlgebra

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] {Dm : Fin k → Type} [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Cm] [DecidableEq Cm]
  [Fintype Z] [DecidableEq Z] [AddGroup Z]
  (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)

/-- Extraction preserves every event determined by the compressed databases. -/
theorem extractUnitary_commute_diagonal (f : (Fin k → Database X Y) → ℂ) :
    ((1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ diagonal f) *
        extractUnitary ME code =
      extractUnitary ME code * ((1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ
        diagonal f) := by
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  ext a b
  rw [diagonal_mul, mul_diagonal]
  by_cases h : extractUnitary ME code a b = 0
  · simp [h]
  · have hD : a.2 = b.2 := by
      rw [extractUnitary_apply] at h
      split_ifs at h with he
      · exact he.2.2
      · exact False.elim (h rfl)
    simp only [one_mul, hD]
    ring

end extractionAlgebra

section interfaces

variable {k : ℕ} {X Y Cm Z Yr Cell : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm]
  [Fintype Z] [DecidableEq Z] [AddGroup Z] [Fintype Yr] [DecidableEq Yr]
  [Fintype Cell] [DecidableEq Cell] {Dm : Fin k → Type}
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]
  (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)
  (bot : Cell) (V : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hV : V ∈ unitaryGroup _ ℂ)

/-- The extraction port with a recording register leaves every database entry unchanged. -/
theorem withRecord_extract_preserves_databases
    (a b : (TpIC k Cm × Z) × ((Fin k → Database X Y) × RecReg k Cm Dm Cell))
    (h : ((compressedVCOracle k X Y).withRecord ME code bot V hV).U
      (.inl (.inr ())) a b ≠ 0) : a.2.1 = b.2.1 := by
  change extractUnitary ME code (a.1, a.2.1) (b.1, b.2.1) *
    (1 : Matrix (RecReg k Cm Dm Cell) (RecReg k Cm Dm Cell) ℂ) a.2.2 b.2.2 ≠ 0 at h
  have he := left_ne_zero_of_mul h
  rw [extractUnitary_apply] at he
  split_ifs at he with hh
  · exact hh.2.2
  · exact False.elim (he rfl)

/-- The recording port leaves every database entry unchanged. -/
theorem withRecord_record_preserves_databases
    (a b : (TpIC k Cm × Yr) × ((Fin k → Database X Y) × RecReg k Cm Dm Cell))
    (h : ((compressedVCOracle k X Y).withRecord ME code bot V hV).U
      (.inr ()) a b ≠ 0) : a.2.1 = b.2.1 := by
  classical
  unfold VCOracle.withRecord EmulatedOracle.extend at h
  change recordUnitary (S := Fin k → Database X Y) V a b ≠ 0 at h
  rw [recordUnitary, cellControlled, labelControlled_apply] at h
  simp only [onFactor, Matrix.reindex_apply, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply, one_apply] at h
  split_ifs at h with he
  · exact congrArg (fun z ↦ z.2.1) he
  · exact False.elim (h (mul_zero _))

/-- Select the ordinary compressed-oracle ports among extraction and recording ports. -/
@[expose]
def ordinaryPort : (Fin k ⊕ Unit) ⊕ Unit → Bool
  | .inl (.inl _) => true
  | _ => false

/-- Selecting the ordinary ports gives exactly the sum of their actual total query masses. -/
theorem selectedTotalMass_ordinaryPort {In : ((Fin k ⊕ Unit) ⊕ Unit) → QReg}
    (E : EmulatedOracle ((Fin k ⊕ Unit) ⊕ Unit) In) {L : LocalSig} (I : L.Interp)
    {W : QReg → Type*} {A : QReg} (x : QuantumComp L (cohSpec In) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) :
    E.selectedTotalMass I ordinaryPort x ρ = ∑ i, E.totalMass I x ρ (.inl (.inl i)) := by
  simp [selectedTotalMass, Fintype.sum_sum_type, ordinaryPort]

/-- All ports satisfy the collision drop and leak inequalities, charging only ordinary ports. -/
theorem withRecord_port_bounds {t n : ℕ} (hn : n < t) (p : (Fin k ⊕ Unit) ⊕ Unit) :
    let U : Matrix (recIn k X Y Cm Z Yr p ×
        ((Fin k → Database X Y) × RecReg k Cm Dm Cell))
      (recIn k X Y Cm Z Yr p × ((Fin k → Database X Y) × RecReg k Cm Dm Cell)) ℂ :=
        ((compressedVCOracle k X Y).withRecord ME code bot V hV).U p
    let P := fun j ↦ (1 : Matrix (recIn k X Y Cm Z Yr p) (recIn k X Y Cm Z Yr p) ℂ) ⊗ₖ
      familyPopulationMatrix (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell) t j
    let Q := (1 : Matrix (recIn k X Y Cm Z Yr p) (recIn k X Y Cm Z Yr p) ℂ) ⊗ₖ
      familyCollisionMatrix (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell)
    let Δ := chargedDrop U (P n) (P (n + 1))
      (if ordinaryPort p then (t : ℝ) / 2 else 0)
    Δ.PosSemidef ∧ (collisionRate t n (Fintype.card Y) • Δ -
      (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef := by
  classical
  rcases p with (i | u) | u
  · change
      let U := Matrix.reindex
          (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) (RecReg k Cm Dm Cell))
          (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) (RecReg k Cm Dm Cell))
          (onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y) ⊗ₖ
            (1 : Matrix (RecReg k Cm Dm Cell) (RecReg k Cm Dm Cell) ℂ))
      let P := fun j ↦ (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        familyPopulationMatrix (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell) t j
      let Q := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        familyCollisionMatrix (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell)
      (chargedDrop U (P n) (P (n + 1)) ((t : ℝ) / 2)).PosSemidef ∧
        (collisionRate t n (Fintype.card Y) • chargedDrop U (P n) (P (n + 1))
          ((t : ℝ) / 2) - (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef
    dsimp only
    have hu' : Matrix.reindex
        (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) (RecReg k Cm Dm Cell))
        (Equiv.prodAssoc (X × Y) (Fin k → Database X Y) (RecReg k Cm Dm Cell))
        (onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y) ⊗ₖ
          (1 : Matrix (RecReg k Cm Dm Cell) (RecReg k Cm Dm Cell) ℂ)) =
        liftBlocks (recordSplit i) (fun _ ↦ compressedOracle X Y) := by
      exact ordinaryRecordUnitary_blocks (X := X) (Y := Y) (R := RecReg k Cm Dm Cell) i
    rw [hu']
    exact ⟨posSemidef_familyOrdinaryDrop hn i, posSemidef_familyOrdinaryLeak hn i⟩
  · cases u
    have h := familyIdle_bounds (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell)
      (((compressedVCOracle k X Y).withRecord ME code bot V hV).U (.inl (.inr ())))
      (((compressedVCOracle k X Y).withRecord ME code bot V hV).conjTranspose_mul_self _)
      (withRecord_extract_preserves_databases ME code bot V hV) hn
    dsimp only [ordinaryPort, Bool.false_eq_true, ite_false]
    refine ⟨h.1, ?_⟩
    have hl := h.1.smul (collisionRate_nonneg t n (N := Fintype.card Y) (by positivity))
    simpa only [h.2, conjTranspose_zero, Matrix.zero_mul, sub_zero,
      Bool.false_eq_true, ite_false] using hl
  · cases u
    have h := familyIdle_bounds (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell)
      (((compressedVCOracle k X Y).withRecord ME code bot V hV).U (.inr ()))
      (((compressedVCOracle k X Y).withRecord ME code bot V hV).conjTranspose_mul_self _)
      (withRecord_record_preserves_databases ME code bot V hV) hn
    dsimp only [ordinaryPort, Bool.false_eq_true, ite_false]
    refine ⟨h.1, ?_⟩
    have hl := h.1.smul (collisionRate_nonneg t n (N := Fintype.card Y) (by positivity))
    simpa only [h.2, conjTranspose_zero, Matrix.zero_mul, sub_zero,
      Bool.false_eq_true, ite_false] using hl

/-- The record-world initial state has empty databases and constant recording cells. -/
theorem compressedWithRecord_init :
    ((compressedVCOracle k X Y).withRecord ME code bot V hV).init =
      SubState.basis ((fun _ : Fin k ↦ (Database.empty : Database X Y)), RecReg.const bot) := by
  change (SubState.basis (fun _ : Fin k ↦ (Database.empty : Database X Y))).prod
    (SubState.basis (RecReg.const bot)) = _
  exact SubState.basis_prod_basis _ _

/-- The collision event and the initial population potential both vanish initially. -/
theorem compressedWithRecord_initial_zero (t : ℕ) {A : QReg} (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withRecord ME code bot V hV
    let Q := familyCollisionMatrix (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell)
    let K := familyPotentialFactor (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell)
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) (ρ.matrix ⊗ₖ E.init.matrix) = 0 ∧
      QuantumRuntime.potential (K t 0) (ρ.matrix ⊗ₖ E.init.matrix) = 0 := by
  classical
  let d : (Fin k → Database X Y) × RecReg k Cm Dm Cell :=
    ((fun _ ↦ Database.empty), RecReg.const bot)
  have hz := diagonal_basis_zero d
  have hq := hz (fun s ↦ if Database.allCollisionLabel s.1 = true then 1 else 0) (by
    simp [d, Database.allCollisionLabel, Database.allCollisionFree_empty])
  have hp := hz (fun s ↦ (familyPopulation t 0 s.1 : ℂ)) (by
    rw [familyPopulation_empty]; rfl)
  dsimp only
  rw [compressedWithRecord_init ME code bot V hV]
  apply initial_zero_of_gram _ _ _ (familyPotentialFactor_gram t 0) d
  · simpa only [familyCollisionMatrix_diagonal, labelProjector] using hq
  · simpa only [familyPopulationMatrix_diagonal] using hp

/-- The family collision event has weight at most `(7t+5)t min(w,t)/(4|Y|)` for
ordinary, extraction, and recording programs. The mass `w` counts only the ordinary ports,
while `t` counts all calls. The statement includes zero calls and subnormalized initial
workspace states. -/
theorem collisionEvent_compressedVCOracle_le {L : LocalSig} (I : L.Interp)
    {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (cohSpec (recIn k X Y Cm Z Yr)) W A)
    {t : ℕ} (hx : x.IsQueryBound (fun _ ↦ t)) (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withRecord ME code bot V hV
    let σ := ρ.matrix ⊗ₖ E.init.matrix
    let w := ∑ i : Fin k, E.totalMass I x σ (.inl (.inl i))
    E.coherent.toRuntime.eventWeight I
        (familyCollisionMatrix (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell)) x σ ≤
      ENNReal.ofReal ((7 * t + 5) * t / (4 * (Fintype.card Y : ℝ))) * min w t := by
  classical
  let E := (compressedVCOracle k X Y).withRecord ME code bot V hV
  let Q := familyCollisionMatrix (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell)
  let K := familyPotentialFactor (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell) t
  have hQ := isStarProjection_labelProjector (α := ℂ)
    (fun s : (Fin k → Database X Y) × RecReg k Cm Dm Cell ↦
      Database.allCollisionLabel s.1) true
  rw [← familyCollisionMatrix_diagonal] at hQ
  have hi := compressedWithRecord_initial_zero ME code bot V hV t ρ
  refine (E.eventWeight_le_collision_of_port_bounds I ordinaryPort Q hQ.isSelfAdjoint
    hQ.isIdempotentElem K (Fintype.card Y) (by positivity) ?_ x hx
    (ρ.prod E.init).posSemidef (ρ.prod E.init).trace_re_le_one hi.1 hi.2).trans_eq ?_
  · intro n hn p
    have h := withRecord_port_bounds ME code bot V hV hn p
    dsimp only at h
    rw [← familyPotentialFactor_gram, ← familyPotentialFactor_gram] at h
    exact h
  · exact congrArg (fun w : ℝ≥0∞ ↦ ENNReal.ofReal
      ((7 * t + 5) * t / (4 * (Fintype.card Y : ℝ))) * min w t)
      (selectedTotalMass_ordinaryPort E I x (ρ.matrix ⊗ₖ E.init.matrix))

end interfaces


section extractionCollision



variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm]
  [Fintype Z] [DecidableEq Z] [AddGroup Z] {Dm : Fin k → Type}
  (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)

/-- The ordinary/extraction ports obey the collision inequalities used by the recorded runtime,
with ordinary ports alone charged. The proof uses the same per-database blocks. -/
private theorem withExtract_collision_port_bounds {t n : ℕ} (hn : n < t) (p : Fin k ⊕ Unit) :
    let U : Matrix ((extIn k X Y Cm Z p) × (Fin k → Database X Y))
      ((extIn k X Y Cm Z p) × (Fin k → Database X Y)) ℂ :=
        ((compressedVCOracle k X Y).withExtract ME code).U p
    let P := fun j ↦ (1 : Matrix (extIn k X Y Cm Z p) (extIn k X Y Cm Z p) ℂ) ⊗ₖ
      extractPopulationMatrix (k := k) (X := X) (Y := Y) t j
    let Q := (1 : Matrix (extIn k X Y Cm Z p) (extIn k X Y Cm Z p) ℂ) ⊗ₖ
      familyCollisionProjector (k := k) (X := X) (Y := Y)
    let Δ := chargedDrop U (P n) (P (n + 1))
      (if p.isLeft then (t : ℝ) / 2 else 0)
    Δ.PosSemidef ∧ (collisionRate t n (Fintype.card Y) • Δ -
      (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef := by
  classical
  rcases p with i | u
  · exact baseOrdinary_bounds hn i
  · cases u
    let U := extractUnitary ME code
    let P := fun j ↦ (1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ
      extractPopulationMatrix (k := k) (X := X) (Y := Y) t j
    let Q := (1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ
      familyCollisionProjector (k := k) (X := X) (Y := Y)
    have hc (f : (Fin k → Database X Y) → ℂ) :=
      extractUnitary_commute_diagonal ME code f
    have hi := diagonalIdle_bounds U
      (mem_unitaryGroup_iff'.mp (extractUnitary_mem_unitaryGroup ME code))
      (familyPopulation t n) (familyPopulation t (n + 1))
      (fun d ↦ if Database.allCollisionLabel d = true then 1 else 0)
      (familyPopulation_idle hn) (hc _) (hc _)
    dsimp only
    change (chargedDrop U (P n) (P (n + 1)) 0).PosSemidef ∧
      (collisionRate t n (Fintype.card Y) • chargedDrop U (P n) (P (n + 1)) 0 -
        (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef
    rw [show Q * U - U * Q = 0 from hi.2, conjTranspose_zero, Matrix.zero_mul, sub_zero]
    exact ⟨hi.1, hi.1.smul (collisionRate_nonneg t n (by positivity))⟩

/-- Empty databases have zero collision weight and zero initial charged population. -/
private theorem compressedWithExtract_initial_zero (t : ℕ) {A : QReg} (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withExtract ME code
    let Q := familyCollisionProjector (k := k) (X := X) (Y := Y)
    let K := extractPotentialFactor (k := k) (X := X) (Y := Y) t 0
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) (ρ.matrix ⊗ₖ E.init.matrix) = 0 ∧
      QuantumRuntime.potential K (ρ.matrix ⊗ₖ E.init.matrix) = 0 := by
  classical
  let D : Fin k → Database X Y := fun _ ↦ Database.empty
  have hz := diagonal_basis_zero D
  have hq := hz (fun D ↦ if Database.allCollisionLabel D = true then 1 else 0)
    (by simp [D, Database.allCollisionLabel, Database.allCollisionFree_empty])
  have hp := hz (fun D ↦ (familyPopulation t 0 D : ℂ))
    (by rw [familyPopulation_empty]; rfl)
  dsimp only
  change MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ familyCollisionProjector)
      (ρ.matrix ⊗ₖ (SubState.basis D).matrix) = 0 ∧
    QuantumRuntime.potential (extractPotentialFactor t 0)
      (ρ.matrix ⊗ₖ (SubState.basis D).matrix) = 0
  exact initial_zero_of_gram _ _ _ (extractPotentialFactor_gram t 0) D hq hp ρ.matrix

/-- The collision event on ordinary/extraction prefixes has weight at most
`(7t+5)t min(w,t)/(4|Y|)`. All calls count towards `t`, including extraction, while `w`
is the actual ordinary mass. Arbitrary coherent programs and substates are allowed. -/
theorem collisionEvent_compressedWithExtract_le {L : LocalSig} (I : L.Interp)
    {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (cohSpec (extIn k X Y Cm Z)) W A)
    {t : ℕ} (hx : x.IsQueryBound (fun _ ↦ t)) (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withExtract ME code
    let σ := ρ.matrix ⊗ₖ E.init.matrix
    let w := ∑ i : Fin k, E.totalMass I x σ (.inl i)
    E.coherent.toRuntime.eventWeight I
        (familyCollisionProjector (k := k) (X := X) (Y := Y)) x σ ≤
      ENNReal.ofReal ((7 * t + 5) * t / (4 * (Fintype.card Y : ℝ))) * min w t := by
  classical
  let E := (compressedVCOracle k X Y).withExtract ME code
  let Q := familyCollisionProjector (k := k) (X := X) (Y := Y)
  let K := extractPotentialFactor (k := k) (X := X) (Y := Y) t
  have hQ := isStarProjection_labelProjector (α := ℂ)
    (fun D : Fin k → Database X Y ↦ Database.allCollisionLabel D) true
  have hi := compressedWithExtract_initial_zero ME code t ρ
  refine (E.eventWeight_le_collision_of_port_bounds I Sum.isLeft Q
    hQ.isSelfAdjoint hQ.isIdempotentElem K (Fintype.card Y) (by positivity) ?_ x hx
    (ρ.prod E.init).posSemidef (ρ.prod E.init).trace_re_le_one hi.1 hi.2).trans_eq ?_
  · intro n hn p
    have h := withExtract_collision_port_bounds ME code hn p
    dsimp only at h
    rw [← extractPotentialFactor_gram, ← extractPotentialFactor_gram] at h
    exact h
  · congr 2
    simp only [selectedTotalMass, Fintype.sum_sum_type, Sum.isLeft_inl,
      Sum.isLeft_inr, ite_true, Bool.false_eq_true, ite_false, Finset.sum_const_zero, add_zero]
    rfl


end extractionCollision

end Quantum
