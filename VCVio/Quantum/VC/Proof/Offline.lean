/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.CollisionRuntime
public import VCVio.Quantum.VC.Proof.Commutativity

/-!
# Collision potentials for the k compressed oracles

This file formalizes NOTE's refinement of the collision-event argument in ePrint 2025/2166
§9.3 (Lemma 9.6, p. 61; event bound, pp. 64–65). The paper uses
the size projection, Corollaries 5.8/5.6, and a coefficient-80 per-database bound.
Corollaries 5.6 and 5.8 appear on pp. 31 and 33.
The charged quadratic schedule and 7/4 coefficient come from the bounds note (NOTE
(77)–(78), (87)–(91), (107)). We sum its per-database potentials. Extraction and recording
preserve the databases, so their charge is zero.

`collisionEvent_compressedVCOracle_le` bounds the final event that at least one database
contains two distinct keys with the same answer by `(7t+5)t min(w,t)/(4|Y|)`. Its original
mass `w` is the sum of `EmulatedOracle.totalMass` over the ordinary ports. Programs may use
arbitrary local instruments and coherent port superpositions. The query bound includes
all ports, and the theorem includes zero queries and subnormalized initial states.

`familyPopulation` sums the per-database potentials, excluding records. The query block
isolates the selected database; all other potentials are nonincreasing spectator scalars.
`withRecord_port_bounds` proves the local operator conditions, and the square-root factor
and empty-database lemmas supply the runtime certificate without additional trace premises.
P4 and the full-response Hadamard extension are separate results.
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
  diagonal fun d ↦ (familyPopulation t n d.1 : ℂ)

/-- The event that some database has a collision, ignoring the recording registers. -/
@[expose]
noncomputable def familyCollisionMatrix :
    Matrix ((Fin k → Database X Y) × R) ((Fin k → Database X Y) × R) ℂ :=
  labelProjector (fun d ↦ Database.allCollisionLabel d.1) true

/-- The blocks of the family potential are a database potential plus an idle scalar. -/
theorem familyPopulationMatrix_blocks (t n : ℕ) (i : Fin k) :
    (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        familyPopulationMatrix (k := k) (X := X) (Y := Y) (R := R) t n =
      liftBlocks (recordSplit i) (fun r ↦
        (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ populationMatrix t n 0 +
        (∑ j, collisionPotential t n (r.1 j).size) • 1) := by
  rw [familyPopulationMatrix, ← diagonal_one, diagonal_kronecker_diagonal]
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
  rw [familyCollisionMatrix, labelProjector, ← diagonal_one, diagonal_kronecker_diagonal]
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

/-- The charged drop on the family of databases is nonnegative for every ordinary selector. -/
theorem posSemidef_familyOrdinaryDrop {t n : ℕ} (hn : n < t) (i : Fin k) :
    (chargedDrop (liftBlocks (recordSplit (X := X) (Y := Y) (R := R) i)
      (fun _ ↦ compressedOracle X Y))
      (1 ⊗ₖ familyPopulationMatrix t n) (1 ⊗ₖ familyPopulationMatrix t (n + 1))
      ((t : ℝ) / 2)).PosSemidef := by
  let B := ({j // j ≠ i} → Database X Y) × R
  let P (j : ℕ) (r : B) := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
    populationMatrix (X := X) (Y := Y) t j 0 +
    (∑ l, collisionPotential t j (r.1 l).size) • 1
  let U (_ : B) := compressedOracle X Y
  let e := recordSplit (X := X) (Y := Y) (R := R) i
  have hb : (liftBlocks e (P n + ((t : ℝ) / 2) • 1 -
      (fun b ↦ (U b)ᴴ) * P (n + 1) * U)).PosSemidef :=
    posSemidef_liftBlocks e (fun b ↦ (familyOrdinaryBlock_bounds hn i b).1)
  rw [liftBlocks_sub, liftBlocks_add, liftBlocks_smul, liftBlocks_one,
    liftBlocks_mul, liftBlocks_mul, liftBlocks_adjoint] at hb
  rw [chargedDrop, familyPopulationMatrix_blocks, familyPopulationMatrix_blocks]
  exact hb

/-- The family collision leak is dominated by the charged drop on an ordinary selector. -/
theorem posSemidef_familyOrdinaryLeak {t n : ℕ} (hn : n < t) (i : Fin k) :
    let U := liftBlocks (recordSplit (X := X) (Y := Y) (R := R) i)
      (fun _ ↦ compressedOracle X Y)
    let Q := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ familyCollisionMatrix
    (collisionRate t n (Fintype.card Y) • chargedDrop U
      (1 ⊗ₖ familyPopulationMatrix t n) (1 ⊗ₖ familyPopulationMatrix t (n + 1))
      ((t : ℝ) / 2) - (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef := by
  let B := ({j // j ≠ i} → Database X Y) × R
  let P (j : ℕ) (r : B) := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
    populationMatrix (X := X) (Y := Y) t j 0 +
    (∑ l, collisionPotential t j (r.1 l).size) • 1
  let U (_ : B) := compressedOracle X Y
  let Q (r : B) := (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ labelProjector
    (fun d ↦ Database.allCollisionLabel
      ((Equiv.funSplitAt i (Database X Y)).symm (d, r.1))) true
  let e := recordSplit (X := X) (Y := Y) (R := R) i
  have hb : (liftBlocks e (collisionRate t n (Fintype.card Y) •
      (P n + ((t : ℝ) / 2) • 1 - (fun b ↦ (U b)ᴴ) * P (n + 1) * U) -
      (fun b ↦ ((Q * U - U * Q) b)ᴴ) * (Q * U - U * Q))).PosSemidef :=
    posSemidef_liftBlocks e (fun b ↦ (familyOrdinaryBlock_bounds hn i b).2)
  simp only [liftBlocks_sub, liftBlocks_add, liftBlocks_smul, liftBlocks_one,
    liftBlocks_mul] at hb
  rw [liftBlocks_adjoint e U, liftBlocks_adjoint e (Q * U - U * Q)] at hb
  simp only [liftBlocks_sub, liftBlocks_mul] at hb
  dsimp only
  rw [chargedDrop, familyPopulationMatrix_blocks, familyPopulationMatrix_blocks,
    familyCollisionMatrix_blocks]
  exact hb

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
  have hp := commute_familyDiagonal U hU (fun d ↦ (familyPopulation t (n + 1) d : ℂ))
  change (1 ⊗ₖ familyPopulationMatrix t (n + 1)) * U =
    U * (1 ⊗ₖ familyPopulationMatrix t (n + 1)) at hp
  have hq := commute_familyDiagonal U hU
    (fun d ↦ if Database.allCollisionLabel d = true then (1 : ℂ) else 0)
  refine ⟨?_, sub_eq_zero.mpr hq⟩
  rw [chargedDrop, zero_smul, add_zero,
    conjTranspose_mul_mul_eq_of_commute hunit hp]
  rw [familyPopulationMatrix, familyPopulationMatrix, ← diagonal_one,
    diagonal_kronecker_diagonal, diagonal_kronecker_diagonal, diagonal_sub]
  apply PosSemidef.diagonal
  intro a
  simp only [Pi.zero_apply, one_mul, ← Complex.ofReal_sub, Complex.zero_le_real]
  exact sub_nonneg.mpr (familyPopulation_idle hn a.2.1)

/-- The diagonal square root factors the family population operator. -/
@[expose]
noncomputable def familyPotentialFactor (t n : ℕ) :
    Matrix ((Fin k → Database X Y) × R) ((Fin k → Database X Y) × R) ℂ :=
  diagonal (fun s ↦ (Real.sqrt (familyPopulation t n s.1) : ℂ))

omit [AddCommGroup Y] in
/-- The Gram matrix of the population factor is the population operator. -/
theorem familyPotentialFactor_gram (t n : ℕ) :
    (familyPotentialFactor (k := k) (X := X) (Y := Y) (R := R) t n)ᴴ *
      familyPotentialFactor t n = familyPopulationMatrix t n := by
  rw [familyPotentialFactor, diagonal_conjTranspose, diagonal_mul_diagonal]
  change diagonal _ = diagonal _
  congr 1
  funext s
  change star (Real.sqrt (familyPopulation t n s.1) : ℂ) *
    (Real.sqrt (familyPopulation t n s.1) : ℂ) = (familyPopulation t n s.1 : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (familyPopulation_nonneg t n s.1)]

omit [DecidableEq X] [DecidableEq Y] [Fintype Y] [AddCommGroup Y] in
/-- The empty family has zero initial potential. -/
theorem familyPopulation_empty (t : ℕ) :
    familyPopulation (k := k) (X := X) (Y := Y) t 0 (fun _ ↦ Database.empty) = 0 := by
  simp [familyPopulation, collisionPotential]

end family

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
      rw [liftBlocks_const]
      ext ⟨xy', d', r'⟩ ⟨xy, d, r⟩
      change onFactor (splitAt (X × Y) (Database X Y) i) (compressedOracle X Y)
          (xy', d') (xy, d) * (1 : Matrix (RecReg k Cm Dm Cell)
            (RecReg k Cm Dm Cell) ℂ) r' r =
        onFactor (recordSplit i) (compressedOracle X Y) (xy', (d', r')) (xy, (d, r))
      rw [onFactor_apply, onFactor_apply, one_apply]
      simp only [splitAt_apply, recordSplit_apply, Prod.mk.injEq]
      split_ifs <;> simp_all
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
  have hz (f : ((Fin k → Database X Y) × RecReg k Cm Dm Cell) → ℂ) (hf : f d = 0) :
      diagonal f * (SubState.basis d).matrix = 0 := by
    rw [SubState.matrix_basis]
    ext a b
    rw [diagonal_mul, Matrix.single_apply]
    split_ifs with h
    · rw [← h.1, hf, zero_mul]
      rfl
    · simp
  have hq := hz (fun s ↦ if Database.allCollisionLabel s.1 = true then 1 else 0) (by
    simp [d, Database.allCollisionLabel, Database.allCollisionFree_empty])
  have hp := hz (fun s ↦ (familyPopulation t 0 s.1 : ℂ)) (by
    rw [familyPopulation_empty]; rfl)
  have he := compressedWithRecord_init ME code bot V hV
  dsimp only
  rw [he]
  constructor
  · change MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ
      diagonal (fun s : (Fin k → Database X Y) × RecReg k Cm Dm Cell ↦
        if Database.allCollisionLabel s.1 = true then (1 : ℂ) else 0))
        (ρ.matrix ⊗ₖ (SubState.basis d).matrix) = 0
    rw [MatrixMap.conj_apply, ← mul_kronecker_mul, hq, kronecker_zero, Matrix.zero_mul]
  · change QuantumRuntime.potential
      (familyPotentialFactor (k := k) (X := X) (Y := Y) (R := RecReg k Cm Dm Cell) t 0)
      (ρ.matrix ⊗ₖ (SubState.basis d).matrix) = 0
    rw [QuantumRuntime.potential_eq, familyPotentialFactor_gram, ← mul_kronecker_mul]
    change ENNReal.ofReal ((((1 : Matrix A A ℂ) * ρ.matrix) ⊗ₖ
      (diagonal (fun s : (Fin k → Database X Y) × RecReg k Cm Dm Cell ↦
        (familyPopulation t 0 s.1 : ℂ)) *
        (SubState.basis d).matrix)).trace.re) = 0
    rw [hp, kronecker_zero, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]

/-- **The concrete `7/4` collision event bound**, bounds-note equations (87)–(89), (91).
This supports NOTE's refinement of the paper's §9.3 collision-event argument
(Lemma 9.6, p. 61; event bound, pp. 64–65).
For arbitrary programs against the old k compressed oracles, extraction, and recording,
the event that at least one database has a collision has weight at most
`(7t+5)t min(w,t)/(4|Y|)`. Here `w` is the actual total ordinary query mass.
The statement includes `t = 0` and subnormalized initial program states. -/
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

end Quantum
