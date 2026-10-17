/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.Offline
import all VCVio.Quantum.VC.Proof.Offline

/-!
# Collision bounds without a recording interface

The per-database collision inequalities underlying the recorded runtime also apply directly
to the ordinary/extraction private register. The runtime bound keeps the actual ordinary mass.
-/

public section

open Matrix Quantum.EmulatedOracle
open scoped Kronecker ComplexOrder ENNReal
namespace Quantum

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm]
  [Fintype Z] [DecidableEq Z] [AddGroup Z] {Dm : Fin k → Type}
  (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)

/-- The family collision event on the ordinary/extraction private register. -/
@[expose]
noncomputable def extractCollisionMatrix : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  labelProjector Database.allCollisionLabel true

/-- The charged family population schedule on the ordinary/extraction private register. -/
@[expose]
noncomputable def extractPopulationMatrix (t n : ℕ) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  diagonal (fun D ↦ (familyPopulation t n D : ℂ))

/-- The ordinary/extraction ports obey the collision inequalities used by the recorded runtime,
with ordinary ports alone charged. The proof uses the same per-database blocks. -/
theorem withExtract_collision_port_bounds {t n : ℕ} (hn : n < t) (p : Fin k ⊕ Unit) :
    let U : Matrix ((extIn k X Y Cm Z p) × (Fin k → Database X Y))
      ((extIn k X Y Cm Z p) × (Fin k → Database X Y)) ℂ :=
        ((compressedVCOracle k X Y).withExtract ME code).U p
    let P := fun j ↦ (1 : Matrix (extIn k X Y Cm Z p) (extIn k X Y Cm Z p) ℂ) ⊗ₖ
      extractPopulationMatrix (k := k) (X := X) (Y := Y) t j
    let Q := (1 : Matrix (extIn k X Y Cm Z p) (extIn k X Y Cm Z p) ℂ) ⊗ₖ
      extractCollisionMatrix (k := k) (X := X) (Y := Y)
    let Δ := chargedDrop U (P n) (P (n + 1))
      (if p.isLeft then (t : ℝ) / 2 else 0)
    Δ.PosSemidef ∧ (collisionRate t n (Fintype.card Y) • Δ -
      (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef := by
  classical
  rcases p with i | u
  · let e := splitAt (X × Y) (Database X Y) i
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
        extractCollisionMatrix (k := k) (X := X) (Y := Y) = liftBlocks e Q := by
      rw [extractCollisionMatrix, labelProjector, ← diagonal_one,
        diagonal_kronecker_diagonal]
      simp only [one_mul]
      rw [← liftBlocks_diagonal e]
      congr 1
      funext r
      simp only [Q, labelProjector, ← diagonal_one, diagonal_kronecker_diagonal, one_mul]
      rfl
    have hu : ((compressedVCOracle k X Y).withExtract ME code).U (.inl i) =
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
    simp only [Sum.isLeft_inl, ite_true, hu]
    rw [← hp, ← hp] at hd hl
    rw [← hq] at hl
    exact ⟨hd, hl⟩
  · cases u
    let U := extractUnitary ME code
    let P := fun j ↦ (1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ
      extractPopulationMatrix (k := k) (X := X) (Y := Y) t j
    let Q := (1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ
      extractCollisionMatrix (k := k) (X := X) (Y := Y)
    have hc (f : (Fin k → Database X Y) → ℂ) :
        ((1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ diagonal f) * U =
          U * ((1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ diagonal f) := by
      rw [← diagonal_one, diagonal_kronecker_diagonal]
      ext a b
      rw [diagonal_mul, mul_diagonal]
      by_cases h : U a b = 0
      · simp [h]
      · have hD : a.2 = b.2 := by
          unfold U at h
          rw [extractUnitary_apply] at h
          split_ifs at h with he
          · exact he.2.2
          · exact False.elim (h rfl)
        simp only [one_mul, hD]
        ring
    have hp : Uᴴ * P (n + 1) * U = P (n + 1) := by
      dsimp only [P, extractPopulationMatrix]
      rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc,
        ← star_eq_conjTranspose,
        mem_unitaryGroup_iff'.mp (extractUnitary_mem_unitaryGroup ME code), Matrix.one_mul]
    have hq : Q * U - U * Q = 0 := sub_eq_zero.mpr (hc _)
    have hd : (P n - P (n + 1)).PosSemidef := by
      simp only [P, extractPopulationMatrix, ← diagonal_one,
        diagonal_kronecker_diagonal, diagonal_sub, one_mul]
      apply PosSemidef.diagonal
      intro a
      change (0 : ℂ) ≤ (familyPopulation t n a.2 : ℂ) -
        (familyPopulation t (n + 1) a.2 : ℂ)
      rw [← Complex.ofReal_sub, Complex.zero_le_real]
      exact sub_nonneg.mpr (familyPopulation_idle hn a.2)
    dsimp only
    change (chargedDrop U (P n) (P (n + 1)) 0).PosSemidef ∧
      (collisionRate t n (Fintype.card Y) • chargedDrop U (P n) (P (n + 1)) 0 -
        (Q * U - U * Q)ᴴ * (Q * U - U * Q)).PosSemidef
    rw [chargedDrop, zero_smul, add_zero, hp, hq, conjTranspose_zero, Matrix.zero_mul, sub_zero]
    exact ⟨hd, hd.smul (collisionRate_nonneg t n (by positivity))⟩

/-- Square root of the charged population schedule without a recording register. -/
@[expose]
noncomputable def extractPotentialFactor (t n : ℕ) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  diagonal (fun D ↦ (Real.sqrt (familyPopulation t n D) : ℂ))

omit [AddCommGroup Y] in
/-- The square-root schedule has the prescribed population Gram matrix. -/
theorem extractPotentialFactor_gram (t n : ℕ) :
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

/-- Empty databases have zero collision weight and zero initial charged population. -/
theorem compressedWithExtract_initial_zero (t : ℕ) {A : QReg} (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withExtract ME code
    let Q := extractCollisionMatrix (k := k) (X := X) (Y := Y)
    let K := extractPotentialFactor (k := k) (X := X) (Y := Y) t 0
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) (ρ.matrix ⊗ₖ E.init.matrix) = 0 ∧
      QuantumRuntime.potential K (ρ.matrix ⊗ₖ E.init.matrix) = 0 := by
  classical
  let D : Fin k → Database X Y := fun _ ↦ Database.empty
  have hz (f : (Fin k → Database X Y) → ℂ) (hf : f D = 0) :
      diagonal f * (SubState.basis D).matrix = 0 := by
    rw [SubState.matrix_basis]
    ext a b
    rw [diagonal_mul, Matrix.single_apply]
    split_ifs with h
    · rw [← h.1, hf, zero_mul]
      rfl
    · simp
  have hq := hz (fun D ↦ if Database.allCollisionLabel D = true then 1 else 0)
    (by simp [D, Database.allCollisionLabel, Database.allCollisionFree_empty])
  have hp := hz (fun D ↦ (familyPopulation t 0 D : ℂ))
    (by rw [familyPopulation_empty]; rfl)
  dsimp only
  change MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ extractCollisionMatrix)
      (ρ.matrix ⊗ₖ (SubState.basis D).matrix) = 0 ∧
    QuantumRuntime.potential (extractPotentialFactor t 0)
      (ρ.matrix ⊗ₖ (SubState.basis D).matrix) = 0
  constructor
  · rw [MatrixMap.conj_apply, ← mul_kronecker_mul]
    change ((1 * ρ.matrix) ⊗ₖ
      ((diagonal fun D ↦ if Database.allCollisionLabel D = true then 1 else 0) *
        (SubState.basis D).matrix)) * _ = 0
    rw [hq, kronecker_zero, Matrix.zero_mul]
  · rw [QuantumRuntime.potential_eq, extractPotentialFactor_gram, ← mul_kronecker_mul]
    change ENNReal.ofReal (((1 * ρ.matrix) ⊗ₖ
      (diagonal (fun D ↦ (familyPopulation t 0 D : ℂ)) *
        (SubState.basis D).matrix)).trace.re) = 0
    rw [hp, kronecker_zero, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero]

/-- The collision event bound of NOTE (91) for the ordinary/extraction runtime. It uses the
same charged block inequalities as the recorded bound supporting ePrint 2025/2166,
Lemma 9.6 (p. 61; collision argument, pp. 64–65). Arbitrary coherent programs and substates
are allowed, and the ordinary-query mass is measured in this runtime. -/
theorem collisionEvent_compressedWithExtract_le {L : LocalSig} (I : L.Interp)
    {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (cohSpec (extIn k X Y Cm Z)) W A)
    {t : ℕ} (hx : x.IsQueryBound (fun _ ↦ t)) (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withExtract ME code
    let σ := ρ.matrix ⊗ₖ E.init.matrix
    let w := ∑ i : Fin k, E.totalMass I x σ (.inl i)
    E.coherent.toRuntime.eventWeight I
        (extractCollisionMatrix (k := k) (X := X) (Y := Y)) x σ ≤
      ENNReal.ofReal ((7 * t + 5) * t / (4 * (Fintype.card Y : ℝ))) * min w t := by
  classical
  let E := (compressedVCOracle k X Y).withExtract ME code
  let Q := extractCollisionMatrix (k := k) (X := X) (Y := Y)
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

end Quantum
