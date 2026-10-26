/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.CheckerDistance

/-!
# Checked-read channel tests

Prescriptions include zero, repeated cells, conflicting answers, and equal addresses in different
databases. Equalities compare projector products and complete residual channels.
-/

public section

open Quantum Quantum.CompressedReplay Matrix OracleSpec
open scoped Kronecker ENNReal Matrix.Norms.L2Operator

namespace VCVioTest.QuantumCheckedRead

/-- A repeated prescription across two oracle databases, touching only one cell. -/
abbrev repeated : QueryLog ((Fin 2 × Bool) →ₒ ZMod 3) :=
  [⟨(0, true), 1⟩, ⟨(0, true), 1⟩]

/-- Duplicate checks retain the one-cell squared discrepancy `5/9`. -/
example : ‖filledCheck repeated - partialCheck repeated‖ ^ 2 = 5 / 9 := by
  have hc : QueryLog.Consistent repeated := by
    intro p hp q hq _
    simp only [repeated, List.mem_cons, List.not_mem_nil, or_false, or_self] at hp hq
    subst p
    subst q
    rfl
  rw [filled_partial_distance_sq repeated hc]
  norm_num [loggedCells, repeated, ZMod.card]

/-- Equal addresses in distinct databases count as two cells, giving `65/81`. -/
example :
    ‖filledCheck
        ([⟨(0, true), 1⟩, ⟨(1, true), 1⟩] : QueryLog ((Fin 2 × Bool) →ₒ ZMod 3)) -
      partialCheck [⟨(0, true), 1⟩, ⟨(1, true), 1⟩]‖ ^ 2 = 65 / 81 := by
  have hc : QueryLog.Consistent
      ([⟨(0, true), 1⟩, ⟨(1, true), 1⟩] : QueryLog ((Fin 2 × Bool) →ₒ ZMod 3)) := by
    refine QueryLog.consistent_iff.mpr fun p hp q hq _ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rfl
  rw [filled_partial_distance_sq _ hc]
  norm_num [loggedCells, ZMod.card]

/-- Two different answers at one cell, one of them the special zero answer. -/
abbrev conflicting : QueryLog ((Fin 2 × Bool) →ₒ ZMod 3) :=
  [⟨(0, true), 0⟩, ⟨(0, true), 1⟩]

/-- Conflicting prescriptions vanish even if one is the special zero answer. -/
example : filledCheck conflicting = 0 ∧ partialCheck conflicting = 0 := by
  apply filled_partial_eq_zero_of_conflict
  intro h
  have he := QueryLog.consistent_iff.mp h ⟨(0, true), 0⟩ (by simp [conflicting])
    ⟨(0, true), 1⟩ (by simp [conflicting]) rfl
  exact (by decide : (0 : ZMod 3) ≠ 1) he

/-- The singleton answer alphabet has unit distance on a prescribed cell. -/
example : ‖filledCheck ([⟨(0, true), 0⟩] : QueryLog ((Fin 1 × Bool) →ₒ ZMod 1)) -
    partialCheck [⟨(0, true), 0⟩]‖ ^ 2 = 1 := by
  rw [filled_partial_distance_sq _ (QueryLog.consistent_singleton _)]
  norm_num [loggedCells, ZMod.card]

/-- An empty list has zero checker distance, including for a singleton alphabet. -/
example :
    ‖filledCheck ([] : QueryLog ((Fin 1 × Bool) →ₒ ZMod 1)) - partialCheck []‖ = 0 := by
  simp [filledCheck_nil, partialCheck]

local notation "E" => compressedVCOracle 2 Bool (ZMod 2)
local notation "Q" => compressedReadProjector 2 Bool (ZMod 2)
local notation "Cell" => Fin 2 × Bool
local notation "DB" => Fin 2 → Database Bool (ZMod 2)

/-- Empty prescriptions retain every residual state. -/
example (ρ : Matrix DB DB ℂ) :
    MatrixMap.conj (filledCheck ([] : QueryLog (Cell →ₒ ZMod 2))) ρ = ρ := by
  simp

/-- Prescribing zero selects the present-zero projector. -/
example (c : Cell) : filledCheck [⟨c, (0 : ZMod 2)⟩] = Q c (some 0) := by
  rw [filledCheck_cons, filledCheck_nil, Matrix.mul_one]

/-- A missing label and a present zero are orthogonal outcomes. -/
example (c : Cell) : Q c none * Q c (some 0) = 0 := by
  rw [compressedReadProjector_orthogonal]
  simp

/-- The missing projector differs from present zero on the compressed empty-label state. -/
example (c : Cell) : Q c none ≠ Q c (some 0) := by
  let C := compressDatabases 2 Bool (ZMod 2)
  have hc (a : Option (ZMod 2)) : C * Q c a * C =
      diagonal (fun D : DB ↦ if D c.1 c.2 = a then (1 : ℂ) else 0) := by
    change C * (C * _ * C) * C = _
    calc
      _ = (C * C) * (diagonal fun D : DB ↦ if D c.1 c.2 = a then (1 : ℂ) else 0) *
          (C * C) := by simp only [Matrix.mul_assoc]
      _ = _ := by simp [C, compressDatabases_mul_self]
  intro he
  have h := congrArg (fun M ↦ (C * M * C) (fun _ ↦ Database.empty)
    (fun _ ↦ Database.empty)) he
  rw [hc, hc] at h
  simp [Database.empty] at h

/-- Repeating the same prescription leaves the complete channel unchanged. -/
example (c : Cell) (ρ : Matrix DB DB ℂ) :
    MatrixMap.conj (filledCheck [⟨c, (0 : ZMod 2)⟩, ⟨c, 0⟩]) ρ =
      MatrixMap.conj (filledCheck [⟨c, (0 : ZMod 2)⟩]) ρ := by
  simp [filledCheck_cons, compressedReadProjector_orthogonal]

/-- Conflicting prescriptions annihilate the residual state. -/
example (c : Cell) (ρ : Matrix DB DB ℂ) :
    MatrixMap.conj (filledCheck [⟨c, (0 : ZMod 2)⟩, ⟨c, 1⟩]) ρ = 0 := by
  simp [filledCheck_cons, compressedReadProjector_orthogonal]

/-- An empty cell does not satisfy even a zero prescription. -/
example : partialCheck [⟨((0 : Fin 2), false), (0 : ZMod 2)⟩]
    (fun _ ↦ Database.empty) (fun _ ↦ Database.empty) = 0 := by
  simp [partialCheck, Database.empty]

/-- Equal addresses at different indices remain independent prescribed cells. -/
example : partialCheck [⟨((0 : Fin 2), false), (0 : ZMod 2)⟩, ⟨(1, false), 1⟩]
    (fun i _ ↦ some (if i = 0 then 0 else 1))
    (fun i _ ↦ some (if i = 0 then 0 else 1)) = 1 := by
  simp [partialCheck]

/-- A present zero does satisfy the same prescription that rejects an empty cell. -/
example : partialCheck [⟨((0 : Fin 2), false), (0 : ZMod 2)⟩]
    (fun _ _ ↦ some 0) (fun _ _ ↦ some 0) = 1 := by
  simp [partialCheck]

/-- Missing reads vanish throughout the complete-table subspace. -/
example (c : Cell) : Q c none *
    (compressDatabases 2 Bool (ZMod 2) * basisMatrix (ofFunDatabases 2 Bool (ZMod 2))) = 0 :=
  compressedReadProjector_none_mul_tabulate c

/-- Mixed adaptive programs need no query bound for their full observed-law equality. -/
example {L : LocalSig} (I : L.Interp) {W : QReg → Type} {A : QReg}
    (x : QuantumComp L (mixedOracleSpec 2 Bool (ZMod 2)) W A) (ρ : SubState A)
    {γ : Type} [MeasurableSpace γ] (f : (Σ B, W B) → γ) :
    (E).mixedRuntime.evalDistMap I x ρ f =
      ∑ H : Fin 2 → Bool → ZMod 2,
        (Fintype.card (Fin 2 → Bool → ZMod 2) : ℝ≥0∞)⁻¹ •
        (romVCOracle 2 Bool (ZMod 2) H).mixedRuntime.evalDistMap I x ρ f :=
  evalDistMap_mixed_compressedVCOracle I x ρ f

/-- The actual checked read retains its projected joint state, including the empty outcome. -/
example {Cm Z : Type} [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
    {Dm : Fin 2 → Type} (ME : MultiExtractor 2 Cm Dm (E).S) (code : TpDCode 2 Dm Z)
    (B : QReg) (j : Fin 2) (x : Bool) (a : Option (ZMod 2))
    (ρ : Matrix (B × (E).S) (B × (E).S) ℂ) :
    ((((E).mixedExtractRuntime ME code).run₂ .instruments (checkedRead B j x)).branch a) ρ =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Q (j, x) a) ρ :=
  LinearMap.congr_fun (branch_run₂_checkedRead_compressedVCOracle ME code B j x a) ρ

/-- A minimal commitment interface whose checker uses a fixed optional prescription. -/
noncomputable def prescribedVC (ps : Option (QueryLog (Bool →ₒ ZMod 2))) :
    VectorCommitment Bool (ZMod 2) Unit Unit Unit Unit 0 where
  commit _ := pure ((), ())
  opening _ _ := pure ()
  check _ _ _ :=
    OracleComp.liftComp (ps.elim (pure false) QueryLog.recheck) (unifSpec + (Bool →ₒ ZMod 2))

/-- The fixed checker exposes precisely its prescribed list. -/
def prescribedCheck (ps : Option (QueryLog (Bool →ₒ ZMod 2))) :
    (prescribedVC ps).NonadaptiveCheck where
  log _ _ _ := ps
  check_eq _ _ _ := rfl
  qVC _ := ps.elim 0 List.length
  qVC_mono _ _ _ := le_rfl
  length_le _ _ _ L h := by cases ps <;> simp_all

/-- Flattening a batch follows claim order and retains the selected database indices. -/
example : batchLog (fun _ : Fin 2 ↦ prescribedCheck (some [⟨false, 0⟩])) Finset.univ
    ⟨Fin.rev, fun _ ↦ (), fun _ _ ↦ none, fun _ ↦ (), Finset.univ⟩ =
      [⟨(1, false), 0⟩, ⟨(0, false), 0⟩] := by
  decide

/-- A zero prescription reaches the actual accepting channel of `checkAt`. -/
example {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
    (ME : MultiExtractor 2 Unit (DmOf (fun _ ↦ 0) Unit (fun _ ↦ Unit)) (E).S)
    (code : TpDCode 2 (DmOf (fun _ ↦ 0) Unit (fun _ ↦ Unit)) Z)
    (B : QReg) (ρ : Matrix (B × DB) (B × DB) ℂ) :
    ((((E).mixedExtractRuntime ME code).run₂ .instruments
      (checkAt (fun _ ↦ prescribedVC (some [⟨false, 0⟩]))
        B 0 0 () (fun _ ↦ none) ())).branch true) ρ =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Q (0, false) (some 0)) ρ := by
  have h := branch_run₂_checkAt_compressedVCOracle
    (fun _ : Fin 2 ↦ prescribedVC (some [⟨false, 0⟩])) ME code
    (fun _ ↦ prescribedCheck (some [⟨false, 0⟩])) B 0 0 () (fun _ ↦ none) ()
  have hP : compressDatabases 2 Bool (ZMod 2) * diagonal (fun D : DB ↦
      if (prescribedCheck (some [⟨false, 0⟩])).checkOn (D 0) () (fun _ ↦ none) ()
        then (1 : ℂ) else 0) *
        compressDatabases 2 Bool (ZMod 2) = Q (0, false) (some 0) := by
    simp [compressedReadProjector, VectorCommitment.NonadaptiveCheck.checkOn,
      prescribedCheck, QueryLog.agreesWith_eq_true_iff]
  exact (LinearMap.congr_fun h ρ).trans
    (congrArg (fun P ↦ MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ P) ρ) hP)

section EmptyChecks

variable {Z : Type} [Fintype Z] [DecidableEq Z] [AddGroup Z]
  (ME : MultiExtractor 2 Unit (DmOf (fun _ ↦ 0) Unit (fun _ ↦ Unit)) (E).S)
  (code : TpDCode 2 (DmOf (fun _ ↦ 0) Unit (fun _ ↦ Unit)) Z) (B : QReg)

/-- A malformed opening has zero accepting channel through the actual checker. -/
example :
    ((((E).mixedExtractRuntime ME code).run₂ .instruments
      (checkAt (fun _ ↦ prescribedVC none) B 0 0 () (fun _ ↦ none) ())).branch true) = 0 := by
  have h := branch_run₂_checkAt_compressedVCOracle (fun _ ↦ prescribedVC none)
    ME code (fun _ ↦ prescribedCheck none) B 0 0 () (fun _ ↦ none) ()
  have hP : compressDatabases 2 Bool (ZMod 2) * diagonal (fun D : DB ↦
      if (prescribedCheck none).checkOn (D 0) () (fun _ ↦ none) ()
        then (1 : ℂ) else 0) * compressDatabases 2 Bool (ZMod 2) = 0 := by
    simp [VectorCommitment.NonadaptiveCheck.checkOn, prescribedCheck]
  exact h.trans ((congrArg (fun P ↦ MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ P)) hP).trans
    (by rw [kronecker_zero]; exact MatrixMap.conj_zero))

/-- A batch of malformed checks rejects through the batch's actual accepting channel. -/
example :
    ((((E).mixedExtractRuntime ME code).run₂ .instruments
      (QComp.allIn Finset.univ fun i ↦
        checkAt (fun _ ↦ prescribedVC none) B i i () (fun _ ↦ none) ())).branch true) = 0 := by
  refine (branch_run₂_filledBatch_compressedVCOracle
    (fun _ : Fin 2 ↦ prescribedCheck none) ME code B Finset.univ
    ⟨id, fun _ ↦ (), fun _ _ ↦ none, fun _ ↦ (), Finset.univ⟩).trans ?_
  simp only [filledBatch, checkPassProjector, Finset.mem_univ,
    VectorCommitment.NonadaptiveCheck.checkOn, prescribedCheck, Option.elim_none, id_eq,
    Bool.false_eq_true, imp_false, not_true_eq_false, forall_const, ↓reduceIte, diagonal_zero,
    mul_zero, zero_mul, implies_true, kroneckerMap_zero_right, MatrixMap.conj_zero]
  rfl

/-- A well-formed empty log accepts and preserves every joint residual state. -/
example (ρ : Matrix (B × DB) (B × DB) ℂ) :
    ((((E).mixedExtractRuntime ME code).run₂ .instruments
      (checkAt (fun _ ↦ prescribedVC (some [])) B 0 0 () (fun _ ↦ none) ())).branch true) ρ =
        ρ := by
  have h := branch_run₂_checkAt_compressedVCOracle (fun _ ↦ prescribedVC (some []))
    ME code (fun _ ↦ prescribedCheck (some [])) B 0 0 () (fun _ ↦ none) ()
  have hP : compressDatabases 2 Bool (ZMod 2) * diagonal (fun D : DB ↦
      if (prescribedCheck (some [])).checkOn (D 0) () (fun _ ↦ none) ()
        then (1 : ℂ) else 0) * compressDatabases 2 Bool (ZMod 2) = 1 := by
    simp [VectorCommitment.NonadaptiveCheck.checkOn, prescribedCheck,
      QueryLog.agreesWith_eq_true_iff, compressDatabases_mul_self]
  exact (LinearMap.congr_fun h ρ).trans
    ((congrArg (fun P ↦ MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ P) ρ) hP).trans (by simp))

end EmptyChecks

end VCVioTest.QuantumCheckedRead
