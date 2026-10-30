/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Compressed

/-!
# Checked reads and prescribed classical checks

A successful transcript requires a present value at every prescribed cell. Its residual channel
is conjugation by the compressed partial-table projector, including zero values, repetitions,
and conflicting prescriptions. Oracle indices remain part of the cell address.
-/

public section

open Matrix OracleComp OracleSpec
open scoped Kronecker

namespace Quantum
namespace CompressedReplay

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The partial-database checker on a query log spanning several oracle indices. -/
@[expose]
noncomputable def partialCheck (log : QueryLog ((Fin k × X) →ₒ Y)) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  diagonal fun D ↦ if ∀ p ∈ log, D p.1.1 p.1.2 = some p.2 then 1 else 0

/-- The filled checker is the compressed conjugate of the partial-database checker. -/
@[expose]
noncomputable def filledCheck (log : QueryLog ((Fin k × X) →ₒ Y)) :
    Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  compressDatabases k X Y * partialCheck log * compressDatabases k X Y

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

/-- Flattening private tables preserves the prescribed partial-table predicate. -/
theorem partialCheck_eq_flat (log : QueryLog ((Fin k × X) →ₒ Y)) :
    partialCheck log = (diagonal (fun D : Database (Fin k × X) Y ↦
      if ∀ p ∈ log, D p.1 = some p.2 then (1 : ℂ) else 0)).submatrix
        (Equiv.curry (Fin k) X (Option Y)).symm
        (Equiv.curry (Fin k) X (Option Y)).symm := by
  rw [partialCheck, submatrix_diagonal_equiv]
  rfl

/-- Flattening private tables preserves the compressed prescribed projector. -/
theorem filledCheck_eq_flat (log : QueryLog ((Fin k × X) →ₒ Y)) :
    filledCheck log = (compressAll (Fin k × X) Y *
      diagonal (fun D : Database (Fin k × X) Y ↦
        if ∀ p ∈ log, D p.1 = some p.2 then (1 : ℂ) else 0) *
      compressAll (Fin k × X) Y).submatrix
        (Equiv.curry (Fin k) X (Option Y)).symm
        (Equiv.curry (Fin k) X (Option Y)).symm := by
  rw [filledCheck, compressDatabases_eq_flat, partialCheck_eq_flat,
    submatrix_mul_equiv, submatrix_mul_equiv]

variable [AddCommGroup Y]

/-- With no prescriptions the successful projector is the identity. -/
@[simp]
theorem filledCheck_nil : filledCheck ([] : QueryLog ((Fin k × X) →ₒ Y)) = 1 := by
  simp [filledCheck, partialCheck, compressDatabases_mul_self]

/-- Adding a prescription multiplies the successful projector by that cell's answer projector. -/
theorem filledCheck_cons (p : (_ : Fin k × X) × Y) (log : QueryLog ((Fin k × X) →ₒ Y)) :
    filledCheck (p :: log) = compressedReadProjector k X Y p.1 (some p.2) * filledCheck log := by
  rw [filledCheck, compressedReadProjector, filledCheck,
    compressed_conjugate_mul _ (compressDatabases_mul_self k X Y)]
  congr 2
  rw [partialCheck, partialCheck, diagonal_mul_diagonal]
  congr 1
  funext D
  simp only [List.forall_mem_cons]
  split_ifs <;> simp_all

/-- The successful log projector is the product of its optional-answer projectors. -/
theorem filledCheck_eq_prod (log : QueryLog ((Fin k × X) →ₒ Y)) :
    filledCheck log = (log.map fun p ↦ compressedReadProjector k X Y p.1 (some p.2)).prod := by
  induction log with
  | nil => simp
  | cons p log ih => rw [filledCheck_cons, List.map_cons, List.prod_cons, ih]

/-- Placing the final read on the right gives the same successful projector. -/
theorem filledCheck_cons_right (p : (_ : Fin k × X) × Y)
    (log : QueryLog ((Fin k × X) →ₒ Y)) :
    filledCheck (p :: log) = filledCheck log * compressedReadProjector k X Y p.1 (some p.2) := by
  simp only [filledCheck_eq_prod]
  refine (Commute.list_prod_right _ _ fun Q hQ ↦ ?_).eq
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hQ
  exact compressedReadProjector_commute k X Y p.1 q.1 (some p.2) (some q.2)

end CompressedReplay

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {Dm : Fin k → Type}
  (ME : MultiExtractor k Cm Dm (compressedVCOracle k X Y).S) (code : TpDCode k Dm Z)

/-- Each concrete read branch retains exactly its projected joint state. -/
theorem branch_run₂_checkedRead_compressedVCOracle (B : QReg) (j : Fin k) (t : X) (a : Option Y) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
      (checkedRead B j t)).branch a =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ compressedReadProjector k X Y (j, t) a) :=
  branch_run₂_checkedRead _ ME code B j t a

omit [AddCommGroup Y] [AddGroup Z] in
private theorem checked_fold_branch (R : QuantumRuntime (mixedExtSpec k X Y Cm Z))
    (B : QReg) (j : Fin k) (P : X → Y → Matrix R.D R.D ℂ)
    (K : QueryLog (X →ₒ Y) → Matrix R.D R.D ℂ) (hNil : K [] = 1)
    (hCons : ∀ p ps, K (p :: ps) = K ps * P p.1 p.2)
    (hRead : ∀ x y, (R.run₂ .instruments (checkedRead B j x)).branch (some y) =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ P x y))
    (log : QueryLog (X →ₒ Y)) (acc : Bool) :
    (R.run₂ .instruments (runClassicalChecked B j
      (liftComp (log.foldlM QueryLog.recheckStep acc) (unifSpec + (X →ₒ Y))))).branch
        (some true) =
      if acc then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ K log) else 0 := by
  induction log generalizing acc with
  | nil =>
    simp only [List.foldlM_nil, liftComp_pure, runClassicalChecked_pure,
      QuantumRuntime.run₂_pure, hNil, one_kronecker_one,
      MatrixMap.conj_one]
    cases acc <;> simp
  | cons p log ih =>
    have hp : runClassicalChecked (Cm := Cm) (Z := Z) B j
        (liftComp ((p :: log).foldlM QueryLog.recheckStep acc) (unifSpec + (X →ₒ Y))) =
        (checkedRead B j p.1).bind (fun a ↦ match a with
          | none => QuantumComp₂.pure none
          | some y => runClassicalChecked B j
              (liftComp (log.foldlM QueryLog.recheckStep (acc && decide (y = p.2)))
                (unifSpec + (X →ₒ Y)))) := by
      simp only [List.foldlM_cons, QueryLog.recheckStep, bind_assoc, pure_bind, liftComp_bind,
        liftComp_liftM_query]
      rw [OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_right_query]
      erw [runClassicalChecked_query_bind]
      simp only [checkedOracleImpl, QueryImpl.add_apply_inr, OptionT.run_mk]
      congr 1
      funext a
      cases a <;> rfl
    rw [hp, QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply_univ,
      Finset.sum_eq_single (some p.2)]
    · rw [ih]
      simp only [decide_true, Bool.and_true]
      cases acc
      · simp
      · simp only [↓reduceIte]
        rw [hRead, ← MatrixMap.conj_mul,
          ← mul_kronecker_mul, Matrix.one_mul, hCons]
    · intro a _ ha
      cases a with
      | none => simp
      | some y => rw [ih]; simp_all
    · simp

open CompressedReplay in
/-- The present accepting result of a prescribed fold retains its full successful channel. -/
theorem branch_run₂_checked_fold (B : QReg) (j : Fin k) (log : QueryLog (X →ₒ Y))
    (acc : Bool) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
      (runClassicalChecked B j (liftComp (log.foldlM QueryLog.recheckStep acc)
        (unifSpec + (X →ₒ Y))))).branch (some true) =
      if acc then MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        filledCheck (log.map fun p ↦ ⟨(j, p.1), p.2⟩)) else 0 := by
  let R := (compressedVCOracle k X Y).mixedExtractRuntime ME code
  let P : X → Y → Matrix R.D R.D ℂ :=
    fun x y ↦ compressedReadProjector k X Y (j, x) (some y)
  let K : QueryLog (X →ₒ Y) → Matrix R.D R.D ℂ :=
    fun ps ↦ filledCheck (ps.map fun p ↦ ⟨(j, p.1), p.2⟩)
  have hn : K [] = 1 := filledCheck_nil (k := k) (X := X) (Y := Y)
  have hc (p : (_ : X) × Y) (ps : QueryLog (X →ₒ Y)) : K (p :: ps) = K ps * P p.1 p.2 := by
    dsimp +instances only [K, P, R, VCOracle.mixedExtractRuntime, QuantumRuntime.extend,
      EmulatedOracle.toRuntime, EmulatedOracle.coherent, VCOracle.withExtract,
      EmulatedOracle.extend, compressedVCOracle]
    simpa only [List.map_cons] using
      (filledCheck_cons_right (k := k) (X := X) (Y := Y)
        ⟨(j, p.1), p.2⟩ (ps.map fun q ↦ ⟨(j, q.1), q.2⟩))
  have hr (x : X) (y : Y) : (R.run₂ .instruments (checkedRead B j x)).branch (some y) =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ P x y) :=
    branch_run₂_checkedRead_compressedVCOracle ME code B j x (some y)
  exact checked_fold_branch R B j P K hn hc hr log acc

variable {Msg : Type} {ℓ : Fin k → ℕ} {Td Pf : Fin k → Type}
  (VC : ∀ i, VectorCommitment X Y Msg Cm (Td i) (Pf i) (ℓ i))

omit [AddCommGroup Y] [AddGroup Z] in
private theorem checkAt_branch (R : QuantumRuntime (mixedExtSpec k X Y Cm Z))
    (B : QReg) (i j : Fin k) (cm : Cm) (ans : PartialVec (ℓ i) Msg) (pf : Pf i) :
    (R.run₂ .instruments (checkAt VC B i j cm ans pf)).branch true =
      (R.run₂ .instruments
        (runClassicalChecked B j ((VC i).check cm ans pf))).branch (some true) := by
  rw [checkAt, QuantumComp₂.bind_eq, QuantumRuntime.run₂_bind,
    DSubInstrument.branch_bind_apply_univ, Finset.sum_eq_single (some true)]
  · simp
  · intro a _ ha
    cases a with
    | none => simp
    | some b => cases b <;> simp_all
  · simp

/-- The accepting checked branch is exactly the compressed partial-table check projector. -/
theorem branch_run₂_checkAt_compressedVCOracle
    (ME : MultiExtractor k Cm (DmOf ℓ Msg Td) (compressedVCOracle k X Y).S)
    (code : TpDCode k (DmOf ℓ Msg Td) Z) (chk : ∀ i, (VC i).NonadaptiveCheck)
    (B : QReg) (i j : Fin k) (cm : Cm) (ans : PartialVec (ℓ i) Msg) (pf : Pf i) :
    (((compressedVCOracle k X Y).mixedExtractRuntime ME code).run₂ .instruments
      (checkAt VC B i j cm ans pf)).branch true =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (compressDatabases k X Y * diagonal (fun D ↦
          if (chk i).checkOn (D j) cm ans pf then (1 : ℂ) else 0) *
            compressDatabases k X Y)) := by
  refine (checkAt_branch VC _ B i j cm ans pf).trans ?_
  have hcheck := (chk i).check_eq cm ans pf
  rw [hcheck]
  cases h : (chk i).log cm ans pf with
  | none =>
    have hzero : (diagonal (fun D : Fin k → Database X Y ↦
        if (chk i).checkOn (D j) cm ans pf then (1 : ℂ) else 0)) = 0 := by
      simp [VectorCommitment.NonadaptiveCheck.checkOn, h]
    simp only [Option.elim_none, liftComp_pure, runClassicalChecked_pure,
      QuantumRuntime.run₂_pure]
    have hP : MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (compressDatabases k X Y * diagonal (fun D ↦
          if (chk i).checkOn (D j) cm ans pf then (1 : ℂ) else 0) *
            compressDatabases k X Y)) = 0 := by
      rw [hzero, Matrix.mul_zero, Matrix.zero_mul, kronecker_zero, MatrixMap.conj_zero]
    exact (SubInstrument.branch_pure_of_ne (by decide)).trans hP.symm
  | some ps =>
    have hP : CompressedReplay.filledCheck (ps.map fun p ↦ ⟨(j, p.1), p.2⟩) =
        compressDatabases k X Y * diagonal (fun D ↦
          if (chk i).checkOn (D j) cm ans pf then (1 : ℂ) else 0) * compressDatabases k X Y := by
      unfold CompressedReplay.filledCheck CompressedReplay.partialCheck
      congr 2
      congr 1
      funext D
      simp only [VectorCommitment.NonadaptiveCheck.checkOn, h, Option.elim_some,
        QueryLog.agreesWith_eq_true_iff, QueryCache.ofFn_apply]
      congr 1
      simp only [List.forall_mem_map]
    exact (branch_run₂_checked_fold ME code B j ps true).trans
      (congrArg (fun P ↦ MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ P)) hP)

end Quantum
