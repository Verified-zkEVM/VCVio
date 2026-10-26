/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Proof.CheckerDistance
public import VCVio.Quantum.VC.Proof.Repeatability

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
      ∑ H : Fin 2 → Bool → ZMod 2, (Fintype.card (Fin 2 → Bool → ZMod 2) : ℝ≥0∞)⁻¹ •
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

local notation "Old" => projectiveClassicalAnswers (k := 2) (X := Bool) (Y := ZMod 2)

/-- The public mixed-runtime theorem covers both retained answer families together. -/
example {L : LocalSig} (I : L.Interp) {W : QReg → Type} {B : QReg}
    (prog : QuantumComp L (mixedOracleSpec 2 Bool (ZMod 2)) W B)
    (leaf : Σ u, W u) (tr : QueryLog (Cell →ₒ ZMod 2))
    (us : QueryLog (Cell →ₒ Option (ZMod 2))) :
    ((Old).transcriptBranch leaf.1 tr ∘ₗ (E).classicalRead.transcriptBranch leaf.1 us) ∘ₗ
        ((E).mixedRuntime.run I prog).branch leaf ∘ₗ
        ((Old).transcriptBranch B tr ∘ₗ (E).classicalRead.transcriptBranch B us) =
      ((E).mixedRuntime.run I prog).branch leaf ∘ₗ
        ((Old).transcriptBranch B tr ∘ₗ (E).classicalRead.transcriptBranch B us) := by
  exact (Old).replay_mixed_transcripts_after_run (E).classicalRead
    (fun x y c a ↦ answer_commute_checked x c y a) I prog leaf tr us

/-- Fixed coins preserve optional answers, including the missing outcome. -/
example (B : QReg) (next : Bool → List (Option (ZMod 2)) → Cell) (coins : Bool)
    (ys zs : List (Option (ZMod 2))) (hl : zs.length = ys.length) :
    (E).classicalRead.transcriptBranch B
        (ProjectiveClassicalAnswers.adaptiveTranscript (next coins) zs) ∘ₗ
      (E).classicalRead.transcriptBranch B
        (ProjectiveClassicalAnswers.adaptiveTranscript (next coins) ys) =
      if zs = ys then (E).classicalRead.transcriptBranch B
        (ProjectiveClassicalAnswers.adaptiveTranscript (next coins) ys) else 0 :=
  (E).classicalRead.replay_fixedCoins_answers B next coins ys zs hl

/-- A fixed policy alternates ports and chooses later actions from both answer types. -/
def alternatingPolicy : List (ZMod 2 ⊕ Option (ZMod 2)) →
    (Fin 1 × ZMod 2) ⊕ (Fin 1 × ZMod 2)
  | [] => .inl (0, 0)
  | [.inl y] => .inr (0, y)
  | [.inl y, .inr none] => .inl (0, y + 1)
  | [.inl _, .inr (some z)] => .inr (0, z)
  | _ => .inl (0, 0)

/-- The missing-answer path really executes ordinary, checked, then ordinary reads. -/
example (B : QReg) :
    ((compressedVCOracle 1 (ZMod 2) (ZMod 2)).mixedRuntime.run₂ .instruments
      (ProjectiveClassicalAnswers.checkMixedTranscript (CompressedReplay.mixedCall B)
        alternatingPolicy [.inl 0, .inr none, .inl 0])).branch true =
      MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
        (CompressedReplay.answer (0, 0) (0 : ZMod 2) *
          (compressedReadProjector 1 (ZMod 2) (ZMod 2) (0, 0) none *
            CompressedReplay.answer (0, 1) (0 : ZMod 2)))) := by
  rw [CompressedReplay.branch_mixedAdaptive]
  simp only [ProjectiveClassicalAnswers.transcriptBranch,
    ProjectiveClassicalAnswers.adaptiveTranscript, alternatingPolicy,
    CompressedReplay.mixedAnswers, ProjectiveClassicalAnswers.projector_cons,
    ProjectiveClassicalAnswers.sumAnswers, CompressedReplay.projectiveClassicalAnswers,
    ProjectiveClassicalAnswers.projector_nil, zero_add]
  erw [Matrix.mul_one]
  rfl

/-- All three-step terminal paths of this policy obey operational replay, including paths
that branch on `none` and paths that continue with a present checked answer. -/
example (B : QReg) (ys zs : List (ZMod 2 ⊕ Option (ZMod 2)))
    (hy : ProjectiveClassicalAnswers.TerminalTranscript (fun pre ↦ pre.length == 3) ys)
    (hz : ProjectiveClassicalAnswers.TerminalTranscript (fun pre ↦ pre.length == 3) zs) :
    ((compressedVCOracle 1 (ZMod 2) (ZMod 2)).mixedRuntime.run₂ .instruments
        (ProjectiveClassicalAnswers.checkMixedTranscript
          (CompressedReplay.mixedCall B) alternatingPolicy zs)).branch true ∘ₗ
      ((compressedVCOracle 1 (ZMod 2) (ZMod 2)).mixedRuntime.run₂ .instruments
        (ProjectiveClassicalAnswers.checkMixedTranscript
          (CompressedReplay.mixedCall B) alternatingPolicy ys)).branch true =
      if zs = ys then ((compressedVCOracle 1 (ZMod 2) (ZMod 2)).mixedRuntime.run₂ .instruments
        (ProjectiveClassicalAnswers.checkMixedTranscript
          (CompressedReplay.mixedCall B) alternatingPolicy ys)).branch true else 0 :=
  CompressedReplay.replay_mixedAdaptive B (fun _ : Unit ↦ alternatingPolicy)
    (fun _ pre ↦ pre.length == 3) () ys zs hy hz

/-- Both checked outcomes occur in well-formed terminal histories of the alternating policy. -/
example :
    ProjectiveClassicalAnswers.TerminalTranscript
        (fun pre : List (ZMod 2 ⊕ Option (ZMod 2)) ↦ pre.length == 3)
        [.inl 0, .inr none, .inl 0] ∧
      ProjectiveClassicalAnswers.TerminalTranscript
        (fun pre : List (ZMod 2 ⊕ Option (ZMod 2)) ↦ pre.length == 3)
        [.inl 0, .inr (some 0), .inr (some 0)] := by
  simp [ProjectiveClassicalAnswers.TerminalTranscript]

namespace ExtractionReplay

/-- Identify a one-cell database family with its stored label. -/
def cellEquiv : (Fin 1 → Database Unit (ZMod 2)) ≃ Option (ZMod 2) :=
  (Equiv.funUnique (Fin 1) _).trans (Equiv.funUnique Unit _)

/-- The implemented checked projector in one-cell coordinates. -/
noncomputable def readProjector (a : Option (ZMod 2)) :
    Matrix (Option (ZMod 2)) (Option (ZMod 2)) ℂ :=
  Matrix.reindex cellEquiv cellEquiv (compressedReadProjector 1 Unit (ZMod 2) (0, ()) a)

/-- One-cell coordinates recover the compressed label projector. -/
theorem readProjector_eq (a : Option (ZMod 2)) :
    readProjector a = cellCompress (ZMod 2) *
      diagonal (fun d ↦ if d = a then 1 else 0) * cellCompress (ZMod 2) := by
  rw [readProjector, compressedReadProjector, Matrix.reindex_apply,
    ← Matrix.submatrix_mul_equiv _ _ _ cellEquiv.symm,
    ← Matrix.submatrix_mul_equiv _ _ _ cellEquiv.symm]
  congr 2 <;> ext i j <;>
    simp [cellEquiv, compressDatabases, compressAll, piKron_apply,
      Equiv.funUnique, Equiv.piUnique, Matrix.diagonal_apply, funext_iff]
  rfl

/-- Phase kickback controlled by whether the stored cell contains zero. -/
noncomputable def extractionPhase : Matrix (Option (ZMod 2)) (Option (ZMod 2)) ℂ :=
  diagonal fun d ↦ if d = some 0 then -1 else 1

/-- A one-cell extractor reports the predicate that the compressed cell stores zero. -/
noncomputable def phaseExtractor :
    MultiExtractor 1 Unit (fun _ ↦ ZMod 2) (Fin 1 → Database Unit (ZMod 2)) where
  extract _ d _ := if cellEquiv d = some 0 then 1 else 0

private theorem length_one (j : TupleLen 1) : j.len = 1 := by
  have := j.len_pos
  have := j.len_le
  omega

/-- A length-one decommitment is encoded by its unique bit. -/
noncomputable def phaseCode : TpDCode 1 (fun _ ↦ ZMod 2) (ZMod 2) where
  enc t := t.2 ⟨0, t.1.len_pos⟩
  enc_injective := by
    rintro ⟨j, t⟩ ⟨j', t'⟩ h
    have hj : j = j' := by
      apply Subtype.ext
      apply Fin.ext
      exact (length_one j).trans (length_one j').symm
    subst j'
    congr 1
    funext i
    have hi : i = ⟨0, j.len_pos⟩ := by
      apply Fin.ext
      have := i.isLt
      have := length_one j
      omega
    rw [hi]
    exact h

/-- The phase-kickback sector has the extraction output in the minus state. -/
noncomputable def phaseSector :
    Matrix ((TpIC 1 Unit × ZMod 2) × (Fin 1 → Database Unit (ZMod 2)))
      (Option (ZMod 2)) ℂ :=
  fun r a ↦ if cellEquiv r.2 = a then
    (if r.1.2 = 0 then cellAmp (ZMod 2) else -cellAmp (ZMod 2)) else 0

/-- The concrete purified extractor acts as the database phase on this sector. -/
theorem extractUnitary_phaseSector :
    extractUnitary phaseExtractor phaseCode * phaseSector = phaseSector * extractionPhase := by
  ext ⟨⟨tic, z⟩, d⟩ a
  rw [extractUnitary, basisMatrix_equiv_mul_apply]
  simp only [extractPerm, Equiv.coe_fn_symm_mk, phaseSector, phaseExtractor, phaseCode,
    extractionPhase, Matrix.mul_diagonal]
  by_cases hd : cellEquiv d = a
  · subst a
    by_cases h : cellEquiv d = some 0
    · have hz : z = 0 ∨ z = 1 := by
        exact Fin.cases (Or.inl rfl)
          (fun i ↦ Or.inr (by have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl)) z
      rcases hz with rfl | rfl <;> norm_num [h]
    · simp [h]
  · simp [hd]

/-- The extraction port of the runtime realizes the same phase on arbitrary states in the
phase-kickback sector. This equation includes the runtime's implemented extraction step. -/
theorem extraction_runtime_phase :
    (((compressedVCOracle 1 Unit (ZMod 2)).withExtract phaseExtractor phaseCode).toRuntime.step
        (.inr ())).branch () ∘ₗ MatrixMap.conj phaseSector =
      MatrixMap.conj phaseSector ∘ₗ MatrixMap.conj extractionPhase := by
  erw [EmulatedOracle.toRuntime_step_branch, VCOracle.withExtract_U_inr,
    ← MatrixMap.conj_mul, extractUnitary_phaseSector, MatrixMap.conj_mul]
  rfl

/-- Embed the phase sector in the extraction summand of the coherent call register. -/
noncomputable def mixedPhaseSector :
    Matrix ((EmulatedOracle.cohIn (extIn 1 Unit (ZMod 2) Unit (ZMod 2))) ×
      (Fin 1 → Database Unit (ZMod 2))) (Option (ZMod 2)) ℂ :=
  fun r a ↦ match r.1 with
    | ⟨.inl _, _⟩ => 0
    | ⟨.inr _, o⟩ => phaseSector (o, r.2) a

/-- Coherent selection of the extraction port preserves the phase-kickback sector. -/
theorem coherent_extract_phaseSector :
    (show Matrix ((EmulatedOracle.cohIn (extIn 1 Unit (ZMod 2) Unit (ZMod 2))) ×
        (Fin 1 → Database Unit (ZMod 2)))
      ((EmulatedOracle.cohIn (extIn 1 Unit (ZMod 2) Unit (ZMod 2))) ×
        (Fin 1 → Database Unit (ZMod 2))) ℂ from
      ((compressedVCOracle 1 Unit (ZMod 2)).withExtract phaseExtractor phaseCode).coherent.U ()) *
        mixedPhaseSector = mixedPhaseSector * extractionPhase := by
  ext ⟨⟨i, o⟩, d⟩ a
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma, Fintype.sum_sum_type, mixedPhaseSector, mul_zero,
    Finset.sum_const_zero, zero_add, Fintype.sum_unique]
  cases i with
  | inl i =>
    change (∑ o' : TpIC 1 Unit × ZMod 2, ∑ d' : Fin 1 → Database Unit (ZMod 2),
      (0 : ℂ) * phaseSector (o', d') a) =
        ∑ b : Option (ZMod 2), (0 : ℂ) * extractionPhase b a
    simp
  | inr u =>
    cases u
    change (∑ o', ∑ d', extractUnitary phaseExtractor phaseCode (o, d) (o', d') *
      phaseSector (o', d') a) = _
    have h := congrFun (congrFun extractUnitary_phaseSector (o, d)) a
    simpa only [Matrix.mul_apply, Fintype.sum_prod_type, mixedPhaseSector] using h

/-- The mixed extraction runtime's ordinary arm executes the purified extractor on its
extraction summand and therefore realizes the database phase. -/
theorem mixed_extraction_runtime_phase :
    (((compressedVCOracle 1 Unit (ZMod 2)).mixedExtractRuntime phaseExtractor phaseCode).step
        (.inl ())).branch () ∘ₗ MatrixMap.conj mixedPhaseSector =
      MatrixMap.conj mixedPhaseSector ∘ₗ MatrixMap.conj extractionPhase := by
  change MatrixMap.conj
    (((compressedVCOracle 1 Unit (ZMod 2)).withExtract phaseExtractor phaseCode).coherent.U ()) ∘ₗ
      MatrixMap.conj mixedPhaseSector = _
  erw [← MatrixMap.conj_mul, coherent_extract_phaseSector, MatrixMap.conj_mul]
  rfl

/-- The normalized residual state of the checked outcome `some 0`. -/
noncomputable def afterZero : Matrix (Option (ZMod 2)) (Option (ZMod 2)) ℂ :=
  readProjector (some 0)

/-- Extraction of the checked-zero state in the actual mixed runtime produces exactly the
phase-transformed state used in the probability calculation, with its output sector retained. -/
theorem runtime_extracted_input :
    (((compressedVCOracle 1 Unit (ZMod 2)).mixedExtractRuntime phaseExtractor phaseCode).step
        (.inl ())).branch () (MatrixMap.conj mixedPhaseSector afterZero) =
      MatrixMap.conj mixedPhaseSector (MatrixMap.conj extractionPhase afterZero) :=
  LinearMap.congr_fun mixed_extraction_runtime_phase afterZero

/-- The database-controlled phase is unitary. -/
theorem extractionPhase_unitary : extractionPhaseᴴ * extractionPhase = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i = some 0 <;>
      simp [extractionPhase, diagonal_conjTranspose, hi]
  · simp [extractionPhase, diagonal_conjTranspose, h]

/-- Conditioning on the present-zero outcome leaves a normalized state. -/
theorem afterZero_trace : afterZero.trace = 1 := by
  rw [afterZero, readProjector_eq, trace_mul_cycle, cellCompress_mul_self, Matrix.one_mul]
  simp [Matrix.trace]

/-- Extraction between repetitions changes the checked outcome distribution. -/
theorem extraction_between_probabilities (a : Option (ZMod 2)) :
    (MatrixMap.conj (readProjector a) (MatrixMap.conj extractionPhase afterZero)).trace =
      if a = none then (1 / 2 : ℂ) else 1 / 4 := by
  rw [MatrixMap.trace_conj_apply]
  have hp : (readProjector a)ᴴ * readProjector a = readProjector a := by
    simp only [readProjector, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, compressedReadProjector_hermitian,
      compressedReadProjector_orthogonal, ite_true]
  rw [hp]
  have hs : cellAmp (ZMod 2) ^ 2 = (1 / 2 : ℂ) := by
    simpa [pow_two, ZMod.card] using cellAmp_mul_self (ZMod 2)
  have hs4 : cellAmp (ZMod 2) ^ 4 = (1 / 4 : ℂ) := by
    calc
      _ = (cellAmp (ZMod 2) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs]; norm_num
  have hsum (f : ZMod 2 → ℂ) : ∑ x, f x = f 0 + f 1 := by
    change (∑ x : Fin 2, f x) = _
    exact Fin.sum_univ_two f
  have ha : a = none ∨ a = some 0 ∨ a = some 1 := by
    rcases a with _ | a
    · simp
    · fin_cases a <;> decide
  rcases ha with rfl | rfl | rfl
  all_goals
    norm_num [readProjector_eq, afterZero, extractionPhase, MatrixMap.conj_apply,
      Matrix.trace, Matrix.mul_apply, Fintype.sum_option, hsum,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply, cellCompress,
      map_ofNat, apply_ite (starRingEnd ℂ), star_cellAmp, ZMod.card]
    ring_nf
    norm_num [hs, hs4]

/-- The phase inserted after the first read prevents exact replay. -/
theorem extraction_breaks_replay :
    MatrixMap.conj (readProjector (some 0)) (MatrixMap.conj extractionPhase afterZero) ≠
      MatrixMap.conj extractionPhase afterZero := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [extraction_between_probabilities, MatrixMap.trace_conj_apply,
    extractionPhase_unitary, Matrix.one_mul, afterZero_trace] at ht
  norm_num at ht

/-- An extraction-produced input still permits exact replay when extraction precedes both reads. -/
example (a : Option (ZMod 2)) :
    MatrixMap.conj (readProjector a)
        (MatrixMap.conj (readProjector a) (MatrixMap.conj extractionPhase afterZero)) =
      MatrixMap.conj (readProjector a) (MatrixMap.conj extractionPhase afterZero) := by
  have hp : readProjector a * readProjector a = readProjector a := by
    simp only [readProjector, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      compressedReadProjector_orthogonal,
      ite_true]
  rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul, hp]

end ExtractionReplay

end VCVioTest.QuantumCheckedRead
