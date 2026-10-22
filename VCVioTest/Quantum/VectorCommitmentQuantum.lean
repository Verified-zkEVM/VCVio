/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.MultiExtractable

/-!
# Multi-extractable vector commitments: regression tests

Elaboration and non-vacuity tests for Def 7.3 of ePrint 2025/2166
(`VCVio.Quantum.VC.MultiExtractable`), on a toy instance: one scheme (`k = 1`) of length zero
with trivial commitments, openings and checks, the random-oracle model at the zero function as
the emulated oracle, and the constant extractor.

* The challengers of P3 and P4, the experiment, the five properties and the bundle elaborate on
  the toy instance; the reference model is the random-oracle model, the uniform distribution
  over all functions.
* The constant extractor is admissible (Def 7.1).
* `Quantum.run₂_extractQuery_branch` applies: on the toy instance the unique successful
  extraction branch, at `some tdm`, is the identity (the branch at `none` is zero), so extraction
  is lossless there.
* `Quantum.comError_of_pure` applies: its hypotheses hold for the program that returns at once,
  from a basis state. Since the zero oracle is the identity, the commutation defect vanishes and
  the distance is zero.
-/

public section

open Quantum Matrix OracleSpec
open scoped ENNReal Kronecker

namespace VCVioTest.QuantumVC

open EmulatedOracle (cohSpec)

/- Types are written as notations rather than constants, so that no finiteness instance is
evaluated when the module is loaded. -/

/-- The decommitments of the toy scheme: partial vectors of length zero, and unit trapdoors. -/
local notation "Dm0" => DmOf (k := 1) (fun _ ↦ 0) Bool (fun _ ↦ Unit)

/-- The extraction output register of the toy instance. -/
local notation "Z0" => ZMod (Fintype.card (TpD 1 Dm0) + 1)

/-- The coherent signature of `EO^(Ext)` on the toy instance. -/
local notation "extSpec" => cohSpec (extIn 1 (Fin 2) (Fin 2) Unit Z0)

local notation "mixedSpec" => mixedExtSpec 1 (Fin 2) (Fin 2) Unit Z0

/-- The trivial vector commitment of length zero: commitments, trapdoors and proofs are units,
and every check accepts. -/
def trivialVC : VectorCommitment (Fin 2) (Fin 2) Bool Unit Unit Unit 0 where
  commit _ := pure ((), ())
  opening _ _ := pure ()
  check _ _ _ := pure true

/-- The random-oracle model at the zero function, as an emulated oracle. -/
@[expose]
noncomputable def zeroOracle : VCOracle 1 (Fin 2) (Fin 2) :=
  romVCOracle 1 (Fin 2) (Fin 2) fun _ _ ↦ 0

/-- The constant extractor: every position extracts to the all-`⊥` decommitment. A notation
rather than a constant, since a constant of this type would enumerate a type at load. -/
local notation "toyME" =>
  (MultiExtractor.mk (fun _ _ _ ↦ (fun _ ↦ none, ())) : MultiExtractor 1 Unit Dm0 zeroOracle.S)

/-- The constant extractor is admissible. -/
theorem toyME_admissible : MultiExtractor.Admissible toyME fun _ ↦ ((fun _ ↦ none), ()) where
  eq_bot_of_not_injective _ _ _ _ := rfl
  prefix_eq _ _ _ _ _ _ := rfl

/-- The default encoding of extracted tuples. -/
noncomputable def code0 : TpDCode 1 Dm0 Z0 :=
  TpDCode.ofFintype

/-! ## Elaboration -/

/-- The P3 challenger on the toy instance. -/
noncomputable example (B : QReg) (c : ExtractClaim 1 Unit) : QComp mixedSpec B B Bool :=
  extractChallenger (fun _ ↦ trivialVC) code0 le_rfl 1 c B

/-- The P4 challenger on the toy instance. -/
noncomputable example (B : QReg) (c : OpeningClaim 1 Unit Bool (fun _ ↦ 0) fun _ ↦ Unit) :
    QComp mixedSpec B B Bool :=
  offlineChallenger (fun _ ↦ trivialVC) code0 le_rfl 0 c B

/-- A P3 adversary followed by the challenger, as one program. -/
noncomputable example {A : QReg} {W : QReg → Type}
    (x : QuantumComp LocalSig.instruments extSpec W A) (claim : ∀ u, W u → ExtractClaim 1 Unit) :
    QuantumComp LocalSig.instruments mixedSpec (fun _ ↦ Bool) A :=
  experiment x.liftOrdinary fun u y ↦
    extractChallenger (fun _ ↦ trivialVC) code0 le_rfl 1 (claim u y) u

/-- The random-oracle model over all functions, as the reference model of P1. -/
noncomputable def romRef (H : Fin 1 → Fin 2 → Fin 2) :
    QuantumRuntime (mixedOracleSpec 1 (Fin 2) (Fin 2)) :=
  (romVCOracle 1 (Fin 2) (Fin 2) H).mixedRuntime

/-- The five properties elaborate on the toy instance, against adversaries in `Type`. -/
example (κ : MEErrors) : Prop :=
  Simulates.{0, 0} (uniformWeights _) romRef zeroOracle κ.sim ∧ OraclesCommute zeroOracle ∧
    ComBound.{0, 0} zeroOracle toyME code0 κ.com ∧
    ExtractionCorrect.{0, 0} (fun _ ↦ trivialVC) zeroOracle toyME code0 κ.extract ∧
    OfflineExtractable.{0, 0} (fun _ ↦ trivialVC) zeroOracle toyME code0 κ.offline ∧
    OnlineIndistinguishable.{0, 0} zeroOracle toyME code0 κ.online

/-- The bundle of Def 7.3 elaborates on the toy instance, against adversaries in `Type`. -/
example (κ : MEErrors) : Prop :=
  IsMultiExtractable.{0, 0} (fun _ ↦ trivialVC) (fun _ ↦ ()) (uniformWeights _) romRef κ

/-! ## Extraction on the toy instance -/

/-- On the toy instance there is one decommitment tuple of each length, so every projector of
extraction is the identity. -/
theorem extractProj_toyME (tic : TpIC 1 Unit) (tdm : TpDLen 1 Dm0 tic.1) :
    extractProj toyME tic tdm = 1 := by
  ext s s'
  obtain rfl : (fun _ ↦ (fun _ ↦ none, ()) : TpDLen 1 Dm0 tic.1) = tdm := Subsingleton.elim _ _
  by_cases hs : s = s' <;> simp [extractProj, hs, one_apply]

/-- Non-vacuity of `Quantum.run₂_extractQuery_branch`: on the toy instance the unique successful
branch of extraction, at `some tdm`, is the identity. -/
example (B : QReg) (tic : TpIC 1 Unit) (tdm : TpDLen 1 Dm0 tic.1) :
    ((zeroOracle.withExtract toyME code0).coherent.toRuntime.run₂ .instruments
      (extractQuery code0 B tic)).branch (some tdm) = LinearMap.id := by
  rw [run₂_extractQuery_branch, extractProj_toyME, one_kronecker_one, MatrixMap.conj_one]
  rfl

/-! ## Checked reads -/

/-- A deterministic answer instrument on a trivial private register distinguishes absence
from a present zero answer. -/
@[expose]
noncomputable def answerOracle (answer : Option (Fin 2)) : VCOracle 1 (Fin 2) (Fin 2) where
  toEmulatedOracle := zeroOracle.toEmulatedOracle
  classicalRead := {
    A := fun _ a ↦ if a = answer then 1 else 0
    hermitian := by intros; split_ifs <;> simp
    orthogonal := by
      intro x a b
      by_cases ha : a = answer <;> by_cases hb : b = answer <;> simp_all [eq_comm]
    complete := by intro x; simp
    commute_cells := by intros; split_ifs <;> simp
    commute_ordinary := by intros; split_ifs <;> simp }

/-- Missing answers and present zero answers occupy distinct retained read branches. -/
example (B : QReg) (t : Fin 2) (answer a : Option (Fin 2)) :
    (((answerOracle answer).mixedExtractRuntime toyME code0).run₂ .instruments
      (checkedRead B 0 t)).branch a =
      if a = answer then LinearMap.id else 0 := by
  erw [branch_run₂_checkedRead]
  change MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
    (if a = answer then (1 : Matrix Unit Unit ℂ) else 0)) = _
  split_ifs <;> simp [MatrixMap.conj_one] <;> rfl

/-- The complete instrument retains the deterministic optional answer. -/
theorem run₂_read_answer (B : QReg) (t : Fin 2) (answer : Option (Fin 2)) :
    ((answerOracle answer).mixedExtractRuntime toyME code0).run₂ .instruments
      (checkedRead B 0 t) = SubInstrument.pure answer := by
  apply DSubInstrument.ext
  funext a
  erw [branch_run₂_checkedRead]
  change MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ
    (if a = answer then (1 : Matrix Unit Unit ℂ) else 0)) = _
  by_cases h : a = answer
  · subst a
    simp only [ite_true, one_kronecker_one, MatrixMap.conj_one]
    erw [SubInstrument.branch_pure_self]
    rfl
  · simp only [ite_eq_right h, kronecker_zero, MatrixMap.conj_zero]
    erw [SubInstrument.branch_pure_of_ne h]
    rfl

/-- A present zero is not a missing answer. -/
example (B : QReg) :
    (((answerOracle none).mixedExtractRuntime toyME code0).run₂ .instruments
      (checkedRead B 0 0)).branch (some 0) = 0 := by
  rw [run₂_read_answer]
  exact SubInstrument.branch_pure_of_ne (by simp)

/-- The classical one-query check of a zero answer. -/
def zeroCheck : OracleComp (unifSpec + (Fin 2 →ₒ Fin 2)) Bool := do
  let y : Fin 2 ← (unifSpec + (Fin 2 →ₒ Fin 2)).query (.inr 0)
  pure (y == 0)

/-- A one-query toy checker accepts exactly zero. -/
def queryVC : VectorCommitment (Fin 2) (Fin 2) Bool Unit Unit Unit 0 where
  commit _ := pure ((), ())
  opening _ _ := pure ()
  check _ _ _ := zeroCheck

/-- The optional result of the single-query classical check. -/
theorem runChecked_zeroCheck (B : QReg) :
    runClassicalChecked (Cm := Unit) (Z := Z0) B (0 : Fin 1) zeroCheck =
      QuantumComp₂.bind (checkedRead (X := Fin 2) (Y := Fin 2) (Cm := Unit) (Z := Z0)
        B (0 : Fin 1) 0) (fun a ↦
        match a with
        | none => QuantumComp₂.pure none
        | some y => QuantumComp₂.pure (some (y == 0))) := by
  unfold zeroCheck
  rw [runClassicalChecked_query_bind]
  change QuantumComp₂.bind
    (checkedRead (X := Fin 2) (Y := Fin 2) (Cm := Unit) (Z := Z0) B (0 : Fin 1) 0) _ = _
  apply congrArg (QuantumComp₂.bind
    (checkedRead (X := Fin 2) (Y := Fin 2) (Cm := Unit) (Z := Z0) B (0 : Fin 1) 0))
  funext a
  cases a <;> rfl

/-- The one-query checker maps its optional answer to an acceptance bit. -/
theorem checkAt_queryVC (B : QReg) (ans : PartialVec 0 Bool) :
    checkAt (Z := Z0) (fun _ : Fin 1 ↦ queryVC) B 0 0 () ans () =
      (checkedRead (X := Fin 2) (Y := Fin 2) (Cm := Unit) (Z := Z0) B (0 : Fin 1) 0).map
        (fun a ↦ (a.map (fun y ↦ y == 0)).getD false) := by
  simp only [checkAt, queryVC, runChecked_zeroCheck, QuantumComp₂.bind_eq,
    QuantumComp₂.bind_assoc, QuantumComp₂.map]
  apply congrArg (QuantumComp₂.bind
    (checkedRead (X := Fin 2) (Y := Fin 2) (Cm := Unit) (Z := Z0) B (0 : Fin 1) 0))
  funext a
  cases a <;> rfl

/-- A deterministic optional read decides the one-query checker without losing mass. -/
theorem run₂_check_of_read (R : QuantumRuntime mixedSpec) (B : QReg)
    (ans : PartialVec 0 Bool) (answer : Option (Fin 2))
    (hread : R.run₂ .instruments (checkedRead B 0 0) = SubInstrument.pure answer) :
    R.run₂ .instruments (checkAt (fun _ : Fin 1 ↦ queryVC) B 0 0 () ans ()) =
      SubInstrument.pure ((answer.map (fun y ↦ y == 0)).getD false) := by
  rw [checkAt_queryVC, QuantumRuntime.run₂_map, hread, SubInstrument.map_eq_bind_pure]
  exact SubInstrument.pure_bind answer _

/-- Missing answers reject while a present zero accepts, in the actual challenger checker. -/
theorem run₂_check_answer (B : QReg) (ans : PartialVec 0 Bool) (answer : Option (Fin 2)) :
    ((answerOracle answer).mixedExtractRuntime toyME code0).run₂ .instruments
      (checkAt (fun _ : Fin 1 ↦ queryVC) B 0 0 () ans ()) =
      SubInstrument.pure ((answer.map (fun y ↦ y == 0)).getD false) :=
  run₂_check_of_read _ B ans answer (run₂_read_answer B 0 answer)

example (B : QReg) (ans : PartialVec 0 Bool) :
    ((answerOracle none).mixedExtractRuntime toyME code0).run₂ .instruments
      (checkAt (fun _ : Fin 1 ↦ queryVC) B 0 0 () ans ()) = SubInstrument.pure false :=
  run₂_check_answer B ans none

example (B : QReg) (ans : PartialVec 0 Bool) :
    ((answerOracle (some 0)).mixedExtractRuntime toyME code0).run₂ .instruments
      (checkAt (fun _ : Fin 1 ↦ queryVC) B 0 0 () ans ()) = SubInstrument.pure true :=
  run₂_check_answer B ans (some 0)

/-- The zero real oracle returns a present zero, never a missing value. -/
example (B : QReg) (t : Fin 2) :
    ((zeroOracle.mixedExtractRuntime toyME code0).run₂ .instruments
      (checkedRead B 0 t)).branch none = 0 := by
  erw [run₂_checkedRead_rom]
  exact SubInstrument.branch_pure_of_ne (by simp)

/-- The toy check with an empty transcript. -/
def trivialIO : trivialVC.NonadaptiveCheck where
  pairs _ _ _ := some []
  check_eq _ _ _ := rfl
  qVC _ := 0
  qVC_mono := monotone_const
  length_le _ _ _ io h := by cases h; simp

/-- Malformed proof strings produce rejection. -/
def rejectingVC : VectorCommitment (Fin 2) (Fin 2) Bool Unit Unit Unit 0 :=
  { trivialVC with check := fun _ _ _ ↦ pure false }

/-- The malformed transcript form of the rejecting toy check. -/
def rejectingIO : rejectingVC.NonadaptiveCheck where
  pairs _ _ _ := none
  check_eq _ _ _ := rfl
  qVC _ := 0
  qVC_mono := monotone_const
  length_le _ _ _ io h := by cases h

/-- A malformed transcript rejects. -/
example (B : QReg) (ans : PartialVec 0 Bool) :
    checkAt (Z := Z0) (fun _ : Fin 1 ↦ rejectingVC) B 0 0 () ans () =
      QuantumComp₂.pure false :=
  checkAt_pairs_none _ _ rejectingIO _ _ _ _ _ rfl

/-- A present empty transcript accepts. -/
example (B : QReg) (ans : PartialVec 0 Bool) :
    checkAt (Z := Z0) (fun _ : Fin 1 ↦ trivialVC) B 0 0 () ans () =
      QuantumComp₂.pure true :=
  checkAt_pairs_nil _ _ trivialIO _ _ _ _ _ rfl

/-- The real checked interpreter preserves the complete joint law of a toy oracle check. -/
example (B : QReg) :
    (zeroOracle.mixedExtractRuntime toyME code0).run₂ .instruments
      (runClassicalChecked B 0 zeroCheck) =
    ((zeroOracle.mixedExtractRuntime toyME code0).run₂ .instruments
      (zeroCheck.toQuantumAt
        (QComp.coinImpl mixedSpec B +
          (fun _ ↦ QuantumComp₂.pure (0 : Fin 2) :
            QueryImpl (Fin 2 →ₒ Fin 2) (QComp mixedSpec B B))))).map some :=
  runClassicalChecked_rom (fun _ _ ↦ 0) toyME code0 B 0 _

/-! ## The pure form of P2's distance -/

/-- The oracle unitary of the zero oracle is the identity. -/
theorem zeroOracle_U (i : Fin 1) : zeroOracle.U i = 1 := by
  change oracleUnitary (0 : Fin 2 → Fin 2) ⊗ₖ (1 : Matrix Unit Unit ℂ) = 1
  rw [oracleUnitary_zero, one_kronecker_one]

/-- The commutation defect of the identity oracle with any extractor vanishes. -/
theorem comDefect_zeroOracle (Env : QReg) (i : Fin 1) :
    comDefect zeroOracle toyME code0 Env i = 0 := by
  rw [comDefect, zeroOracle_U, onFactor_one, Matrix.mul_one, Matrix.one_mul, sub_self]

/-- A product of basis states is the pure state of the basis vector of the pair. -/
theorem basis_kronecker_basis {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (a : A) (b : B) :
    (SubState.basis a).matrix ⊗ₖ (SubState.basis b).matrix =
      vecMulVec (Pi.single (a, b) 1) (star (Pi.single (a, b) 1)) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp only [SubState.matrix_basis, kroneckerMap_apply, single_apply, vecMulVec_apply,
    Pi.star_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Non-vacuity of `Quantum.comError_of_pure`: its hypotheses hold for the program that returns
at once, from a basis state, and on the toy instance the distance is zero. -/
example (Env : QReg) (a : ComOut 1 (Fin 2) (Fin 2) Unit Z0 Env) :
    comError zeroOracle toyME code0 0
      (QuantumComp₂.pure () : QuantumComp₂ LocalSig.instruments mixedSpec
        (ComOut 1 (Fin 2) (Fin 2) Unit Z0 Env) (ComOut 1 (Fin 2) (Fin 2) Unit Z0 Env) Unit)
      (SubState.basis a) = 0 := by
  rw [comError_of_pure zeroOracle toyME code0 () 1 (v := Pi.single (a, ()) 1)]
  · simp [comDefect_zeroOracle]
  · rw [QuantumRuntime.run₂_pure, SubInstrument.branch_pure_self, MatrixMap.conj_one]
    rfl
  · exact fun a h ↦ absurd rfl h
  · exact basis_kronecker_basis a ()

/-- Every read consumes one call even when the addresses are distinct. -/
noncomputable def twoReads : QuantumComp LocalSig.instruments mixedSpec (fun _ ↦ Unit)
    (QReg.of (Unit × Unit)) :=
  QuantumComp.queryBind (.inr (0, 0)) (QReg.of Unit) (Equiv.refl _) fun _ ↦
    QuantumComp.queryBind (.inr (0, 1)) (QReg.of Unit) (Equiv.refl _) fun _ ↦
      QuantumComp.pure ()

example : ¬ twoReads.IsTotalQueryBound 1 := by
  intro h
  have h₁ := (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mp h
  have h₂ := (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mp (h₁.2 none)
  exact h₂.1.false

example : twoReads.IsTotalQueryBound 2 := by
  apply (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
  refine ⟨by decide, fun _ ↦ ?_⟩
  apply (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
  exact ⟨by decide, fun _ ↦ QuantumComp.isTotalQueryBound_pure _ _⟩

example : ComBound.{0, 0} zeroOracle toyME code0 (fun _ ↦ 4) :=
  comBound_four zeroOracle toyME code0

end VCVioTest.QuantumVC
