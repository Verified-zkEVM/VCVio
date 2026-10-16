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
noncomputable example (B : QReg) (c : ExtractClaim 1 Unit) : QComp extSpec B B Bool :=
  extractChallenger (fun _ ↦ trivialVC) code0 le_rfl 1 c B

/-- The P4 challenger on the toy instance. -/
noncomputable example (B : QReg) (c : OpeningClaim 1 Unit Bool (fun _ ↦ 0) fun _ ↦ Unit) :
    QComp extSpec B B Bool :=
  offlineChallenger (fun _ ↦ trivialVC) code0 le_rfl 0 c B

/-- A P3 adversary followed by the challenger, as one program. -/
noncomputable example {A : QReg} {W : QReg → Type}
    (x : QuantumComp LocalSig.instruments extSpec W A) (claim : ∀ u, W u → ExtractClaim 1 Unit) :
    QuantumComp LocalSig.instruments extSpec (fun _ ↦ Bool) A :=
  experiment x fun u y ↦ extractChallenger (fun _ ↦ trivialVC) code0 le_rfl 1 (claim u y) u

/-- The random-oracle model over all functions, as the reference model of P1. -/
noncomputable def romRef (H : Fin 1 → Fin 2 → Fin 2) :
    QuantumRuntime (cohSpec (oIn 1 (Fin 2) (Fin 2))) :=
  (romVCOracle 1 (Fin 2) (Fin 2) H).coherent.toRuntime

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
      (QuantumComp₂.pure () : QuantumComp₂ LocalSig.instruments extSpec
        (ComOut 1 (Fin 2) (Fin 2) Unit Z0 Env) (ComOut 1 (Fin 2) (Fin 2) Unit Z0 Env) Unit)
      (SubState.basis a) = 0 := by
  rw [comError_of_pure zeroOracle toyME code0 () 1 (v := Pi.single (a, ()) 1)]
  · simp [comDefect_zeroOracle]
  · rw [QuantumRuntime.run₂_pure, SubInstrument.branch_pure_self, MatrixMap.conj_one]
    rfl
  · exact fun a h ↦ absurd rfl h
  · exact basis_kronecker_basis a ()

end VCVioTest.QuantumVC
