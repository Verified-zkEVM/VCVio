/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public import VCVioComplexity.Backend.Polynomial

/-!
# End-to-end complexitylib canary for certified pure programs

This module instantiates VCVio's `PureCertificate` with actual complexitylib machines. The
program is intentionally tiny: identity on `PUnit`, over an interface with no query positions.
Nevertheless all three first-order machine maps contain exact `TM.reachesIn` evidence, their
charged maps have explicit polynomial work and size bounds, and the resulting theorem is a real
backend-relative `IsOraclePPTBy` statement rather than a zero-cost semantic fixture.

The canary does not claim the still-reserved unqualified `IsPPT`: that name additionally requires
the general oracle-machine compiler and adequacy theorem.
-/

@[expose] public section

namespace VCVioComplexity.Backend.TuringMachine

open PFunctor
open PFunctor.DynSystem.DynComputation
open OracleComp.Complexity
open _root_.Complexity

local instance : stepClass.HasProd := hasProd
local instance : stepClass.HasSum := hasSum
local instance : stepClass.HasOption := hasOption

/-! ## A concrete machine which writes the left sum tag -/

/-- Three finite control states of the constant-false writer. -/
abbrev FalseTagState := Fin 3

abbrev falseTagStart : FalseTagState := 0
abbrev falseTagWrite : FalseTagState := 1
abbrev falseTagHalt : FalseTagState := 2

/-- Two-step machine which moves onto output cell one, writes `false`, and halts. -/
def falseTagMachine : _root_.Complexity.TM 0 where
  Q := FalseTagState
  qstart := falseTagStart
  qhalt := falseTagHalt
  δ := fun state inputHead _ outputHead =>
    (if state = falseTagStart then falseTagWrite else falseTagHalt,
    fun index ↦ Fin.elim0 index,
    if state = falseTagWrite then .zero else .blank,
    Primitive.safeDirection inputHead,
    fun index ↦ Fin.elim0 index,
    Primitive.safeDirection outputHead)
  δ_right_of_start := by
    intro state inputHead workHeads outputHead
    simp only
    constructor
    · intro h
      simp [Primitive.safeDirection, h]
    constructor
    · intro index
      exact Fin.elim0 index
    · intro h
      simp [Primitive.safeDirection, h]

/-- Configuration after moving every head right from its left-end marker. -/
def falseTagMiddle (word : Word) :
    _root_.Complexity.Cfg 0 falseTagMachine.Q where
  state := falseTagWrite
  input := (_root_.Complexity.Tape.init (word.map _root_.Complexity.Γ.ofBool)).move .right
  work := fun index ↦ Fin.elim0 index
  output := (_root_.Complexity.Tape.init []).move .right

/-- Halting configuration after writing the false tag in output cell one. -/
def falseTagFinal (word : Word) :
    _root_.Complexity.Cfg 0 falseTagMachine.Q where
  state := falseTagHalt
  input :=
    let tape := (falseTagMiddle word).input
    tape.move (Primitive.safeDirection tape.read)
  work := fun index ↦ Fin.elim0 index
  output :=
    let tape := (falseTagMiddle word).output
    tape.writeAndMove _root_.Complexity.Γ.zero
      (Primitive.safeDirection tape.read)

@[simp]
theorem falseTagMachine_step_init (word : Word) :
    falseTagMachine.step (falseTagMachine.initCfg word) = some (falseTagMiddle word) := by
  have empty_work (left right : Fin 0 → _root_.Complexity.Tape) : left = right := by
    funext index
    exact Fin.elim0 index
  simpa [falseTagMachine, falseTagMiddle, _root_.Complexity.TM.step,
    Primitive.safeDirection, _root_.Complexity.Tape.write,
    _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
    _root_.Complexity.Tape.init] using
      And.intro (show ¬falseTagStart = falseTagHalt by decide) (empty_work _ _)

@[simp]
theorem falseTagMachine_step_middle (word : Word) :
    falseTagMachine.step (falseTagMiddle word) = some (falseTagFinal word) := by
  have empty_work (left right : Fin 0 → _root_.Complexity.Tape) : left = right := by
    funext index
    exact Fin.elim0 index
  simpa [falseTagMachine, falseTagMiddle, falseTagFinal, _root_.Complexity.TM.step,
    Primitive.safeDirection, _root_.Complexity.Tape.write,
    _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
    _root_.Complexity.Tape.init] using
      And.intro (show ¬falseTagWrite = falseTagHalt by decide) (empty_work _ _)

/-- Exact two-step run of the false-tag writer. -/
def falseTagRun (word : Word) : ExactRun falseTagMachine word [false] where
  final := falseTagFinal word
  steps := 2
  reaches := .step (falseTagMachine_step_init word) <|
    .step (falseTagMachine_step_middle word) .zero
  halted := rfl
  output_correct := by
    constructor
    · intro index hindex
      have hzero : index = 0 := by
        simp only [List.length_cons, List.length_nil] at hindex
        omega
      subst hzero
      simp [falseTagFinal, falseTagMiddle, _root_.Complexity.Tape.writeAndMove,
        _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
        _root_.Complexity.Tape.read, _root_.Complexity.Tape.init,
        _root_.Complexity.Γ.ofBool, Primitive.safeDirection]
    · simp [falseTagFinal, falseTagMiddle, _root_.Complexity.Tape.writeAndMove,
        _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
        _root_.Complexity.Tape.read, _root_.Complexity.Tape.init,
        Primitive.safeDirection]

/-! ## Exact codes for the pure realization -/

/-- The PFunctor with no possible query position. -/
abbrev noQuery : PFunctor.{0, 0} := 0

/-- Trusted empty representation for the absent position type. -/
def noQueryPosition : Representation noQuery.A :=
  .empty PEmpty.elim

/-- Trusted empty representation for the absent dependent answer index. -/
def noQueryIndex : Representation noQuery.Idx :=
  .empty fun index ↦ index.1.elim

/-- Pinned boundary of the unit canary. -/
def unitBoundary : Boundary stepClass noQuery PUnit PUnit where
  input := .unit
  out := .unit
  pos := noQueryPosition
  idx := noQueryIndex

/-- Concrete product representation used by the unreachable transition. -/
def unitStateIndexRepresentation : Representation (PUnit × noQuery.Idx) :=
  .prod .unit noQueryIndex

/-- Concrete option representation used by the unreachable transition. -/
def unitOptionRepresentation : Representation (Option PUnit) :=
  .option .unit

/-- Exact code for the resolved `Sum.inl` readout. -/
def falseTagCode : Code Representation.unit unitBoundary.head
    (Sum.inl : PUnit → PUnit ⊕ noQuery.A) where
  workTapes := 0
  machine := falseTagMachine
  wordFunction := fun _ ↦ [false]
  run := falseTagRun
  encode_eq value := by cases value; rfl

/-- Exact code for the unreachable partial transition of the pure machine. -/
def emptyUpdateCode : Code unitStateIndexRepresentation unitOptionRepresentation
    (PFunctor.DynSystem.DynComputation.ofFn (p := noQuery) id).update? where
  workTapes := 0
  machine := Primitive.haltMachine
  wordFunction := fun _ ↦ []
  run := Primitive.haltRun
  encode_eq input := input.2.1.elim

/-- Polynomial certificate for the unit identity's initialization. -/
def unitResultPolyRealizer : quantitativeStepClass.PolyRealizer
    Representation.unit Representation.unit id where
  code := (Primitive.unitCode Representation.unit).castFunction (by
    funext value
    cases value
    rfl)
  work := FirstOrderPolynomial.const 0
  outputSize := FirstOrderPolynomial.const 0
  work_le value := by cases value; rfl
  outputSize_le value := by cases value; rfl

/-- Polynomial certificate for the exact two-step resolved readout. -/
def falseTagPolyRealizer : quantitativeStepClass.PolyRealizer
    Representation.unit unitBoundary.head (Sum.inl : PUnit → PUnit ⊕ noQuery.A) where
  code := falseTagCode
  work := FirstOrderPolynomial.const 2
  outputSize := FirstOrderPolynomial.const 1
  work_le value := by cases value; exact le_rfl
  outputSize_le value := by cases value; exact le_rfl

/-- The returned unit payload cannot be hidden by its tagged readout representation. -/
def unitOutputRecovery : quantitativeStepClass.PolyOutputSizeRecovery unitBoundary where
  polynomial := FirstOrderPolynomial.const 0
  output_le value := by
    cases value
    rfl

/-- All concrete code required by VCVio's certified-pure constructor. -/
def unitPureCertificate : PureCertificate quantitativeStepClass unitBoundary id where
  result := unitResultPolyRealizer
  head := falseTagPolyRealizer
  outputRecovery := unitOutputRecovery
  update := emptyUpdateCode

/-- A canonical singleton-model contract over the empty interface. -/
def noQueryResourceModel : OracleResourceModel quantitativeStepClass unitBoundary.interface
    (fun position ↦ (position.elim : PEmpty)) where
  allows := fun position ↦ position.elim
  responseSize := fun interface ↦ interface.elim
  responseSize_monotone := fun interface ↦ interface.elim
  responseSize_le := fun position ↦ position.elim

/-- Canonical nonvacuous resource contract for the empty interface. -/
def noQueryContract : OracleContract quantitativeStepClass unitBoundary.interface PEmpty where
  labelOf := PEmpty.elim
  admissible model := model = noQueryResourceModel
  model_nonempty := ⟨noQueryResourceModel, rfl⟩

/-- End-to-end backend-relative strict-PPT theorem backed by exact complexitylib runs. -/
theorem unitIdentity_isOraclePPTBy :
    IsOraclePPTBy quantitativeStepClass unitBoundary noQueryContract
      (fun value ↦ FreeM.pure (id value)) :=
  unitPureCertificate.isOraclePPTBy noQueryContract

end VCVioComplexity.Backend.TuringMachine
