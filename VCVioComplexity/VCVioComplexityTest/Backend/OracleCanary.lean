/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioComplexityTest.Backend.PureCanary
public import VCVio.EvalDist.PFunctorPath

/-!
# Test fixture: one-query complexitylib program

This module certifies a program which makes exactly one fair-coin query and returns its reply.
Unlike the pure canary, both Boolean replies are admitted and charged, the enabled update map has
inhabited inputs, and the resource proof accounts for both readouts, the update, one visible query,
encoded query-answer traffic, and reachable progress.

Every first-order map is backed by one concrete deterministic complexitylib Turing machine with an
exact `TM.reachesIn` run. The final result remains deliberately backend-relative
`IsOraclePPTBy`; no whole-oracle-machine compiler or unqualified `IsPPT` theorem is claimed.
-/

@[expose] public section

namespace VCVioComplexity.Backend.TuringMachine

open PFunctor
open PFunctor.DynSystem
open PFunctor.DynSystem.DynComputation
open OracleComp.Complexity
open _root_.Complexity
open MeasureTheory ProbabilityTheory
open scoped ENNReal

local instance : stepClass.HasProd := hasProd
local instance : stepClass.HasSum := hasSum
local instance : stepClass.HasOption := hasOption

/-! ## Representations and the one-query state machine -/

/-- Representation of the hidden state: `none` is the pending query and `some bit` has returned. -/
def coinStateRepresentation : Representation (Option Bool) :=
  .option .bool

/-- Representation of the dependent fair-coin answer index. -/
def coinIndexRepresentation : Representation coinSpec.toPFunctor.Idx :=
  .sigma .unit (fun _ ↦ .bool)

/-- Pinned boundary for a unit-indexed computation returning its fair-coin reply. -/
def coinBoundary : Boundary stepClass coinSpec.toPFunctor Unit Bool where
  input := .unit
  out := .bool
  pos := .unit
  idx := coinIndexRepresentation

/-- One-step view of the one-query machine. -/
def coinView : Option Bool → Bool ⊕ coinSpec.toPFunctor.Obj (Option Bool)
  | none => Sum.inr ⟨(), fun answer ↦ some answer⟩
  | some answer => Sum.inl answer

/-- A finite-state machine which asks once and then returns the supplied answer. -/
def oneCoinMachine : DynComputation coinSpec.toPFunctor Unit Bool where
  State := Option Bool
  toDynSystem :=
    (fun state ↦ (Resumption.pack (coinView state)).1) ⇆
      fun state ↦ (Resumption.pack (coinView state)).2
  init := fun _ ↦ none

@[simp]
theorem oneCoinMachine_init (input : Unit) : oneCoinMachine.init input = none :=
  rfl

@[simp]
theorem oneCoinMachine_view_none : oneCoinMachine.view none =
    Sum.inr ⟨(), fun answer ↦ some answer⟩ := by
  change Resumption.unpack (Resumption.pack (coinView none)) = _
  exact Resumption.unpack_pack _

@[simp]
theorem oneCoinMachine_view_some (answer : Bool) :
    oneCoinMachine.view (some answer) = Sum.inl answer := by
  change Resumption.unpack (Resumption.pack (coinView (some answer))) = _
  exact Resumption.unpack_pack _

@[simp]
theorem oneCoinMachine_head_none : oneCoinMachine.head none = Sum.inr () :=
  oneCoinMachine.head_eq_inr_of_view oneCoinMachine_view_none

@[simp]
theorem oneCoinMachine_head_some (answer : Bool) :
    oneCoinMachine.head (some answer) = Sum.inl answer :=
  oneCoinMachine.head_eq_inl_of_view (oneCoinMachine_view_some answer)

/-- The free program implemented by `oneCoinMachine`. -/
def oneCoinProgram (_ : Unit) : FreeM coinSpec.toPFunctor Bool :=
  FreeM.liftBind () fun answer ↦ FreeM.pure answer

/-- The one-query program presented through VCVio's `OracleComp` facade. -/
def oneCoinOracleProgram (_ : Unit) : OracleComp coinSpec Bool :=
  OracleComp.ofFreeM (oneCoinProgram ())

@[simp]
theorem oneCoinOracleProgram_toFreeM (input : Unit) :
    (oneCoinOracleProgram input).toFreeM = oneCoinProgram input := by
  cases input
  rfl

/-! ## Native measure semantics -/

/-- The native fair-coin interpretation is selected explicitly for this canary. -/
@[instance_reducible]
noncomputable def oneCoinMeasureSpec : coinSpec.toPFunctor.IsMeasureSpec :=
  IsMeasureSpec.uniformOfFintypeInhabited _

attribute [local instance] oneCoinMeasureSpec

/-- The one-query program directly denotes the uniform measure on Boolean answers. -/
theorem oneCoinProgram_denote_eq_uniformOn (input : Unit) :
    FreeM.denote (oneCoinProgram input) = (uniformOn Set.univ : Measure Bool) := by
  cases input
  change FreeM.denote (FreeM.lift (P := coinSpec.toPFunctor) ()) = _
  rw [FreeM.denote_lift (P := coinSpec.toPFunctor)]
  rfl

/-- The query-count measure of the one-query program is concentrated at one. -/
theorem oneCoinProgram_queryCountMeasure_eq_dirac (input : Unit) :
    FreeM.queryCountMeasure (oneCoinProgram input) = Measure.dirac 1 := by
  cases input
  apply FreeM.queryCountMeasure_eq_dirac_of_length_eq (P := coinSpec.toPFunctor) _ 1
  rintro ⟨answer, tail⟩
  rcases tail with ⟨⟩
  rfl

/-- The expected query count of the one-query program is exactly one. -/
theorem oneCoinProgram_expectedQueryCount_eq_one (input : Unit) :
    FreeM.expectedQueryCount (oneCoinProgram input) = (1 : ℝ≥0∞) := by
  unfold FreeM.expectedQueryCount
  rw [oneCoinProgram_queryCountMeasure_eq_dirac]
  simp

/-- Residual-program relation used to prove semantic implementation. -/
inductive CoinResidual : Option Bool → FreeM coinSpec.toPFunctor Bool → Prop where
  | start : CoinResidual none (oneCoinProgram ())
  | done (answer : Bool) : CoinResidual (some answer) (FreeM.pure answer)

/-- The finite-state one-query machine simulates the canonical residual-program machine. -/
theorem oneCoinSimulation : IsSimulation oneCoinMachine.toDynSystem
    (DynComputation.ofFreeM oneCoinProgram).toDynSystem CoinResidual where
  expose_eq := by
    intro state residual related
    cases related <;> rfl
  update_rel := by
    intro state residual related direction
    cases related with
    | start => exact CoinResidual.done direction
    | done answer => exact PEmpty.elim direction

/-- `oneCoinMachine` implements a genuine query and returns either supplied Boolean reply. -/
theorem oneCoinMachine_implements : oneCoinMachine.Implements oneCoinProgram := by
  apply implements_of_isSimulation oneCoinMachine oneCoinProgram CoinResidual oneCoinSimulation
  intro input
  cases input
  exact CoinResidual.start

/-! ## Shared exact-machine helpers -/

/-- Convert a readable tape symbol into the corresponding writable symbol, using blank for the
left marker. -/
def writableOfRead : _root_.Complexity.Γ → _root_.Complexity.Γw
  | .zero => .zero
  | .one => .one
  | .blank => .blank
  | .start => .blank

@[simp]
theorem writableOfRead_ofBool (bit : Bool) :
    writableOfRead (_root_.Complexity.Γ.ofBool bit) =
      _root_.Complexity.Γw.ofBool bit := by
  cases bit <;> rfl

@[simp]
theorem writableOfRead_ofBool_toΓ (bit : Bool) :
    (writableOfRead (_root_.Complexity.Γ.ofBool bit)).toΓ =
      _root_.Complexity.Γ.ofBool bit := by
  cases bit <;> rfl

/-- All families of tapes indexed by the empty finite type are equal. -/
theorem finZeroTape_funext (left right : Fin 0 → _root_.Complexity.Tape) : left = right := by
  funext index
  exact Fin.elim0 index

/-! ## Exact readout code -/

/-- Control states of the fixed-three-step readout transducer. -/
abbrev HeadState := Fin 5

abbrev headStart : HeadState := 0
abbrev headInspect : HeadState := 1
abbrev headQuery : HeadState := 2
abbrev headReturn : HeadState := 3
abbrev headHalt : HeadState := 4

/-- A three-step transducer for `coinView` on the trusted optional-Boolean encoding. -/
def coinHeadMachine : _root_.Complexity.TM 0 where
  Q := HeadState
  qstart := headStart
  qhalt := headHalt
  δ := fun state inputHead _ _ =>
    (if state = headStart then headInspect
      else if state = headInspect then
        if inputHead = .blank then headQuery else headReturn
      else headHalt,
    fun index ↦ Fin.elim0 index,
    if state = headStart then .blank
      else if state = headInspect then
        if inputHead = .blank then .one else .zero
      else if state = headReturn then writableOfRead inputHead else .blank,
    .right,
    fun index ↦ Fin.elim0 index,
    .right)
  δ_right_of_start := by
    intro state inputHead workHeads outputHead
    exact ⟨fun _ ↦ rfl, fun index ↦ Fin.elim0 index, fun _ ↦ rfl⟩

/-- Configuration after moving the input and output heads onto cell one. -/
def coinHeadFirst (word : Word) : _root_.Complexity.Cfg 0 coinHeadMachine.Q where
  state := headInspect
  input := (_root_.Complexity.Tape.init (word.map _root_.Complexity.Γ.ofBool)).move .right
  work := fun index ↦ Fin.elim0 index
  output := (_root_.Complexity.Tape.init []).move .right

/-- Configuration after writing the return/query tag. -/
def coinHeadSecond (word : Word) : _root_.Complexity.Cfg 0 coinHeadMachine.Q :=
  let first := coinHeadFirst word
  { state := if first.input.read = .blank then headQuery else headReturn
    input := first.input.move .right
    work := fun index ↦ Fin.elim0 index
    output := first.output.writeAndMove
      (if first.input.read = .blank then Γw.one else Γw.zero).toΓ .right }

/-- Halting configuration after writing the optional Boolean payload. -/
def coinHeadFinal (word : Word) : _root_.Complexity.Cfg 0 coinHeadMachine.Q :=
  let first := coinHeadFirst word
  let second := coinHeadSecond word
  { state := headHalt
    input := second.input.move .right
    work := fun index ↦ Fin.elim0 index
    output := second.output.writeAndMove
      (if first.input.read = .blank then Γw.blank
        else writableOfRead second.input.read).toΓ .right }

@[simp]
theorem coinHeadMachine_step_init (word : Word) :
    coinHeadMachine.step (coinHeadMachine.initCfg word) = some (coinHeadFirst word) := by
  simpa [coinHeadMachine, coinHeadFirst, _root_.Complexity.TM.step,
    _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
    _root_.Complexity.Tape.read, _root_.Complexity.Tape.init] using
      And.intro (show ¬headStart = headHalt by decide) (finZeroTape_funext _ _)

@[simp]
theorem coinHeadMachine_step_first (word : Word) :
    coinHeadMachine.step (coinHeadFirst word) = some (coinHeadSecond word) := by
  simpa [coinHeadMachine, coinHeadFirst, coinHeadSecond, _root_.Complexity.TM.step,
    _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
    _root_.Complexity.Tape.read, _root_.Complexity.Tape.init] using
      And.intro (show ¬headInspect = headHalt by decide) (finZeroTape_funext _ _)

@[simp]
theorem coinHeadMachine_step_second (word : Word) :
    coinHeadMachine.step (coinHeadSecond word) = some (coinHeadFinal word) := by
  cases word with
  | nil =>
      simpa [coinHeadMachine, coinHeadFirst, coinHeadSecond, coinHeadFinal,
        _root_.Complexity.TM.step, _root_.Complexity.Tape.write,
        _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
        _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
        _root_.Complexity.Γw.toΓ, writableOfRead, headStart, headInspect, headQuery,
        headReturn, headHalt] using (finZeroTape_funext _ _)
  | cons bit rest =>
      cases bit <;>
        simpa [coinHeadMachine, coinHeadFirst, coinHeadSecond, coinHeadFinal,
          _root_.Complexity.TM.step, _root_.Complexity.Tape.write,
          _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
          _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
          _root_.Complexity.Γ.ofBool_ne_blank, _root_.Complexity.Γw.toΓ,
          writableOfRead, headStart, headInspect, headQuery, headReturn,
          headHalt] using (finZeroTape_funext _ _)

/-- Total raw-word function computed by `coinHeadMachine`. -/
def coinHeadWordFunction : Word → Word
  | [] => [true]
  | _ :: [] => [false]
  | _ :: answer :: _ => [false, answer]

/-- Exact three-step run of the readout transducer on every raw word. -/
def coinHeadRun (word : Word) :
    ExactRun coinHeadMachine word (coinHeadWordFunction word) where
  final := coinHeadFinal word
  steps := 3
  reaches := .step (coinHeadMachine_step_init word) <|
    .step (coinHeadMachine_step_first word) <|
      .step (coinHeadMachine_step_second word) .zero
  halted := rfl
  output_correct := by
    cases word with
    | nil =>
        constructor
        · intro index hindex
          simp only [coinHeadWordFunction, List.length_cons, List.length_nil] at hindex
          have : index = 0 := by omega
          subst index
          simp [coinHeadFinal, coinHeadSecond, coinHeadFirst, coinHeadWordFunction,
            _root_.Complexity.Tape.writeAndMove, _root_.Complexity.Tape.write,
            _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
            _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
            _root_.Complexity.Γw.toΓ]
        · simp [coinHeadFinal, coinHeadSecond, coinHeadFirst, coinHeadWordFunction,
            _root_.Complexity.Tape.writeAndMove, _root_.Complexity.Tape.write,
            _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
            _root_.Complexity.Tape.init, _root_.Complexity.Γw.toΓ]
    | cons first rest =>
        cases rest with
        | nil =>
            cases first <;> constructor
            · intro index hindex
              simp only [coinHeadWordFunction, List.length_cons, List.length_nil] at hindex
              have : index = 0 := by omega
              subst index
              simp [coinHeadFinal, coinHeadSecond, coinHeadFirst, coinHeadWordFunction,
                _root_.Complexity.Tape.writeAndMove, _root_.Complexity.Tape.write,
                _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
                _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
                _root_.Complexity.Γw.toΓ]
            · simp [coinHeadFinal, coinHeadSecond, coinHeadFirst, coinHeadWordFunction,
                _root_.Complexity.Tape.writeAndMove, _root_.Complexity.Tape.write,
                _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
                _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
                _root_.Complexity.Γw.toΓ, writableOfRead]
            · intro index hindex
              simp only [coinHeadWordFunction, List.length_cons, List.length_nil] at hindex
              have : index = 0 := by omega
              subst index
              simp [coinHeadFinal, coinHeadSecond, coinHeadFirst, coinHeadWordFunction,
                _root_.Complexity.Tape.writeAndMove, _root_.Complexity.Tape.write,
                _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
                _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
                _root_.Complexity.Γw.toΓ]
            · simp [coinHeadFinal, coinHeadSecond, coinHeadFirst, coinHeadWordFunction,
                _root_.Complexity.Tape.writeAndMove, _root_.Complexity.Tape.write,
                _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
                _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
                _root_.Complexity.Γw.toΓ, writableOfRead]
        | cons answer rest =>
            cases first <;> cases answer
            all_goals
              constructor
              · intro index hindex
                simp only [coinHeadWordFunction, List.length_cons, List.length_nil] at hindex
                have : index = 0 ∨ index = 1 := by omega
                rcases this with rfl | rfl <;>
                  simp [coinHeadFinal, coinHeadSecond, coinHeadFirst,
                    coinHeadWordFunction, _root_.Complexity.Tape.writeAndMove,
                    _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
                    _root_.Complexity.Tape.read, _root_.Complexity.Tape.init,
                    _root_.Complexity.Γ.ofBool, _root_.Complexity.Γw.toΓ,
                    writableOfRead]
              · simp [coinHeadFinal, coinHeadSecond, coinHeadFirst,
                  coinHeadWordFunction, _root_.Complexity.Tape.writeAndMove,
                  _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
                  _root_.Complexity.Tape.read, _root_.Complexity.Tape.init,
                  _root_.Complexity.Γ.ofBool, _root_.Complexity.Γw.toΓ,
                  writableOfRead]

/-! ## Exact update code -/

/-- Control states of the fixed-four-step enabled-update transducer. -/
abbrev UpdateState := Fin 7

abbrev updateStart : UpdateState := 0
abbrev updateInspect : UpdateState := 1
abbrev updateEmitInner : UpdateState := 2
abbrev updateCopy : UpdateState := 3
abbrev updateNoneFirst : UpdateState := 4
abbrev updateNoneSecond : UpdateState := 5
abbrev updateHalt : UpdateState := 6

/-- A four-step transducer for the flattened partial update map. -/
def coinUpdateMachine : _root_.Complexity.TM 0 where
  Q := UpdateState
  qstart := updateStart
  qhalt := updateHalt
  δ := fun state inputHead _ _ =>
    (if state = updateStart then updateInspect
      else if state = updateInspect then
        if inputHead = .one then updateEmitInner else updateNoneFirst
      else if state = updateEmitInner then updateCopy
      else if state = updateNoneFirst then updateNoneSecond
      else updateHalt,
    fun index ↦ Fin.elim0 index,
    if state = updateInspect then
        if inputHead = .one then .one else .blank
      else if state = updateEmitInner then .one
      else if state = updateCopy then writableOfRead inputHead
      else .blank,
    .right,
    fun index ↦ Fin.elim0 index,
    .right)
  δ_right_of_start := by
    intro state inputHead workHeads outputHead
    exact ⟨fun _ ↦ rfl, fun index ↦ Fin.elim0 index, fun _ ↦ rfl⟩

/-- First configuration of the update transducer. -/
def coinUpdateFirst (word : Word) : _root_.Complexity.Cfg 0 coinUpdateMachine.Q where
  state := updateInspect
  input := (_root_.Complexity.Tape.init (word.map _root_.Complexity.Γ.ofBool)).move .right
  work := fun index ↦ Fin.elim0 index
  output := (_root_.Complexity.Tape.init []).move .right

/-- Configuration after inspecting whether the paired state encoding is empty. -/
def coinUpdateSecond (word : Word) : _root_.Complexity.Cfg 0 coinUpdateMachine.Q :=
  let first := coinUpdateFirst word
  { state := if first.input.read = .one then updateEmitInner else updateNoneFirst
    input := first.input.move .right
    work := fun index ↦ Fin.elim0 index
    output := first.output.writeAndMove
      (if first.input.read = .one then Γw.one else Γw.blank).toΓ .right }

/-- Configuration after emitting the nested optional tag or taking the no-update padding branch. -/
def coinUpdateThird (word : Word) : _root_.Complexity.Cfg 0 coinUpdateMachine.Q :=
  let first := coinUpdateFirst word
  let second := coinUpdateSecond word
  { state := if first.input.read = .one then updateCopy else updateNoneSecond
    input := second.input.move .right
    work := fun index ↦ Fin.elim0 index
    output := second.output.writeAndMove
      (if first.input.read = .one then Γw.one else Γw.blank).toΓ .right }

/-- Halting update configuration after copying the admitted Boolean response. -/
def coinUpdateFinal (word : Word) : _root_.Complexity.Cfg 0 coinUpdateMachine.Q :=
  let first := coinUpdateFirst word
  let third := coinUpdateThird word
  { state := updateHalt
    input := third.input.move .right
    work := fun index ↦ Fin.elim0 index
    output := third.output.writeAndMove
      (if first.input.read = .one then writableOfRead third.input.read
        else Γw.blank).toΓ .right }

@[simp]
theorem coinUpdateMachine_step_init (word : Word) :
    coinUpdateMachine.step (coinUpdateMachine.initCfg word) = some (coinUpdateFirst word) := by
  simpa [coinUpdateMachine, coinUpdateFirst, _root_.Complexity.TM.step,
    _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
    _root_.Complexity.Tape.read, _root_.Complexity.Tape.init] using
      And.intro (show ¬updateStart = updateHalt by decide) (finZeroTape_funext _ _)

@[simp]
theorem coinUpdateMachine_step_first (word : Word) :
    coinUpdateMachine.step (coinUpdateFirst word) = some (coinUpdateSecond word) := by
  simpa [coinUpdateMachine, coinUpdateFirst, coinUpdateSecond, _root_.Complexity.TM.step,
    _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
    _root_.Complexity.Tape.read, _root_.Complexity.Tape.init] using
      And.intro (show ¬updateInspect = updateHalt by decide) (finZeroTape_funext _ _)

@[simp]
theorem coinUpdateMachine_step_second (word : Word) :
    coinUpdateMachine.step (coinUpdateSecond word) = some (coinUpdateThird word) := by
  cases word with
  | nil =>
      simpa [coinUpdateMachine, coinUpdateFirst, coinUpdateSecond, coinUpdateThird,
        _root_.Complexity.TM.step, _root_.Complexity.Tape.write,
        _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
        _root_.Complexity.Tape.init, _root_.Complexity.Γw.toΓ, writableOfRead,
        updateStart, updateInspect, updateEmitInner, updateCopy, updateNoneFirst,
        updateNoneSecond, updateHalt] using (finZeroTape_funext _ _)
  | cons bit rest =>
      cases bit <;>
        simpa [coinUpdateMachine, coinUpdateFirst, coinUpdateSecond, coinUpdateThird,
          _root_.Complexity.TM.step, _root_.Complexity.Tape.write,
          _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
          _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
          _root_.Complexity.Γw.toΓ, writableOfRead, updateStart, updateInspect,
          updateEmitInner, updateCopy, updateNoneFirst, updateNoneSecond,
          updateHalt] using (finZeroTape_funext _ _)

@[simp]
theorem coinUpdateMachine_step_third (word : Word) :
    coinUpdateMachine.step (coinUpdateThird word) = some (coinUpdateFinal word) := by
  cases word with
  | nil =>
      simpa [coinUpdateMachine, coinUpdateFirst, coinUpdateSecond, coinUpdateThird,
        coinUpdateFinal, _root_.Complexity.TM.step, _root_.Complexity.Tape.write,
        _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
        _root_.Complexity.Tape.init, _root_.Complexity.Γw.toΓ, writableOfRead,
        updateStart, updateInspect, updateEmitInner, updateCopy, updateNoneFirst,
        updateNoneSecond, updateHalt] using (finZeroTape_funext _ _)
  | cons bit rest =>
      cases bit <;>
        simpa [coinUpdateMachine, coinUpdateFirst, coinUpdateSecond, coinUpdateThird,
          coinUpdateFinal, _root_.Complexity.TM.step, _root_.Complexity.Tape.write,
          _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
          _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
          _root_.Complexity.Γw.toΓ, writableOfRead, updateStart, updateInspect,
          updateEmitInner, updateCopy, updateNoneFirst, updateNoneSecond,
          updateHalt] using (finZeroTape_funext _ _)

/-- Total raw-word function computed by `coinUpdateMachine`. -/
def coinUpdateWordFunction : Word → Word
  | true :: _ :: answer :: _ => [true, true, answer]
  | true :: _ => [true, true]
  | _ => []

/-- Exact four-step run of the update transducer on every raw word. -/
def coinUpdateRun (word : Word) :
    ExactRun coinUpdateMachine word (coinUpdateWordFunction word) where
  final := coinUpdateFinal word
  steps := 4
  reaches := .step (coinUpdateMachine_step_init word) <|
    .step (coinUpdateMachine_step_first word) <|
      .step (coinUpdateMachine_step_second word) <|
        .step (coinUpdateMachine_step_third word) .zero
  halted := rfl
  output_correct := by
    cases word with
    | nil =>
        simp [coinUpdateFinal, coinUpdateThird, coinUpdateSecond, coinUpdateFirst,
          coinUpdateWordFunction, _root_.Complexity.Tape.HasOutput,
          _root_.Complexity.Tape.writeAndMove, _root_.Complexity.Tape.write,
          _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
          _root_.Complexity.Tape.init, _root_.Complexity.Γw.toΓ]
    | cons first rest =>
        cases first with
        | false =>
            simp [coinUpdateFinal, coinUpdateThird, coinUpdateSecond, coinUpdateFirst,
              coinUpdateWordFunction, _root_.Complexity.Tape.HasOutput,
              _root_.Complexity.Tape.writeAndMove, _root_.Complexity.Tape.write,
              _root_.Complexity.Tape.move, _root_.Complexity.Tape.read,
              _root_.Complexity.Tape.init, _root_.Complexity.Γ.ofBool,
              _root_.Complexity.Γw.toΓ]
        | true =>
            cases rest with
            | nil =>
                constructor
                · intro index hindex
                  simp only [coinUpdateWordFunction, List.length_cons,
                    List.length_nil] at hindex
                  have : index = 0 ∨ index = 1 := by omega
                  rcases this with rfl | rfl <;>
                    simp [coinUpdateFinal, coinUpdateThird, coinUpdateSecond,
                      coinUpdateFirst, coinUpdateWordFunction,
                      _root_.Complexity.Tape.writeAndMove,
                      _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
                      _root_.Complexity.Tape.read, _root_.Complexity.Tape.init,
                      _root_.Complexity.Γ.ofBool, _root_.Complexity.Γw.toΓ,
                      writableOfRead]
                · simp [coinUpdateFinal, coinUpdateThird, coinUpdateSecond,
                    coinUpdateFirst, coinUpdateWordFunction,
                    _root_.Complexity.Tape.writeAndMove,
                    _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
                    _root_.Complexity.Tape.read, _root_.Complexity.Tape.init,
                    _root_.Complexity.Γ.ofBool, _root_.Complexity.Γw.toΓ,
                    writableOfRead]
            | cons second rest =>
                cases rest with
                | nil =>
                    constructor
                    · intro index hindex
                      simp only [coinUpdateWordFunction, List.length_cons,
                        List.length_nil] at hindex
                      have : index = 0 ∨ index = 1 := by omega
                      rcases this with rfl | rfl <;>
                        simp [coinUpdateFinal, coinUpdateThird, coinUpdateSecond,
                          coinUpdateFirst, coinUpdateWordFunction,
                          _root_.Complexity.Tape.writeAndMove,
                          _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
                          _root_.Complexity.Tape.read, _root_.Complexity.Tape.init,
                          _root_.Complexity.Γ.ofBool, _root_.Complexity.Γw.toΓ,
                          writableOfRead]
                    · simp [coinUpdateFinal, coinUpdateThird, coinUpdateSecond,
                        coinUpdateFirst, coinUpdateWordFunction,
                        _root_.Complexity.Tape.writeAndMove,
                        _root_.Complexity.Tape.write, _root_.Complexity.Tape.move,
                        _root_.Complexity.Tape.read, _root_.Complexity.Tape.init,
                        _root_.Complexity.Γ.ofBool, _root_.Complexity.Γw.toΓ,
                        writableOfRead]
                | cons answer rest =>
                    cases answer
                    all_goals
                      constructor
                      · intro index hindex
                        simp only [coinUpdateWordFunction, List.length_cons,
                          List.length_nil] at hindex
                        have : index = 0 ∨ index = 1 ∨ index = 2 := by omega
                        rcases this with rfl | rfl | rfl <;>
                          simp [coinUpdateFinal, coinUpdateThird, coinUpdateSecond,
                            coinUpdateFirst, coinUpdateWordFunction,
                            _root_.Complexity.Tape.writeAndMove,
                            _root_.Complexity.Tape.write,
                            _root_.Complexity.Tape.move,
                            _root_.Complexity.Tape.read,
                            _root_.Complexity.Tape.init,
                            _root_.Complexity.Γ.ofBool,
                            _root_.Complexity.Γw.toΓ, writableOfRead]
                      · simp [coinUpdateFinal, coinUpdateThird, coinUpdateSecond,
                          coinUpdateFirst, coinUpdateWordFunction,
                          _root_.Complexity.Tape.writeAndMove,
                          _root_.Complexity.Tape.write,
                          _root_.Complexity.Tape.move,
                          _root_.Complexity.Tape.read,
                          _root_.Complexity.Tape.init,
                          _root_.Complexity.Γ.ofBool,
                          _root_.Complexity.Γw.toΓ, writableOfRead]

/-! ## Quantitative realization -/

/-- Representation of the flattened update input. -/
def coinStateIndexRepresentation : Representation
    (Option Bool × coinSpec.toPFunctor.Idx) :=
  .prod coinStateRepresentation coinIndexRepresentation

/-- Representation of the partial update output. -/
def coinStateOptionRepresentation : Representation (Option (Option Bool)) :=
  .option coinStateRepresentation

/-- Exact zero-step initialization code. -/
def coinInitCode : Code .unit coinStateRepresentation oneCoinMachine.init where
  workTapes := 0
  machine := Primitive.haltMachine
  wordFunction := fun _ ↦ []
  run := Primitive.haltRun
  encode_eq input := by cases input; rfl

/-- Exact fixed-three-step code for the state readout. -/
def coinHeadCode : Code coinStateRepresentation coinBoundary.head oneCoinMachine.head where
  workTapes := 0
  machine := coinHeadMachine
  wordFunction := coinHeadWordFunction
  run := coinHeadRun
  encode_eq state := by
    cases state with
    | none => rfl
    | some answer => cases answer <;> rfl

/-- Exact fixed-four-step code for the inhabited flattened update map. -/
def coinUpdateCode : Code coinStateIndexRepresentation coinStateOptionRepresentation
    oneCoinMachine.update? where
  workTapes := 0
  machine := coinUpdateMachine
  wordFunction := coinUpdateWordFunction
  run := coinUpdateRun
  encode_eq input := by
    rcases input with ⟨state, ⟨position, answer⟩⟩
    cases position
    cases state with
    | none => cases answer <;> rfl
    | some retained => cases retained <;> cases answer <;> rfl

@[simp]
theorem coinInitCode_cost (input : Unit) :
    quantitativeStepClass.cost coinInitCode input = 0 := by
  cases input
  rfl

@[simp]
theorem coinHeadCode_cost (state : Option Bool) :
    quantitativeStepClass.cost coinHeadCode state = 3 :=
  rfl

@[simp]
theorem coinUpdateCode_cost (input : Option Bool × coinSpec.toPFunctor.Idx) :
    quantitativeStepClass.cost coinUpdateCode input = 4 :=
  rfl

@[simp]
theorem coinStateSize_none :
    quantitativeStepClass.size coinStateRepresentation none = 0 :=
  rfl

@[simp]
theorem coinStateSize_some (answer : Bool) :
    quantitativeStepClass.size coinStateRepresentation (some answer) = 2 :=
  rfl

@[simp]
theorem coinPositionSize : quantitativeStepClass.size coinBoundary.pos () = 0 :=
  rfl

@[simp]
theorem coinIndexSize (answer : Bool) :
    quantitativeStepClass.size coinBoundary.idx ⟨(), answer⟩ = 2 :=
  rfl

@[simp]
theorem coinHeadSize_query :
    quantitativeStepClass.size coinBoundary.head (Sum.inr ()) = 1 :=
  rfl

@[simp]
theorem coinHeadSize_return (answer : Bool) :
    quantitativeStepClass.size coinBoundary.head (Sum.inl answer) = 2 :=
  rfl

/-- Polynomial initialization certificate. -/
def coinInitPolyRealizer : quantitativeStepClass.PolyRealizer
    .unit coinStateRepresentation oneCoinMachine.init where
  code := coinInitCode
  work := FirstOrderPolynomial.const 0
  outputSize := FirstOrderPolynomial.const 0
  work_le input := by cases input; rfl
  outputSize_le input := by cases input; rfl

/-- Polynomial readout certificate. -/
def coinHeadPolyRealizer : quantitativeStepClass.PolyRealizer
    coinStateRepresentation coinBoundary.head oneCoinMachine.head where
  code := coinHeadCode
  work := FirstOrderPolynomial.const 3
  outputSize := FirstOrderPolynomial.const 2
  work_le state := by cases state <;> rfl
  outputSize_le state := by
    cases state with
    | none => change 1 ≤ 2; decide
    | some answer =>
        cases answer <;> change 2 ≤ 2 <;> exact le_rfl

/-- Concrete exact-machine realization of the one-query program. -/
def oneCoinRealization : QuantitativeRealization quantitativeStepClass coinBoundary where
  machine := oneCoinMachine
  state := coinStateRepresentation
  initCode := coinInitPolyRealizer.code
  headCode := coinHeadPolyRealizer.code
  updateCode := coinUpdateCode

/-! ## Exact trace and resource proof -/

/-- The exact resource envelope of either one-query branch. -/
def oneCoinCost : ExecutionCost :=
  { work := 10
    queries := 1
    traffic := 2
    peakStateSize := 2
    peakHeadSize := 2 }

/-- The single transition trace selected by a Boolean reply. -/
def oneCoinTrace (answer : Bool) :
    oneCoinRealization.ExecutionTrace (oneCoinMachine.init ()) (some answer) :=
  QuantitativeRealization.ExecutionTrace.query (R := oneCoinRealization)
    oneCoinMachine_view_none answer
    (QuantitativeRealization.ExecutionTrace.nil (R := oneCoinRealization) (some answer))

/-- Both answer branches incur the complete exact resource envelope. -/
theorem oneCoinTrace_executionCost (answer : Bool) :
    oneCoinRealization.executionCost () (oneCoinTrace answer) = oneCoinCost := by
  apply ExecutionCost.ext <;>
    simp only [oneCoinRealization, oneCoinTrace, oneCoinCost,
      QuantitativeRealization.executionCost,
      QuantitativeRealization.ExecutionTrace.cost, coinInitPolyRealizer,
      coinHeadPolyRealizer, oneCoinMachine_init, oneCoinMachine_head_none,
      oneCoinMachine_head_some,
      ExecutionCost.work_add, ExecutionCost.queries_add, ExecutionCost.traffic_add,
      ExecutionCost.peakStateSize_add, ExecutionCost.peakHeadSize_add,
      ExecutionCost.work_zero, ExecutionCost.queries_zero, ExecutionCost.traffic_zero,
      ExecutionCost.peakStateSize_zero, ExecutionCost.peakHeadSize_zero,
      ExecutionCost.ofWork, ExecutionCost.observe, ExecutionCost.query,
      Nat.zero_add, Nat.add_zero, max_zero, zero_max]
  · change 0 + (3 + 4) + 3 = 10
    decide
  · change 0 + 2 = 2
    decide
  · change max 0 2 = 2
    decide
  · change max 1 2 = 2
    decide

/-- Every fair-coin-conforming prefix is bounded, both branches resolve in one query, and every
reachable query has an admitted response. -/
theorem oneCoinRealization_runsWithin :
    oneCoinRealization.RunsWithinUnder
      (fairCoinResourceModel quantitativeStepClass coinBoundary.interface).allows
      (fun _ ↦ oneCoinCost) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input finish trace htrace
    cases input
    cases trace with
    | nil =>
        rw [ExecutionCost.le_iff]
        change 0 + 3 ≤ 10 ∧ 0 ≤ 1 ∧ 0 ≤ 2 ∧ 0 ≤ 2 ∧ 1 ≤ 2
        decide
    | @query state position next finish view_eq answer tail =>
        cases position
        have exposed_eq : oneCoinMachine.view none = Sum.inr ⟨(), next⟩ := by
          simpa only [oneCoinRealization, oneCoinMachine_init] using view_eq
        rw [oneCoinMachine_view_none] at exposed_eq
        have query_eq := Sum.inr.inj exposed_eq
        have next_eq : (fun direction : Bool ↦ some direction) = next :=
          eq_of_heq (Sigma.ext_iff.mp query_eq).2
        subst next
        change oneCoinRealization.ExecutionTrace (some answer) finish at tail
        obtain ⟨finish_eq, tail_cost⟩ :=
          tail.finish_eq_and_cost_eq_zero_of_view_return
            (oneCoinMachine_view_some answer)
        subst finish
        have trace_cost_eq :
            (QuantitativeRealization.ExecutionTrace.query (R := oneCoinRealization)
              view_eq answer tail).cost = (oneCoinTrace answer).cost := by
          have remainder_eq := congrArg (fun remainder : ExecutionCost ↦
            ExecutionCost.ofWork
                (quantitativeStepClass.cost oneCoinRealization.headCode none) +
              ExecutionCost.ofWork
                (quantitativeStepClass.cost oneCoinRealization.updateCode
                  (none, ⟨(), answer⟩)) +
              ExecutionCost.observe
                (quantitativeStepClass.size oneCoinRealization.state none)
                (quantitativeStepClass.size coinBoundary.head
                  (oneCoinRealization.machine.head none)) +
              ExecutionCost.query (quantitativeStepClass.size coinBoundary.pos ())
                (quantitativeStepClass.size coinBoundary.idx ⟨(), answer⟩) + remainder)
            tail_cost
          simpa only [QuantitativeRealization.ExecutionTrace.cost, oneCoinTrace,
            oneCoinRealization, oneCoinMachine_init, add_zero] using remainder_eq
        have execution_eq :
            oneCoinRealization.executionCost ()
                (QuantitativeRealization.ExecutionTrace.query
                  (R := oneCoinRealization) view_eq answer tail) =
              oneCoinRealization.executionCost () (oneCoinTrace answer) := by
          unfold QuantitativeRealization.executionCost
          rw [trace_cost_eq]
          rfl
        rw [execution_eq, oneCoinTrace_executionCost]
  · intro input
    cases input
    simp [oneCoinRealization, oneCoinCost,
      PFunctor.DynSystem.DynComputation.ResolvesInUnder,
      oneCoinMachine_view_none, oneCoinMachine_view_some]
  · intro input state trace htrace position next view_eq
    exact ⟨false, trivial⟩

/-- Constant second-order resource polynomial used by the strict-PPT witness. -/
def oneCoinPolynomial : ResourcePolynomial (OracleModulus Unit) :=
  ResourcePolynomial.const oneCoinCost

/-- The concrete sum encoding exposes every returned Boolean with only a one-bit tag overhead. -/
def coinOutputRecovery : quantitativeStepClass.PolyOutputSizeRecovery coinBoundary where
  polynomial := FirstOrderPolynomial.input
  output_le answer := by
    change encodedSize .bool answer ≤
      encodedSize (.sum .bool .unit) (Sum.inl answer)
    simp

/-- Complete strict-PPT witness for the concrete one-query realization. -/
def oneCoinStrictPPTWitness : StrictPPTWitness quantitativeStepClass coinBoundary
    (fairCoinContract quantitativeStepClass coinBoundary.interface) oneCoinProgram where
  realization := oneCoinRealization
  implements := oneCoinMachine_implements
  outputRecovery := coinOutputRecovery
  runBound :=
    { polynomial := oneCoinPolynomial
      runsWithin model := by
        rw [show model.resourceModel =
          fairCoinResourceModel quantitativeStepClass coinBoundary.interface from model.2]
        simpa [oneCoinPolynomial] using oneCoinRealization_runsWithin }

/-- End-to-end strict, backend-relative PPT theorem for a genuine binary oracle query. -/
theorem oneCoin_isOraclePPTBy :
    IsOraclePPTBy quantitativeStepClass coinBoundary
      (fairCoinContract quantitativeStepClass coinBoundary.interface) oneCoinProgram :=
  ⟨oneCoinStrictPPTWitness⟩

/-- The concrete one-query witness exposed through the canonical fair-coin `IsPPTBy` facade. -/
theorem oneCoin_isPPTBy :
    OracleComp.Complexity.IsPPTBy quantitativeStepClass coinBoundary oneCoinOracleProgram := by
  change IsOraclePPTBy quantitativeStepClass coinBoundary
    (fairCoinContract quantitativeStepClass coinBoundary.interface) oneCoinProgram
  exact oneCoin_isOraclePPTBy

end VCVioComplexity.Backend.TuringMachine
