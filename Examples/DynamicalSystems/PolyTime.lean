/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTimeConstructions
import Examples.DynamicalSystems.Basic

/-!
# Polynomial-time machines — worked examples

Concrete demonstrations of `VCVio.OracleComp.Coinductive.Machine` and
`VCVio.OracleComp.Coinductive.PolyTime` over the coin oracle:

* `coinOnce` — a hand-rolled two-state machine that flips the coin once and reports the
  answer, proved to implement `coinSpec.query ()` through an explicit simulation
  relation (`CoinRel`), with a stable readout that is steady after one round.
* `adaptCoins` — an adaptive machine over the two-coin oracle `coinSpec + coinSpec`
  whose exposed query index depends on the first answer, proved to implement its
  program through a simulation relation whose constructors pin literal indices.
* the program/machine bridges — a query-bounded program *is* a machine
  (`OracleComp.toMachine`), steady within its query bound; and a machine unrolled for
  `k` rounds *is* a program with total query bound `k` and the same semantics
  (`OracleMachine.toComp`).
* canonical interface encodings — `coinSpec`'s pinned interface encoding is the
  registry constant `OracleSpec.InterfaceBitEnc.coin` (queries width `0`, answers
  width `1`).
-/

open OracleSpec OracleComp Computability

namespace DynSystemExamples

/-! ## A one-flip machine, by hand

The machine has states `Option Bool`: `none` before the flip, `some b` after seeing
`b`. Its readout is the state itself, so it is stable and steady after one round. -/

/-- Flip the coin once and report the answer. -/
def coinOnce : OracleMachine coinSpec Unit Bool where
  State := Option Bool
  expose _ := ()
  update s r := some (s.getD r)
  init _ := none
  output s := s

/-- The readout never changes once set. -/
theorem coinOnce_stableOutput : coinOnce.StableOutput := by
  intro s b hb r
  cases s with
  | none => simp [coinOnce] at hb
  | some b' => exact hb

/-- The machine is steady after one round, against every handler. -/
example (h : OracleHandler coinSpec) : coinOnce.SteadyBy h (coinOnce.init ()) 1 := rfl

/-- The simulation relation: the fresh state tracks the query, a resolved state tracks
the halted program. -/
inductive CoinRel : Option Bool → OracleComp coinSpec Bool → Prop
  | start : CoinRel none (coinSpec.query ())
  | done (b : Bool) : CoinRel (some b) (pure b)

theorem coinOnce_isSimulation : coinOnce.IsSimulation CoinRel where
  output_pure := by rintro s b h; cases h; rfl
  output_queryBind := by rintro s t k h; cases h; rfl
  expose_eq := by rintro s t k h; cases h; rfl
  update_rel := by rintro s t k h r; cases h; exact CoinRel.done r

/-- `coinOnce` implements the one-query program at fuel `1`. -/
theorem coinOnce_implements :
    coinOnce.Implements (fun _ : Unit => coinSpec.query ()) 1 :=
  OracleMachine.implements_of_isSimulation coinOnce_isSimulation
    (fun _ => CoinRel.start) (fun _ => ⟨Nat.one_pos, fun _ => trivial⟩)

/-! ## An adaptive two-oracle machine

Over the two-coin oracle `coinSpec + coinSpec`, a machine's exposed query can depend on
earlier answers. `adaptCoins` flips the left coin, then flips the left coin again on
heads but switches to the right coin on tails, reporting the second answer. Each
constructor of the simulation relation `AdaptRel` pins the exposed index to a literal
(`.inl ()` or `.inr ()`), which keeps the dependent answer-cast in `update_rel`
definitionally trivial. -/

/-- States of the adaptive machine: fresh, awaiting the second flip on the given side
(`true` = left, `false` = right), or halted with the reported answer. -/
inductive AdaptState where
  | start : AdaptState
  | second (side : Bool) : AdaptState
  | done (b : Bool) : AdaptState

/-- Flip the left coin; on heads flip left again, on tails flip right; report the
second answer. -/
def adaptProg : OracleComp (coinSpec + coinSpec) Bool :=
  OracleComp.queryBind (Sum.inl ()) fun b =>
    bif b then OracleComp.queryBind (Sum.inl ()) pure
    else OracleComp.queryBind (Sum.inr ()) pure

/-- The adaptive machine: the index of the second query depends on the first answer.
The `update` matches the two `second` sides separately so that the answer type
`(coinSpec + coinSpec).Range (adaptCoins.expose s)` reduces to `Bool` in each branch. -/
def adaptCoins : OracleMachine (coinSpec + coinSpec) Unit Bool where
  State := AdaptState
  expose s := match s with
    | .start => Sum.inl ()
    | .second true => Sum.inl ()
    | .second false => Sum.inr ()
    | .done _ => Sum.inl ()
  update s := match s with
    | .start => fun b => .second b
    | .second true => fun b => .done b
    | .second false => fun b => .done b
    | .done b => fun _ => .done b
  init _ := .start
  output s := match s with
    | .done b => some b
    | _ => none

/-- The readout never changes once set. -/
theorem adaptCoins_stableOutput : adaptCoins.StableOutput := by
  intro s b hb r
  cases s with
  | start => simp [adaptCoins] at hb
  | second side => cases side <;> simp [adaptCoins] at hb
  | done b' => exact hb

/-- The simulation relation: each constructor pins the machine state to a literal
residual program, including the literal index of its head query. -/
inductive AdaptRel : AdaptState → OracleComp (coinSpec + coinSpec) Bool → Prop
  | start : AdaptRel .start (OracleComp.queryBind (Sum.inl ()) fun b =>
      bif b then OracleComp.queryBind (Sum.inl ()) pure
      else OracleComp.queryBind (Sum.inr ()) pure)
  | secondLeft : AdaptRel (.second true) (OracleComp.queryBind (Sum.inl ()) pure)
  | secondRight : AdaptRel (.second false) (OracleComp.queryBind (Sum.inr ()) pure)
  | done (b : Bool) : AdaptRel (.done b) (pure b)

theorem adaptCoins_isSimulation : adaptCoins.IsSimulation AdaptRel where
  output_pure := by rintro s b h; cases h; rfl
  output_queryBind := by rintro s t k h; cases h <;> rfl
  expose_eq := by rintro s t k h; cases h <;> rfl
  update_rel := by
    rintro s t k h r
    cases h with
    | start => cases r with
      | false => exact AdaptRel.secondRight
      | true => exact AdaptRel.secondLeft
    | secondLeft => exact AdaptRel.done r
    | secondRight => exact AdaptRel.done r

/-- `adaptProg` makes at most two queries. -/
theorem isTotalQueryBound_adaptProg : IsTotalQueryBound adaptProg 2 :=
  ⟨by norm_num, fun b => by cases b <;> exact ⟨by norm_num, fun _ => trivial⟩⟩

/-- `adaptCoins` implements the adaptive program at fuel `2`. -/
theorem adaptCoins_implements : adaptCoins.Implements (fun _ : Unit => adaptProg) 2 :=
  OracleMachine.implements_of_isSimulation adaptCoins_isSimulation
    (fun _ => AdaptRel.start) (fun _ => isTotalQueryBound_adaptProg)

/-- After the first answer the machine resolves in one more round, whichever side it
turned to. -/
theorem adaptCoins_output_advanceOnce_second (h : OracleHandler (coinSpec + coinSpec))
    (side : Bool) :
    (adaptCoins.output
      (OracleStrategy.advanceOnce h adaptCoins.toDynSystem (.second side))).isSome := by
  cases side <;> rfl

/-- The machine is steady after two rounds, against every handler. -/
example (h : OracleHandler (coinSpec + coinSpec)) :
    adaptCoins.SteadyBy h (adaptCoins.init ()) 2 :=
  adaptCoins_output_advanceOnce_second h _

/-- A handler answering tails on the left coin and heads on the right coin. -/
def leftTailsRightHeads : OracleHandler (coinSpec + coinSpec) :=
  OracleHandler.ofFn fun t => match t with
    | Sum.inl _ => false
    | Sum.inr _ => true

/-- Left says tails, so the second flip is routed to the right coin: result `true`. -/
example : adaptCoins.runD leftTailsRightHeads 2 (adaptCoins.init ()) = some true := rfl

/-- A handler answering heads on the left coin and tails on the right coin. -/
def leftHeadsRightTails : OracleHandler (coinSpec + coinSpec) :=
  OracleHandler.ofFn fun t => match t with
    | Sum.inl _ => true
    | Sum.inr _ => false

/-- Left says heads, so the right coin is never consulted: result `true` even though the
right coin answers `false`. -/
example : adaptCoins.runD leftHeadsRightTails 2 (adaptCoins.init ()) = some true := rfl

/-! ## Program-to-machine: query bounds are steadiness -/

/-- `prog` (two coin flips) makes at most two queries. -/
theorem isTotalQueryBound_prog : IsTotalQueryBound prog 2 :=
  ⟨by norm_num, fun _ => ⟨by norm_num, fun _ => trivial⟩⟩

/-- The program-as-machine implements `prog` at its query bound... -/
example : (toMachine fun _ : Unit => prog).Implements (fun _ => prog) 2 :=
  toMachine_implements fun _ => isTotalQueryBound_prog

/-- ...and is steady within it, against every handler. -/
example (h : OracleHandler coinSpec) :
    (toMachine fun _ : Unit => prog).SteadyBy h ((toMachine fun _ => prog).init ()) 2 :=
  toMachine_steadyBy h () isTotalQueryBound_prog

/-! ## Machine-to-program: steadiness fuel is a query bound -/

/-- Unrolling `coinOnce` for one round gives a program making at most one query. -/
example : IsTotalQueryBound (coinOnce.toComp 1 none) 1 :=
  coinOnce.isTotalQueryBound_toComp 1 none

/-- The unrolled program's semantics is the machine's run: against the all-heads
oracle, one flip reports `true`. -/
example : evalWithAnswerFn (QueryImpl.ofFn allHeads) (coinOnce.toComp 1 none) =
    coinOnce.runD allHeads 1 none :=
  coinOnce.evalWithAnswerFn_toComp allHeads 1 none

example : coinOnce.runD allHeads 1 none = some true := rfl

/-! ## Canonical interface encodings

The coin oracle's canonical interface encoding is `OracleSpec.InterfaceBitEnc.coin`:
queries have width `0` (the index type is `Unit`) and answers width `1` (the coin
bit). No construction work is needed at call sites. -/

noncomputable example : OracleSpec.InterfaceBitEnc (fun _ => coinSpec) := .coin

/-! ## Query-free adversaries, hypothesis form

`OracleComp.isPolyTime_pure_of_witnesses` certifies any query-free adversary as
polynomial time once uniform machine families (a constant for query selection, a
projection for the update, and the output map itself) are supplied against the pinned
canonical boundaries. On polynomially small domains every witness is a concrete finite
table (`OracleComp.isPolyTime_pure_ofFintype`); the output family for a function on a
large domain is a genuine computability assumption, awaiting the base-machine library.
See `Examples.DynamicalSystems.XorFlips` for a fully concrete, hypothesis-free
`MachineAdversary` built from the coin-fold combinator. -/

/-- The constant query-selection family is concrete: a verified machine erases the
input and writes the (zero-width) encoded coin query. -/
noncomputable example :
    EncPolyTimeFam BitEncFam.bool.enc InterfaceBitEnc.coin.encQuery.enc
      (fun _ (_ : Bool) => (default : Unit)) :=
  .const _ _ InterfaceBitEnc.coin.encQuery.widBound
    (fun n => (InterfaceBitEnc.coin.encQuery.len_eq n _).le.trans
      (InterfaceBitEnc.coin.encQuery.wid_le n))

/-- Bit negation as a query-free polynomial-time family, in the honest hypothesis form:
the projection and output families are the awaited base machines. -/
example
    (updateF : EncPolyTimeFam
      (BitEncFam.bool.toStrEncFam.pairVar InterfaceBitEnc.coin.encAns).enc
      BitEncFam.bool.enc (fun _ => Prod.fst))
    (outputF : EncPolyTimeFam BitEncFam.bool.enc (BitEncFam.bool.option).enc
      (fun _ b => some (!b))) :
    OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.bool BitEncFam.bool)
      (fun (_ : ℕ) (b : Bool) => (pure (!b) : OracleComp coinSpec Bool)) :=
  OracleComp.isPolyTime_pure_of_witnesses _ (fun _ b => !b)
    (.const _ _ InterfaceBitEnc.coin.encQuery.widBound
      (fun n => (InterfaceBitEnc.coin.encQuery.len_eq n _).le.trans
        (InterfaceBitEnc.coin.encQuery.wid_le n)))
    updateF outputF

/-- On the constant-cardinality `Bool` domain, negation is polynomial time with **no**
hypotheses: the finite-table former discharges every witness. -/
example :
    OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.bool BitEncFam.bool)
      (fun (_ : ℕ) (b : Bool) => (pure (!b) : OracleComp coinSpec Bool)) :=
  OracleComp.isPolyTime_pure_ofFintype _ (fun _ b => !b)
    (.C 2) (fun n => by simp)
    (.C 2) (fun n => by simp [Nat.card_eq_fintype_card, Fintype.card_sigma])

end DynSystemExamples
