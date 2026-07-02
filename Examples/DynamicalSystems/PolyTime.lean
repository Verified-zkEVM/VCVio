/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTime
import ToMathlib.Computability.PolyTimeTM
import Examples.DynamicalSystems.Basic

/-!
# Polynomial-time machines — worked examples

Concrete demonstrations of `VCVio.OracleComp.Coinductive.Machine` and
`VCVio.OracleComp.Coinductive.PolyTime` over the coin oracle:

* `coinOnce` — a hand-rolled two-state machine that flips the coin once and reports the
  answer, proved to implement `coinSpec.query ()` through an explicit simulation
  relation (`CoinRel`), with a stable readout that is steady after one round.
* the program/machine bridges — a query-bounded program *is* a machine
  (`OracleComp.toMachine`), steady within its query bound; and a machine unrolled for
  `k` rounds *is* a program with total query bound `k` and the same semantics
  (`OracleMachine.toComp`).
* free interface encodings — `coinSpec`'s query and answer types are `FinEnum`, so its
  `InterfaceEncoding` comes for free.
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

/-! ## Free interface encodings

`coinSpec`'s query type (`Unit`) and answer type (`Bool`) are `FinEnum`, so the
Turing-machine-facing interface encoding needs no construction work. -/

/-- The coin oracle's interface encoding, for free. -/
noncomputable example : coinSpec.InterfaceEncoding := .ofFinEnum coinSpec

/-! ## Query-free adversaries, hypothesis form

`OracleComp.isPolyTime_pure_of_witnesses` certifies any query-free adversary as
polynomial time once base machine witnesses (constants, projections, and the output
map) are supplied. The constant witness is already concrete
(`Computability.EncPolyTime.const`, built on a verified single-tape machine);
projections and the output map are the remaining Turing-machine-level work. -/

/-- The constant query-selection witness is concrete: a verified machine erases the
input and writes the encoded query. -/
noncomputable example (encIface : coinSpec.InterfaceEncoding) :
    EncPolyTime ((finEncodingOfFinEnum Bool).boolify) (encIface.encQuery.boolify)
      (fun _ => (default : Unit)) :=
  .const _ _ default

example (encIface : (n : ℕ) → (coinSpec).InterfaceEncoding)
    (sizeBound : Polynomial ℕ)
    (hsize : ∀ (n : ℕ) (b : Bool),
      ((finEncodingOfFinEnum Bool).boolify b).length ≤ sizeBound.eval n)
    (stepTime : Polynomial ℕ) (hone : ∀ m, 1 ≤ stepTime.eval m)
    (exposeTM : (n : ℕ) → EncPolyTime ((finEncodingOfFinEnum Bool).boolify)
      ((encIface n).encQuery.boolify) (fun _ => (default : Unit)))
    (hexpose : ∀ n k, ((exposeTM n).time).eval k ≤ stepTime.eval (n + k))
    (updateTM : (n : ℕ) → EncPolyTime
      ((finEncodingPair (finEncodingOfFinEnum Bool) (encIface n).encAns).boolify)
      ((finEncodingOfFinEnum Bool).boolify) Prod.fst)
    (hupdate : ∀ n k, ((updateTM n).time).eval k ≤ stepTime.eval (n + k))
    (outputTM : (n : ℕ) → EncPolyTime ((finEncodingOfFinEnum Bool).boolify)
      ((finEncodingOption (finEncodingOfFinEnum Bool)).boolify) (fun b => some (!b)))
    (houtput : ∀ n k, ((outputTM n).time).eval k ≤ stepTime.eval (n + k)) :
    OracleComp.IsPolyTime
      (fun (_ : ℕ) (b : Bool) => (pure (!b) : OracleComp coinSpec Bool)) :=
  OracleComp.isPolyTime_pure_of_witnesses (fun _ b => !b)
    (fun _ => finEncodingOfFinEnum Bool) (fun _ => finEncodingOfFinEnum Bool)
    encIface sizeBound hsize
    stepTime hone exposeTM hexpose updateTM hupdate outputTM houtput

end DynSystemExamples
