/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Model
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Machines: free programs over the tape and the inputs

LICS23's machines for `adv` and `∼` (§II-C.1, §II-C.2, Fig. 2) read the attacker tape `ρa` from a
randomness tape and query their higher-order inputs through a query tape. Here a machine is a
free program over a polynomial interface (VCVio's `OracleComp`), and running it is interpreting
that interface by fixed answers (VCVio's `evalWithAnswerFn`):

* the interface `Model.Iface M η τs` is the sum of the tape interface `tapeSpec`, whose query `i`
  reads bit `i` of `ρa` (`false` past its end), and the input interface `Model.inSpec`, whose
  query to an input of type `τ` carries arguments for all of `τ`'s arguments (`Ty.args τ`) and is
  answered by a value of `Ty.res τ`. A Boolean or base input is queried with no arguments. For
  inputs of order at most one, the arguments are Booleans or bitstrings: LICS23's query tape;
* `Machine M τs β` is a family over `η` of such programs returning a value of `β`;
* `Machine.run A η ρa e` answers the tape from `ρa` and the inputs from the values `e`
  (`Model.answer`);
* `Machine.test` and `AdvMachine.eval` are the denotations that the semantics of `∼` and `adv`
  use: a distinguisher (`Distinguisher`) and a curried attacker function (`AttackerFn`);
* `Machine.input y` returns the value of a Boolean or base input.

## Constructions

Every construction on machines is a handler for the input interface of one machine into the
interface of another, applied by `Machine.handle` (VCVio's `simulateQ`): relabelling the inputs
(`Machine.rename`), answering an input of type `b` by querying an input of type `a → b` at the
value of an input of type `a` (`Machine.app`), answering an input by an honest symbol
(`Machine.fn`), and answering the first input by running another machine on the query's arguments
and the remaining inputs (`Machine.subst`). Besides these, a machine may branch on a Boolean input
(`Machine.branch`), return a constant (`Machine.const`) or compare two Boolean or base inputs
(`Machine.eqTest`). For FreshL, a machine may also read the tape further along (`Machine.shift`, a
handler of the tape interface) and run the model's sampler for names of a type on bits of the tape
(`Machine.sampler`). Each has a `run` lemma that says what it does to the input values and the
tape; the reductions of the rules (`Machine.ite`, `Machine.guard`, `Machine.adv`,
`Machine.deduce`, `AdvMachine.comp`, `AdvMachine.freshL`) are built from them, and their `run`
lemmas follow.

A reduction of a cryptographic rule runs a machine as a program (`Machine.simulate`): it supplies
the attacker tape and answers the input queries in its own oracle computations
(`Model.answerIn`). When it answers them from values, the run collapses to the machine's run at
those values (`Machine.simulate_ofVals`).

## Bounds

Two resource bounds describe a machine without fixing a model of time:

* `Machine.ReadsBelow A b`: every tape read of `A`, on every path, is below `b η` (VCVio's
  `AllQueriesSatisfy`). Then `A`'s run depends on `ρa` only through those bits
  (`Machine.ReadsBelow.run_eq`).
* `Machine.QueryBound A q`: on every path, at every `η`, `A` makes at most `q η` queries to its
  inputs (VCVio's `IsQueryBoundP`; tape reads are not counted).

A machine running in time `t(η)` meets both with `t`: it reads its tape below `t(η)` and makes at
most `t(η)` queries. Each construction keeps a read bound, except that a shift adds its offset
(`Machine.ReadsBelow.shift`) and the sampler reads its bit block (`Machine.readsBelow_sampler`),
and multiplies a query bound by the number of queries its handler makes per query
(`Machine.QueryBound.handle`).

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-B.2, §II-C and Fig. 2.
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 3 and App. C.2.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature OracleComp

variable {B : Type} {D : Decl B} {M : Model D}

/-- A vector of values of the types `τs` at `η`. -/
abbrev Vals (M : Model D) (η : ℕ) (τs : List (Ty B)) : Type := Env (Ty.Value M.carrier η) τs

/-- A distinguisher of vectors of the types `τs`, as a function: a test at each `η` of a vector of
values, reading the attacker tape. It is the denotation of a machine (`Machine.test`). -/
abbrev Distinguisher (M : Model D) (τs : List (Ty B)) : Type :=
  (η : ℕ) → Vals M η τs → M.TapeA η → Bool

/-- An attacker function of type `τ`, as a function of the attacker tape at each `η`. It is the
denotation of a machine (`AdvMachine.eval`). -/
abbrev AttackerFn (M : Model D) (τ : Ty B) : Type := (η : ℕ) → M.TapeA η → τ.Value M.carrier η

/-! ## Interfaces and machines -/

/-- The tape interface: the query `i` reads bit `i` of the attacker tape. -/
@[expose] def tapeSpec : OracleSpec ℕ := fun _ => Bool

/-- A query to an input: its position, of type `τ`, and values for all of `τ`'s arguments. -/
abbrev Model.InQuery (M : Model D) (η : ℕ) (τs : List (Ty B)) : Type :=
  (τ : Ty B) × ScopedVar τs τ × Vals M η τ.args

/-- The input interface: a query to an input of type `τ` is answered by a value of `Ty.res τ`. -/
@[expose, reducible] def Model.inSpec (M : Model D) (η : ℕ) (τs : List (Ty B)) :
    OracleSpec (M.InQuery η τs) :=
  fun q => q.1.res.Value M.carrier η

/-- The interface of a machine for the inputs `τs` at `η`: the sum of the tape interface and the
input interface, as polynomial functors. -/
@[expose, reducible] def Model.Iface (M : Model D) (η : ℕ) (τs : List (Ty B)) :
    OracleSpec (ℕ ⊕ M.InQuery η τs) :=
  tapeSpec + M.inSpec η τs

/-- A machine for the inputs `τs` with results of type `β`: at each `η`, a free program over the
interface `M.Iface η τs`. -/
abbrev Machine (M : Model D) (τs : List (Ty B)) (β : Ty B) : Type :=
  (η : ℕ) → OracleComp (M.Iface η τs) (β.Value M.carrier η)

/-- A machine for `adv` at the type `τ₁ → … → τₙ → β`: its inputs are the tuple `τs` and the
arguments of `β`, and its result is that of `β`. -/
abbrev AdvMachine (M : Model D) (τs : List (Ty B)) (β : Ty B) : Type :=
  Machine M (τs ++ β.args) β.res

variable {η : ℕ} {τs τs' : List (Ty B)} {a b β γ : Ty B}

/-- Read bit `i` of the attacker tape. -/
@[expose] def Machine.read (i : ℕ) : OracleComp (M.Iface η τs) Bool :=
  liftM ((M.Iface η τs).query (.inl i))

/-- Query an input. -/
@[expose] def Machine.ask (q : M.InQuery η τs) :
    OracleComp (M.Iface η τs) (q.1.res.Value M.carrier η) :=
  liftM ((M.Iface η τs).query (.inr q))

/-- The answers of the attacker tape `ρa` and the input values `e`. -/
@[expose] def Model.answer (M : Model D) (ρa : M.TapeA η) (e : Vals M η τs) :
    QueryImpl (M.Iface η τs) Id
  | .inl i => M.readBit ρa i
  | .inr q => Ty.apply (e q.1 q.2.1) q.2.2

/-- The run of a machine at `η`, the attacker tape `ρa` and the input values `e`. -/
@[expose] def Machine.run (A : Machine M τs β) (η : ℕ) (ρa : M.TapeA η) (e : Vals M η τs) :
    β.Value M.carrier η :=
  evalWithAnswerFn (M.answer ρa e) (A η)

/-- A machine returning a Boolean, as a distinguisher. -/
@[expose] def Machine.test (A : Machine M τs .bool) : Distinguisher M τs :=
  fun η e ρa => A.run η ρa e

/-- An attacker machine, as the curried attacker function of type `τ₁ → … → τₙ → β` that it
computes. -/
@[expose] def AdvMachine.eval (A : AdvMachine M τs β) : AttackerFn M (Ty.arrows τs β) :=
  fun η ρa => Ty.curryVals fun e => Ty.curry fun q => A.run η ρa (Env.append e q)

section Run

variable {ρa : M.TapeA η} {e : Vals M η τs}

@[simp] theorem evalWithAnswerFn_read (i : ℕ) :
    evalWithAnswerFn (M.answer ρa e) (Machine.read i) = M.readBit ρa i := rfl

@[simp] theorem evalWithAnswerFn_ask (q : M.InQuery η τs) :
    evalWithAnswerFn (M.answer ρa e) (Machine.ask q) = Ty.apply (e q.1 q.2.1) q.2.2 := rfl

theorem AdvMachine.appVals_eval (A : AdvMachine M τs β) (e : Vals M η τs) :
    Ty.appVals (A.eval η ρa) e = Ty.curry fun q => A.run η ρa (Env.append e q) :=
  Ty.appVals_curryVals _ e

end Run

/-! ## Inputs -/

namespace Machine

/-- The value of a Boolean or base input, queried with no arguments. -/
@[expose] def fetch (y : ScopedVar τs a) (ha : a.IsGround) :
    OracleComp (M.Iface η τs) (a.Value M.carrier η) :=
  Ty.ofRes ha <$> Machine.ask ⟨a, y, Ty.groundArgs ha⟩

/-- Return the value of a Boolean or base input. -/
@[expose] def input (y : ScopedVar τs a) (ha : a.IsGround) : Machine M τs a := fun _ => fetch y ha

variable {ρa : M.TapeA η}

@[simp] theorem evalWithAnswerFn_fetch (e : Vals M η τs) (y : ScopedVar τs a) (ha : a.IsGround) :
    evalWithAnswerFn (M.answer ρa e) (fetch y ha) = e a y := by
  rw [fetch, evalWithAnswerFn_map]
  exact Ty.ofRes_apply_groundArgs ha _

theorem run_input (y : ScopedVar τs a) (ha : a.IsGround) (e : Vals M η τs) :
    (input y ha : Machine M τs a).run η ρa e = e a y :=
  evalWithAnswerFn_fetch e y ha

end Machine

/-! ## Handlers -/

/-- Answers to the inputs `τs` in a monad `m`: for each input of type `τ`, a computation answering
a query with arguments `q` by a value of `Ty.res τ`. -/
abbrev InputImpl (M : Model D) (η : ℕ) (τs : List (Ty B)) (m : Type → Type) : Type :=
  Env (fun τ => Vals M η τ.args → m (τ.res.Value M.carrier η)) τs

/-- Answer the inputs from values, in any monad. -/
@[expose] def InputImpl.ofVals {m : Type → Type} [Pure m] (v : Vals M η τs) :
    InputImpl M η τs m :=
  fun _ x q => pure (Ty.apply (v _ x) q)

/-- A handler for the inputs `τs` into programs over the interface of `τs'`: for each input of
type `τ`, a program answering a query with arguments `q` by a value of `Ty.res τ`. -/
abbrev Handler (M : Model D) (η : ℕ) (τs τs' : List (Ty B)) : Type :=
  InputImpl M η τs (OracleComp (M.Iface η τs'))

/-- The query implementation of a handler: tape reads pass through, and input queries go to the
handler. -/
@[expose] def Handler.impl (H : Handler M η τs τs') :
    QueryImpl (M.Iface η τs) (OracleComp (M.Iface η τs'))
  | .inl i => Machine.read i
  | .inr q => H q.1 q.2.1 q.2.2

/-- Run a machine with its input queries answered by a handler: VCVio's `simulateQ`. -/
@[expose] def Machine.handle (H : ∀ η, Handler M η τs τs') (A : Machine M τs β) :
    Machine M τs' β :=
  fun η => simulateQ (H η).impl (A η)

/-- A handler that, run at the tape `ρa` and the input values `e`, answers as the values `e'`. -/
@[expose] def Handler.EvalsTo (H : Handler M η τs τs') (ρa : M.TapeA η) (e : Vals M η τs')
    (e' : Vals M η τs) : Prop :=
  ∀ τ x q, evalWithAnswerFn (M.answer ρa e) (H τ x q) = Ty.apply (e' τ x) q

/-- Forward the inputs along a renaming. -/
@[expose] def Handler.fwd (r : Renaming τs τs') : Handler M η τs τs' :=
  fun τ x q => Machine.ask ⟨τ, r τ x, q⟩

namespace Handler

variable {ρa : M.TapeA η} {e : Vals M η τs'}

theorem evalsTo_ofVals (v : Vals M η τs) :
    Handler.EvalsTo (InputImpl.ofVals v : Handler M η τs τs') ρa e v :=
  fun _ _ _ => rfl

theorem evalsTo_fwd (r : Renaming τs τs') :
    (fwd r : Handler M η τs τs').EvalsTo ρa e (Env.rename r e) :=
  fun _ _ _ => rfl

theorem EvalsTo.cons {H : Vals M η a.args → OracleComp (M.Iface η τs') (a.res.Value M.carrier η)}
    {H' : Handler M η τs τs'} {v : a.Value M.carrier η} {e' : Vals M η τs}
    (h : ∀ q, evalWithAnswerFn (M.answer ρa e) (H q) = Ty.apply v q) (h' : H'.EvalsTo ρa e e') :
    Handler.EvalsTo (Env.cons H H' : Handler M η (a :: τs) τs') ρa e (Env.cons v e') := by
  intro _ x q
  cases x with
  | zero => exact h q
  | succ x => exact h' _ x q

theorem EvalsTo.append {H₂ : Handler M η τs τs'} {e₂ : Vals M η τs} :
    ∀ {Ξ : List (Ty B)} {H₁ : Handler M η Ξ τs'} {e₁ : Vals M η Ξ},
      H₁.EvalsTo ρa e e₁ → H₂.EvalsTo ρa e e₂ →
        Handler.EvalsTo (Env.append H₁ H₂ : Handler M η (Ξ ++ τs) τs') ρa e (Env.append e₁ e₂)
  | [], _, _, _, h₂ => h₂
  | _ :: _, _, _, h₁, h₂ => by
    intro _ x q
    cases x with
    | zero => exact h₁ _ .zero q
    | succ x => exact EvalsTo.append (fun _ y q => h₁ _ y.succ q) h₂ _ x q

/-- Interpreting a program through a handler, then answering at `ρa` and `e`, answers the program
at `ρa` and the values the handler evaluates to. -/
theorem EvalsTo.evalWithAnswerFn_simulateQ {α : Type} {H : Handler M η τs τs'} {e' : Vals M η τs}
    (h : H.EvalsTo ρa e e') (oa : OracleComp (M.Iface η τs) α) :
    evalWithAnswerFn (M.answer ρa e) (simulateQ H.impl oa) =
      evalWithAnswerFn (M.answer ρa e') oa := by
  rw [_root_.evalWithAnswerFn_simulateQ]
  congr 1
  funext t
  rcases t with i | ⟨τ, x, q⟩
  · rfl
  · exact h τ x q

end Handler

theorem Machine.run_handle_of_evalsTo (A : Machine M τs β) {H : ∀ η, Handler M η τs τs'}
    {ρa : M.TapeA η} {e : Vals M η τs'} {e' : Vals M η τs} (h : (H η).EvalsTo ρa e e') :
    (A.handle H).run η ρa e = A.run η ρa e' :=
  h.evalWithAnswerFn_simulateQ (A η)

/-! ## Running a machine inside a reduction

A reduction of a cryptographic rule runs the adversary's machine as a program: it supplies the
attacker tape and answers the machine's input queries in its own oracle computations.
`Machine.simulate` is that handler composition, VCVio's `simulateQ` of `Model.answerIn`. When the
answers are values, running the machine inside the reduction is returning its run at those values
(`Machine.simulate_ofVals`). -/

/-- The answers of a machine's interface inside a reduction over the oracles `spec`: tape reads
from the attacker tape `ρa` that the reduction drew, and input queries by `H`. -/
@[expose] def Model.answerIn {ι : Type} {spec : OracleSpec ι} (M : Model D) (ρa : M.TapeA η)
    (H : InputImpl M η τs (OracleComp spec)) : QueryImpl (M.Iface η τs) (OracleComp spec)
  | .inl i => pure (M.readBit ρa i)
  | .inr q => H q.1 q.2.1 q.2.2

/-- Run a machine inside a reduction over the oracles `spec`: the machine's program, with its
tape read from `ρa` and its inputs answered by `H` (VCVio's `simulateQ`). -/
@[expose] def Machine.simulate {ι : Type} {spec : OracleSpec ι} (A : Machine M τs β) (η : ℕ)
    (ρa : M.TapeA η) (H : InputImpl M η τs (OracleComp spec)) :
    OracleComp spec (β.Value M.carrier η) :=
  simulateQ (M.answerIn ρa H) (A η)

/-- **Fusion.** A machine run inside a reduction that answers its inputs from values returns its
run at those values. -/
theorem Machine.simulate_ofVals {ι : Type} {spec : OracleSpec ι} (A : Machine M τs β)
    (ρa : M.TapeA η) (e : Vals M η τs) :
    (A.simulate η ρa (InputImpl.ofVals e) : OracleComp spec _) = pure (A.run η ρa e) := by
  rw [simulate, run]
  refine Eq.trans (congrArg (simulateQ · (A η)) (funext fun t => ?_))
    (simulateQ_pure_eq_evalWithAnswerFn _ _)
  rcases t with i | q <;> rfl

section Answers

variable {ι : Type} {spec : OracleSpec ι} {ans : QueryImpl spec Id} {ρa : M.TapeA η}
  {H : InputImpl M η τs (OracleComp spec)} {e : Vals M η τs}

/-- Input answers that, run with the answers `ans`, answer as the values `e` make the reduction's
answers of the machine's interface, run with `ans`, the answers of the tape `ρa` and of `e`. -/
theorem Model.evalWithAnswerFn_answerIn
    (hH : ∀ τ x q, evalWithAnswerFn ans (H τ x q) = Ty.apply (e τ x) q) :
    (fun t => evalWithAnswerFn ans (M.answerIn ρa H t)) = M.answer ρa e := by
  funext t
  rcases t with i | ⟨τ, x, q⟩
  · rfl
  · exact hH τ x q

/-- **Fusion with fixed answers.** A machine run inside a reduction whose input answers, run with
the answers `ans`, answer as the values `e`, returns, run with `ans`, its run at `e`. -/
theorem Machine.evalWithAnswerFn_simulate (A : Machine M τs β)
    (hH : ∀ τ x q, evalWithAnswerFn ans (H τ x q) = Ty.apply (e τ x) q) :
    evalWithAnswerFn ans (A.simulate η ρa H) = A.run η ρa e := by
  rw [simulate, _root_.evalWithAnswerFn_simulateQ, M.evalWithAnswerFn_answerIn hH]
  rfl

end Answers

/-! ## The constructions -/

namespace Machine

/-- Relabel the inputs along a renaming: an input query of `A` is asked of the input it is
renamed to. -/
@[expose] def rename (r : Renaming τs τs') (A : Machine M τs β) : Machine M τs' β :=
  A.handle fun _ => Handler.fwd r

/-- Answer queries to an input of type `b` by querying the input of type `a → b` at the value of
the input of type `a`, a Boolean or base type, followed by the query's arguments. -/
@[expose] def app (ha : a.IsGround) (A : Machine M (b :: τs) β) :
    Machine M (.arrow a b :: a :: τs) β :=
  A.handle fun _ => Env.cons (fun q => do
      let x ← fetch (.succ .zero) ha
      ask ⟨.arrow a b, .zero, Env.cons x q⟩)
    (Handler.fwd fun _ y => y.succ.succ)

/-- Answer queries to the first input by applying an honest symbol to the query's arguments. -/
@[expose] def fn (f : D.Fn a) (A : Machine M (a :: τs) β) : Machine M τs β :=
  A.handle fun η => Env.cons (fun q => pure (Ty.apply (M.fn η f) q)) (Handler.fwd fun _ y => y)

/-- Answer queries to the first input, of type `as → ρ` (`Ty.arrows`), by running the machine
`K`: its first inputs are the query's arguments, split into those of `as` and those of `ρ`, and
its remaining inputs are those of the result. -/
@[expose] def subst {as : List (Ty B)} {ρ : Ty B} (A : Machine M (Ty.arrows as ρ :: τs) β)
    (K : Machine M (as ++ (ρ.args ++ τs)) ρ.res) : Machine M τs β :=
  A.handle fun η => Env.cons
    (fun q => Ty.resArrows as <$> simulateQ (Handler.impl
      (Env.append (InputImpl.ofVals (Ty.splitArgs as q).1)
        (Env.append (InputImpl.ofVals (Ty.splitArgs as q).2) (Handler.fwd fun _ y => y)))) (K η))
    (Handler.fwd fun _ y => y)

/-- Branch on a Boolean first input. -/
@[expose] def branch (x y : Machine M τs β) : Machine M (.bool :: τs) β := fun η => do
  let c ← ask (M := M) (η := η) (τs := .bool :: τs) ⟨.bool, .zero, Env.empty⟩
  cond c ((x.rename fun _ v => v.succ) η) ((y.rename fun _ v => v.succ) η)

/-- A constant Boolean. -/
@[expose] def const (c : Bool) : Machine M τs .bool := fun _ => pure c

/-- The test whether two inputs of a Boolean or base type are equal: equality of Booleans or of
bitstrings (`Ty.decEqValue`). -/
@[expose] def eqTest (hβ : β.IsGround) : Machine M [β, β] .bool := fun _ => do
  let x ← fetch .zero hβ
  let y ← fetch (.succ .zero) hβ
  pure (@decide (x = y) (Ty.decEqValue hβ x y))

variable {ρa : M.TapeA η}

theorem run_rename (r : Renaming τs τs') (A : Machine M τs β) (e : Vals M η τs') :
    (A.rename r).run η ρa e = A.run η ρa (Env.rename r e) :=
  A.run_handle_of_evalsTo (Handler.evalsTo_fwd r)

theorem run_app (ha : a.IsGround) (A : Machine M (b :: τs) β)
    (e : Vals M η (.arrow a b :: a :: τs)) :
    (A.app ha).run η ρa e =
      A.run η ρa (Env.cons (e _ .zero (e _ (.succ .zero))) fun _ y => e _ y.succ.succ) :=
  A.run_handle_of_evalsTo (Handler.EvalsTo.cons (fun q => (evalWithAnswerFn_bind _ _ _).trans
    (congrArg (fun x => Ty.apply (τ := .arrow a b) (e _ .zero) (Env.cons x q))
      (evalWithAnswerFn_fetch e _ ha))) (Handler.evalsTo_fwd _))

theorem run_fn (f : D.Fn a) (A : Machine M (a :: τs) β) (e : Vals M η τs) :
    (A.fn f).run η ρa e = A.run η ρa (Env.cons (M.fn η f) e) :=
  A.run_handle_of_evalsTo (Handler.EvalsTo.cons (fun _ => rfl) (Handler.evalsTo_fwd _))

theorem run_subst {as : List (Ty B)} {ρ : Ty B} (A : Machine M (Ty.arrows as ρ :: τs) β)
    (K : Machine M (as ++ (ρ.args ++ τs)) ρ.res) (e : Vals M η τs) :
    (A.subst K).run η ρa e = A.run η ρa (Env.cons (Ty.curryVals fun x => Ty.curry fun y =>
      K.run η ρa (Env.append x (Env.append y e))) e) := by
  refine A.run_handle_of_evalsTo (Handler.EvalsTo.cons (fun q => ?_) (Handler.evalsTo_fwd _))
  rw [evalWithAnswerFn_map, Handler.EvalsTo.evalWithAnswerFn_simulateQ
    ((Handler.evalsTo_ofVals _).append ((Handler.evalsTo_ofVals _).append
      (Handler.evalsTo_fwd _))), Ty.apply_curryVals_curry]
  rfl

theorem run_branch (x y : Machine M τs β) (e : Vals M η (.bool :: τs)) :
    (branch x y).run η ρa e =
      cond (e _ .zero) (x.run η ρa fun _ v => e _ v.succ) (y.run η ρa fun _ v => e _ v.succ) := by
  simp only [run, branch, evalWithAnswerFn_bind]
  change evalWithAnswerFn _ (cond (e _ .zero) _ _) = _
  cases e _ .zero
  · exact run_rename _ y e
  · exact run_rename _ x e

theorem run_const (c : Bool) (e : Vals M η τs) : (const c : Machine M τs .bool).run η ρa e = c :=
  rfl

theorem run_eqTest (hβ : β.IsGround) (e : Vals M η [β, β]) :
    (eqTest hβ : Machine M [β, β] .bool).run η ρa e =
      @decide (e _ .zero = e _ (.succ .zero)) (Ty.decEqValue hβ _ _) := by
  simp only [run, eqTest, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact decide_eq_decide.2 (by rw [evalWithAnswerFn_fetch, evalWithAnswerFn_fetch])

end Machine

/-! ## Tape offsets and the name sampler

FreshL's reduction (CCS26 App. C.2, p. 17) samples a fresh name "from the adversarial
randomness", from bits of the attacker tape that nothing else reads. Two constructions give it:
`Machine.shift off A` runs `A` with every tape read moved `off η` bits along, a handler of the tape
interface; and `Machine.sampler b` reads the first `coinLen η b` bits of the tape and runs the
model's sampler for names of type `b` on them, as a name does on its bit block of the honest tape
(LICS23 §II-B.2, p. 6).

The proofs of FreshL and of the guessing bound exchange such a block of the attacker tape with
other bits: `Model.bitsAt ρa n k` reads the `k` bits from bit `n` on, and `Model.setBlock o ρa c`
overwrites the bits from bit `o` on with `c`. Reading back what was written gives it
(`Model.bitsAt_setBlock`), and writing back what was read gives the tape (`Model.setBlock_bitsAt`),
so the exchange is an involution. -/

/-- The attacker tape read from bit `n` on: bit `i` of `M.shiftTape n ρa` is bit `n + i` of
`ρa`. -/
@[expose] def Model.shiftTape (M : Model D) {η : ℕ} (n : ℕ) (ρa : M.TapeA η) : M.TapeA η :=
  fun i => M.readBit ρa (n + i)

theorem Model.readBit_shiftTape (n : ℕ) (ρa : M.TapeA η) (i : ℕ) :
    M.readBit (M.shiftTape n ρa) i = M.readBit ρa (n + i) := by
  unfold Model.shiftTape Model.readBit
  dsimp only
  split_ifs <;> first | rfl | omega

/-- The bit block of a name of type `τ`, read from the attacker tape from bit `n` on. -/
@[expose] def Model.coinAt (M : Model D) {η : ℕ} (τ : Ty B) (ρa : M.TapeA η) (n : ℕ) :
    M.Coin η τ :=
  fun j => M.readBit ρa (n + j)

theorem Model.coinAt_shiftTape (τ : Ty B) (n m : ℕ) (ρa : M.TapeA η) :
    M.coinAt τ (M.shiftTape n ρa) m = M.coinAt τ ρa (n + m) :=
  funext fun j => (M.readBit_shiftTape n ρa (m + j)).trans (congrArg _ (Nat.add_assoc _ _ _).symm)

/-- The `k` bits of the attacker tape from bit `n` on. The bit block of a name is the case
`k = coinLen η τ` (`Model.coinAt`). -/
@[expose] def Model.bitsAt (M : Model D) {η : ℕ} (ρa : M.TapeA η) (n k : ℕ) : Fin k → Bool :=
  fun j => M.readBit ρa (n + j)

/-- The attacker tape with the bits `[o, o + L)` replaced by `c`. -/
@[expose] def Model.setBlock (M : Model D) {η : ℕ} (o : ℕ) (ρa : M.TapeA η) {L : ℕ}
    (c : Fin L → Bool) : M.TapeA η :=
  fun j => if h : o ≤ j.1 ∧ j.1 - o < L then c ⟨j.1 - o, h.2⟩ else ρa j

/-- Overwriting a block leaves the bits below it. -/
theorem Model.readBit_setBlock_of_lt {o : ℕ} (ρa : M.TapeA η) {L : ℕ} (c : Fin L → Bool)
    {i : ℕ} (hi : i < o) : M.readBit (M.setBlock o ρa c) i = M.readBit ρa i := by
  unfold Model.readBit Model.setBlock
  dsimp only
  split_ifs <;> first | rfl | omega

/-- A block that fits on the tape reads back as what was written. -/
theorem Model.bitsAt_setBlock (o : ℕ) (ρa : M.TapeA η) {L : ℕ} (c : Fin L → Bool)
    (h : o + L ≤ M.lenA η) : M.bitsAt (M.setBlock o ρa c) o L = c := by
  funext j
  unfold Model.bitsAt Model.readBit Model.setBlock
  dsimp only
  split_ifs with h₁ h₂
  · exact congrArg c (Fin.ext (Nat.add_sub_cancel_left ..))
  · exact absurd ⟨Nat.le_add_right _ _, by simp⟩ h₂
  · omega

theorem Model.setBlock_setBlock {o L : ℕ} (ρa : M.TapeA η) (c c' : Fin L → Bool) :
    M.setBlock o (M.setBlock o ρa c) c' = M.setBlock o ρa c' := by
  funext j
  unfold Model.setBlock
  split_ifs <;> rfl

/-- Writing back the block that was read gives the tape. -/
theorem Model.setBlock_bitsAt (o : ℕ) (ρa : M.TapeA η) (L : ℕ) :
    M.setBlock o ρa (M.bitsAt ρa o L) = ρa := by
  funext j
  unfold Model.setBlock Model.bitsAt
  split_ifs with h
  · rw [Nat.add_sub_cancel' h.1]
    simp [Model.readBit]
  · rfl

namespace Machine

/-- Tape reads go `n` bits further along; input queries pass through. -/
@[expose] def shiftImpl (n : ℕ) : QueryImpl (M.Iface η τs) (OracleComp (M.Iface η τs))
  | .inl i => read (n + i)
  | .inr q => ask q

/-- Run `A` with every tape read moved `off η` bits along: the handler `shiftImpl` of the tape
interface, applied by `simulateQ`. -/
@[expose] def shift (off : ℕ → ℕ) (A : Machine M τs β) : Machine M τs β :=
  fun η => simulateQ (shiftImpl (off η)) (A η)

/-- Read `k` bits of the attacker tape from bit `n` on. -/
@[expose] def readBits (n : ℕ) : (k : ℕ) → OracleComp (M.Iface η τs) (Fin k → Bool)
  | 0 => pure Fin.elim0
  | k + 1 => do
    let x ← read n
    let xs ← readBits (n + 1) k
    pure (Fin.cons x xs)

/-- The values of Boolean or base inputs at the positions `r`. -/
@[expose] def fetchVals : {Ξ : List (Ty B)} → Renaming Ξ τs → (∀ τ ∈ Ξ, τ.IsGround) →
    OracleComp (M.Iface η τs) (Vals M η Ξ)
  | [], _, _ => pure Env.empty
  | _ :: _, r, h => do
    let x ← fetch (r _ .zero) (h _ List.mem_cons_self)
    let xs ← fetchVals (fun _ y => r _ y.succ) fun σ hσ => h σ (List.mem_cons_of_mem _ hσ)
    pure (Env.cons x xs)

/-- The sampler of names of type `b`: read the first `coinLen η b` bits of the attacker tape, run
the model's sampler on them, and apply the value to `b`'s arguments, which are Boolean or base
inputs since `b` has order at most one. -/
@[expose] def sampler (b : Ty B) (hb : b.order ≤ 1) : Machine M b.args b.res := fun η => do
  let c ← readBits 0 (M.coinLen η b)
  let q ← fetchVals (fun _ x => x) (Ty.isGround_of_mem_args hb)
  pure (Ty.apply (M.sample η b c) q)

variable {ρa : M.TapeA η}

theorem run_shift (off : ℕ → ℕ) (A : Machine M τs β) (e : Vals M η τs) :
    (A.shift off).run η ρa e = A.run η (M.shiftTape (off η) ρa) e := by
  rw [run, run, shift, _root_.evalWithAnswerFn_simulateQ]
  congr 1
  funext t
  rcases t with i | q
  · exact (M.readBit_shiftTape _ _ _).symm
  · rfl

/-- Reading `k` bits from bit `n` on returns those bits of the tape. -/
theorem evalWithAnswerFn_readBits (e : Vals M η τs) :
    ∀ n k : ℕ, evalWithAnswerFn (M.answer ρa e) (readBits n k) = M.bitsAt ρa n k
  | _, 0 => funext fun j => j.elim0
  | n, k + 1 => by
    simp only [readBits, evalWithAnswerFn_bind, evalWithAnswerFn_read,
      evalWithAnswerFn_readBits e (n + 1) k, evalWithAnswerFn_pure]
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp only [Fin.cons_succ, Fin.val_succ, Model.bitsAt]
      congr 1
      omega

private theorem evalWithAnswerFn_fetchVals (e : Vals M η τs) :
    ∀ {Ξ : List (Ty B)} (r : Renaming Ξ τs) (h : ∀ τ ∈ Ξ, τ.IsGround),
      evalWithAnswerFn (M.answer ρa e) (fetchVals r h) = Env.rename r e
  | [], _, _ => (Env.eq_empty _).symm
  | _ :: _, r, h => by
    simp only [fetchVals, evalWithAnswerFn_bind, evalWithAnswerFn_fetch,
      evalWithAnswerFn_fetchVals e _ _, evalWithAnswerFn_pure]
    funext σ x
    cases x <;> rfl

theorem run_sampler (b : Ty B) (hb : b.order ≤ 1) (e : Vals M η b.args) :
    (sampler b hb).run η ρa e = Ty.apply (M.sample η b (M.coinAt b ρa 0)) e := by
  simp only [run, sampler, evalWithAnswerFn_bind, evalWithAnswerFn_readBits,
    evalWithAnswerFn_fetchVals, evalWithAnswerFn_pure]
  rfl

/-- The sampler moved `off η` bits along reads the bit block from bit `off η` on. -/
theorem run_shift_sampler (off : ℕ → ℕ) (b : Ty B) (hb : b.order ≤ 1) (e : Vals M η b.args) :
    ((sampler b hb).shift off).run η ρa e = Ty.apply (M.sample η b (M.coinAt b ρa (off η))) e := by
  rw [run_shift, run_sampler, Model.coinAt_shiftTape, Nat.add_zero]

end Machine

/-! ## The reductions of the rules -/

namespace Machine

/-- The reduction of If: test `A` on the conditional of the first three inputs, by branching on
the first and relabelling. -/
@[expose] def ite (A : Machine M (a :: τs) β) : Machine M (.bool :: a :: a :: τs) β :=
  branch (A.rename (Env.cons .zero fun _ v => v.succ.succ))
    (A.rename (Env.cons (.succ .zero) fun _ v => v.succ.succ))

/-- The reduction of the case split: when the Boolean first input is `c`, run `A` on the rest;
otherwise return `false`. -/
@[expose] def guard (c : Bool) (A : Machine M τs .bool) : Machine M (.bool :: τs) .bool :=
  cond c (branch A (const false)) (branch (const false) A)

/-- The reduction of FA-Adv: answer the first input, of type `τ₁ → … → τₙ → β`, by running the
attacker machine `g` on the query's arguments. -/
@[expose] def adv {τs₀ : List (Ty B)} (A : Machine M (Ty.arrows τs₀ β :: τs) γ)
    (g : AdvMachine M τs₀ β) : Machine M τs γ :=
  A.subst (g.rename (Renaming.liftMany (fun _ x => x.appendLeft τs) τs₀))

/-- The renaming that moves the arguments of `ρ` before the tuple `τs` and the inputs `Γ`. -/
@[expose] def argsFirst (τs : List (Ty B)) (ρ : Ty B) (Γ : List (Ty B)) :
    Renaming (τs ++ ρ.args) (ρ.args ++ (τs ++ Γ)) :=
  Env.append (fun _ x => (x.appendLeft Γ).weakenMany ρ.args) fun _ y => y.appendLeft (τs ++ Γ)

/-- The reduction of Rw-Equiv (CCS26 Fig. 3): run the attacker machine `g` on the first inputs and
test its result, of a Boolean or base type, against the last input. -/
@[expose] def deduce (hβ : β.IsGround) (g : AdvMachine M τs β) : Machine M (τs ++ [β]) .bool :=
  subst (as := []) (ρ := β)
    ((eqTest hβ).rename (Env.cons .zero (Env.cons (.succ ((ScopedVar.zero).weakenMany τs))
      Env.empty)))
    (g.rename (argsFirst τs β [β]))

/-- The renaming that moves the last entry `b` of the tuple `τs ++ [b]` before the rest. -/
@[expose] def lastFirst (τs : List (Ty B)) (b : Ty B) (Γ : List (Ty B)) :
    Renaming ((τs ++ [b]) ++ Γ) (b :: (τs ++ Γ)) :=
  Env.append (Env.append (fun _ x => .succ (x.appendLeft Γ)) (Env.cons .zero Env.empty))
    fun _ y => .succ (y.weakenMany τs)

variable {ρa : M.TapeA η}

theorem run_ite (A : Machine M (a :: τs) β) (e : Vals M η (.bool :: a :: a :: τs)) :
    A.ite.run η ρa e = A.run η ρa (Env.cons (cond (e _ .zero) (e _ (.succ .zero))
      (e _ (.succ (.succ .zero)))) fun _ v => e _ v.succ.succ.succ) := by
  rw [ite, run_branch]
  cases e _ .zero <;> simp only [Bool.cond_true, Bool.cond_false, run_rename] <;> congr 1 <;>
    funext _ v <;> cases v <;> rfl

theorem run_guard (c : Bool) (A : Machine M τs .bool) (e : Vals M η (.bool :: τs)) :
    (A.guard c).run η ρa e = ((e _ .zero == c) && A.run η ρa fun _ v => e _ v.succ) := by
  cases c <;> simp only [guard, Bool.cond_true, Bool.cond_false, run_branch, run_const] <;>
    cases e _ .zero <;> rfl

theorem run_adv {τs₀ : List (Ty B)} (A : Machine M (Ty.arrows τs₀ β :: τs) γ)
    (g : AdvMachine M τs₀ β) (e : Vals M η τs) :
    (A.adv g).run η ρa e = A.run η ρa (Env.cons (g.eval η ρa) e) := by
  rw [adv, run_subst]
  simp only [run_rename, Env.rename_append, Env.rename_appendLeft_append]
  rfl

private theorem rename_argsFirst {τs₀ Γ : List (Ty B)} {ρ : Ty B} (q : Vals M η ρ.args)
    (e : Vals M η τs₀) (e' : Vals M η Γ) :
    Env.rename (argsFirst τs₀ ρ Γ) (Env.append q (Env.append e e')) = Env.append e q := by
  rw [argsFirst, Env.rename_append_renaming]
  congr 1
  · funext _ x
    exact (Env.append_weakenMany _ _ _).trans (Env.append_appendLeft e e' x)
  · exact Env.rename_appendLeft_append q _

private theorem rename_lastFirst {τs₀ Γ : List (Ty B)} (y : b.Value M.carrier η)
    (e : Vals M η τs₀) (e' : Vals M η Γ) :
    Env.rename (lastFirst τs₀ b Γ) (Env.cons y (Env.append e e')) =
      Env.append (Env.append e (Env.cons y Env.empty)) e' := by
  rw [lastFirst, Env.rename_append_renaming, Env.rename_append_renaming]
  refine congrArg₂ Env.append (congrArg₂ Env.append (Env.rename_appendLeft_append e e') ?_)
    (Env.rename_weakenMany_append e e')
  funext _ x
  cases x with
  | zero => rfl
  | succ x => exact nomatch x

theorem run_deduce (hβ : β.IsGround) (g : AdvMachine M τs β) (e : Vals M η τs)
    (y : β.Value M.carrier η) :
    (deduce hβ g).run η ρa (Env.append e (Env.cons y Env.empty)) =
      @decide (Ty.appVals (g.eval η ρa) e = y) (Ty.decEqValue hβ _ _) := by
  refine (run_subst _ _ _).trans ((run_rename _ _ _).trans ((run_eqTest hβ _).trans ?_))
  rw [AdvMachine.appVals_eval]
  congr 2
  · refine congrArg Ty.curry (funext fun q => ?_)
    exact (run_rename _ _ _).trans (congrArg _ (rename_argsFirst _ _ _))
  · exact Env.append_weakenMany e _ .zero

end Machine

/-- Post-composition of an attacker function of the tuple `τs` with an attacker function `k`,
both reading the same attacker tape: the denotation of `AdvMachine.comp`, the reduction of Trans,
WeakL and WeakR (CCS26 Fig. 3). -/
@[expose] def AttackerFn.comp (k : AttackerFn M (.arrow β γ)) (f : AttackerFn M (Ty.arrows τs β)) :
    AttackerFn M (Ty.arrows τs γ) :=
  fun η ρa => Ty.postcomp (k η ρa) (f η ρa)

namespace AdvMachine

/-- The reduction of Trans, WeakL and WeakR (CCS26 Fig. 3): answer the input of `k` by running
`f` on the tuple, both on the same attacker tape. -/
@[expose] def comp (k : AdvMachine M [β] γ) (f : AdvMachine M τs β) : AdvMachine M τs γ :=
  Machine.subst (as := []) (ρ := β) (k.rename (Renaming.lift (fun _ x => x.weakenMany τs) β))
    (f.rename (Machine.argsFirst τs β γ.args))

theorem eval_comp (k : AdvMachine M [β] γ) (f : AdvMachine M τs β) :
    (k.comp f).eval = k.eval.comp f.eval := funext fun η => funext fun ρa => by
  refine Eq.trans ?_ (Ty.postcomp_curryVals _ _).symm
  refine congrArg Ty.curryVals (funext fun e => congrArg Ty.curry (funext fun q => ?_))
  refine (Machine.run_subst _ _ _).trans ((Machine.run_rename _ _ _).trans ?_)
  refine congrArg (Machine.run k η ρa) ((Env.rename_cons _ _ _).trans ?_)
  refine (congrArg (Env.cons _) (Env.rename_weakenMany_append e q)).trans ?_
  refine congrArg (fun x => Env.cons x q) (congrArg Ty.curry (funext fun y => ?_))
  exact (Machine.run_rename _ _ _).trans (congrArg _ (Machine.rename_argsFirst _ _ _))

/-- The reduction of FreshL (CCS26 App. C.2, p. 17): answer the input of `g` for the fresh name,
the last entry of its tuple, by the sampler of the name's type moved `off η` bits along
(`Machine.subst`), so that the name is drawn from the bits `[off η, off η + coinLen η b)` of the
attacker tape. CCS26's `f′` "simulates the sampling of `n_fresh` from the adversarial randomness
and then runs `f`". FreshL's proof takes `off` to be a polynomial above the read bounds of `g` and
of the terms. -/
@[expose] def freshL (off : ℕ → ℕ) (hb : b.order ≤ 1) (g : AdvMachine M (τs ++ [b]) β) :
    AdvMachine M τs β :=
  Machine.subst (as := []) (ρ := b) (g.rename (Machine.lastFirst τs b β.args))
    (((Machine.sampler b hb).shift off).rename fun _ x => x.appendLeft (τs ++ β.args))

/-- The reduction of FreshL runs `g` with the fresh name's value sampled from the bit block of the
attacker tape at `off η`. -/
theorem appVals_eval_freshL (off : ℕ → ℕ) (hb : b.order ≤ 1) (g : AdvMachine M (τs ++ [b]) β)
    (ρa : M.TapeA η) (e : Vals M η τs) :
    Ty.appVals ((g.freshL off hb).eval η ρa) e = Ty.appVals (g.eval η ρa)
      (Env.append e (Env.cons (M.sample η b (M.coinAt b ρa (off η))) Env.empty)) := by
  rw [appVals_eval, appVals_eval, freshL]
  refine congrArg Ty.curry (funext fun q => ?_)
  refine (Machine.run_subst _ _ _).trans ((Machine.run_rename _ _ _).trans ?_)
  refine congrArg (Machine.run g η ρa) (Eq.trans ?_ (Machine.rename_lastFirst _ e q))
  refine congrArg
    (fun x => Env.rename (Machine.lastFirst τs b β.args) (Env.cons x (Env.append e q)))
    (Eq.trans ?_ (Ty.curry_apply (M.sample η b (M.coinAt b ρa (off η)))))
  refine congrArg Ty.curry (funext fun y => ?_)
  exact (Machine.run_rename _ _ _).trans ((congrArg _ (Env.rename_appendLeft_append _ _)).trans
    (Machine.run_shift_sampler _ _ _ _))

end AdvMachine

/-! ## Read bounds -/

section ReadBounds

/-- The queries that read the tape below `n`; input queries are unrestricted. -/
@[expose] def Model.tapeBelow (M : Model D) {η : ℕ} {τs : List (Ty B)} (n : ℕ) :
    ℕ ⊕ M.InQuery η τs → Prop
  | .inl i => i < n
  | .inr _ => True

theorem Model.tapeBelow_mono {n n' : ℕ} (h : n ≤ n') (t : ℕ ⊕ M.InQuery η τs) :
    M.tapeBelow n t → M.tapeBelow n' t := by
  rcases t with i | _
  · exact fun hi => lt_of_lt_of_le hi h
  · exact id

/-- Every tape read of `A`, on every path and at every `η`, is below `b η`. LICS23's machines read
`ρa` from a tape (§II-C.1), so one that runs in time `t` reads below `t`. -/
@[expose] def Machine.ReadsBelow (A : Machine M τs β) (b : ℕ → ℕ) : Prop :=
  ∀ η, (A η).AllQueriesSatisfy (M.tapeBelow (b η))

/-- Every tape read of a handler's answers is below `n`. -/
@[expose] def Handler.ReadsBelow (H : Handler M η τs τs') (n : ℕ) : Prop :=
  ∀ τ x q, (H τ x q).AllQueriesSatisfy (M.tapeBelow n)

theorem Machine.allQueriesSatisfy_ask (q : M.InQuery η τs) (n : ℕ) :
    (Machine.ask q).AllQueriesSatisfy (M.tapeBelow n) :=
  (allQueriesSatisfy_query_iff _ _).2 trivial

theorem Machine.allQueriesSatisfy_fetch (y : ScopedVar τs a) (ha : a.IsGround) (n : ℕ) :
    (Machine.fetch (η := η) y ha).AllQueriesSatisfy (M.tapeBelow n) :=
  (allQueriesSatisfy_map_iff _ _ _).2 (Machine.allQueriesSatisfy_ask _ n)

namespace Handler

theorem readsBelow_ofVals (v : Vals M η τs) (n : ℕ) :
    Handler.ReadsBelow (InputImpl.ofVals v : Handler M η τs τs') n :=
  fun _ _ _ => allQueriesSatisfy_pure _ _

theorem readsBelow_fwd (r : Renaming τs τs') (n : ℕ) :
    (fwd r : Handler M η τs τs').ReadsBelow n :=
  fun _ _ _ => Machine.allQueriesSatisfy_ask _ n

theorem ReadsBelow.cons {n : ℕ}
    {H : Vals M η a.args → OracleComp (M.Iface η τs') (a.res.Value M.carrier η)}
    {H' : Handler M η τs τs'} (h : ∀ q, (H q).AllQueriesSatisfy (M.tapeBelow n))
    (h' : H'.ReadsBelow n) :
    Handler.ReadsBelow (Env.cons H H' : Handler M η (a :: τs) τs') n := by
  intro _ x q
  cases x with
  | zero => exact h q
  | succ x => exact h' _ x q

theorem ReadsBelow.append {n : ℕ} {H₂ : Handler M η τs τs'} :
    ∀ {Ξ : List (Ty B)} {H₁ : Handler M η Ξ τs'}, H₁.ReadsBelow n → H₂.ReadsBelow n →
      Handler.ReadsBelow (Env.append H₁ H₂ : Handler M η (Ξ ++ τs) τs') n
  | [], _, _, h₂ => h₂
  | _ :: _, _, h₁, h₂ => by
    intro _ x q
    cases x with
    | zero => exact h₁ _ .zero q
    | succ x => exact ReadsBelow.append (fun _ y q => h₁ _ y.succ q) h₂ _ x q

/-- Interpreting a program that reads below `n` through a handler whose answers read below `n`
gives a program that reads below `n`. -/
theorem ReadsBelow.allQueriesSatisfy_simulateQ {n : ℕ} {α : Type} {H : Handler M η τs τs'}
    (hH : H.ReadsBelow n) {oa : OracleComp (M.Iface η τs) α}
    (h : oa.AllQueriesSatisfy (M.tapeBelow n)) :
    (simulateQ H.impl oa).AllQueriesSatisfy (M.tapeBelow n) := by
  refine h.simulateQ fun t ht => ?_
  rcases t with i | ⟨τ, x, q⟩
  · exact (allQueriesSatisfy_query_iff _ _).2 ht
  · exact hH τ x q

end Handler

namespace Machine

variable {bd : ℕ → ℕ}

theorem ReadsBelow.mono {A : Machine M τs β} {b' : ℕ → ℕ} (h : A.ReadsBelow bd)
    (hb : ∀ η, bd η ≤ b' η) : A.ReadsBelow b' := fun η =>
  (h η).mono (Model.tapeBelow_mono (hb η))

theorem ReadsBelow.handle {A : Machine M τs β} {H : ∀ η, Handler M η τs τs'}
    (hA : A.ReadsBelow bd) (hH : ∀ η, (H η).ReadsBelow (bd η)) : (A.handle H).ReadsBelow bd :=
  fun η => (hH η).allQueriesSatisfy_simulateQ (hA η)

theorem ReadsBelow.rename {A : Machine M τs β} (hA : A.ReadsBelow bd) (r : Renaming τs τs') :
    (A.rename r).ReadsBelow bd :=
  hA.handle fun _ => Handler.readsBelow_fwd r _

theorem ReadsBelow.app {A : Machine M (b :: τs) β} (hA : A.ReadsBelow bd) (ha : a.IsGround) :
    (A.app ha).ReadsBelow bd :=
  hA.handle fun _ => Handler.ReadsBelow.cons
    (fun _ => allQueriesSatisfy_bind (allQueriesSatisfy_fetch _ ha _)
      fun _ => allQueriesSatisfy_ask _ _) (Handler.readsBelow_fwd _ _)

theorem ReadsBelow.fn {A : Machine M (a :: τs) β} (hA : A.ReadsBelow bd) (f : D.Fn a) :
    (A.fn f).ReadsBelow bd :=
  hA.handle fun _ => Handler.ReadsBelow.cons (fun _ => allQueriesSatisfy_pure _ _)
    (Handler.readsBelow_fwd _ _)

theorem ReadsBelow.subst {as : List (Ty B)} {ρ : Ty B} {A : Machine M (Ty.arrows as ρ :: τs) β}
    {K : Machine M (as ++ (ρ.args ++ τs)) ρ.res} (hA : A.ReadsBelow bd) (hK : K.ReadsBelow bd) :
    (A.subst K).ReadsBelow bd :=
  hA.handle fun η => Handler.ReadsBelow.cons (fun _ => (allQueriesSatisfy_map_iff _ _ _).2
    (Handler.ReadsBelow.allQueriesSatisfy_simulateQ ((Handler.readsBelow_ofVals _ _).append
      ((Handler.readsBelow_ofVals _ _).append (Handler.readsBelow_fwd _ _))) (hK η)))
    (Handler.readsBelow_fwd _ _)

theorem ReadsBelow.branch {x y : Machine M τs β} (hx : x.ReadsBelow bd) (hy : y.ReadsBelow bd) :
    (branch x y).ReadsBelow bd := fun η =>
  allQueriesSatisfy_bind (allQueriesSatisfy_ask _ _) fun c => by
    cases c
    · exact (hy.rename _) η
    · exact (hx.rename _) η

theorem readsBelow_const (c : Bool) : (const c : Machine M τs .bool).ReadsBelow bd :=
  fun _ => allQueriesSatisfy_pure _ _

/-- An input projection reads nothing of the tape. -/
theorem readsBelow_input (y : ScopedVar τs a) (ha : a.IsGround) :
    (input y ha : Machine M τs a).ReadsBelow bd :=
  fun _ => allQueriesSatisfy_fetch _ ha _

/-- The equality test reads nothing of the tape. -/
theorem readsBelow_eqTest (hβ : β.IsGround) : (eqTest hβ : Machine M [β, β] .bool).ReadsBelow bd :=
  fun _ => allQueriesSatisfy_bind (allQueriesSatisfy_fetch _ hβ _) fun _ =>
    allQueriesSatisfy_bind (allQueriesSatisfy_fetch _ hβ _) fun _ => allQueriesSatisfy_pure _ _

/-- A machine moved `off η` bits along reads below `off η` plus its own bound. -/
theorem ReadsBelow.shift {A : Machine M τs β} (hA : A.ReadsBelow bd) (off : ℕ → ℕ) :
    (A.shift off).ReadsBelow fun η => off η + bd η := fun η =>
  (hA η).simulateQ fun t ht => by
    rcases t with i | q
    · exact (allQueriesSatisfy_query_iff _ _).2 (Nat.add_lt_add_left ht (off η))
    · exact allQueriesSatisfy_ask _ _

/-- Reading `k` bits from bit `n` on reads below `n + k`. -/
theorem allQueriesSatisfy_readBits :
    ∀ n k : ℕ, (readBits (M := M) (η := η) (τs := τs) n k).AllQueriesSatisfy (M.tapeBelow (n + k))
  | _, 0 => allQueriesSatisfy_pure _ _
  | n, k + 1 => allQueriesSatisfy_bind
      ((allQueriesSatisfy_query_iff _ _).2 (show n < n + (k + 1) by omega)) fun _ =>
    allQueriesSatisfy_bind ((allQueriesSatisfy_readBits (n + 1) k).mono
      (Model.tapeBelow_mono (by omega))) fun _ => allQueriesSatisfy_pure _ _

private theorem allQueriesSatisfy_fetchVals (n : ℕ) :
    ∀ {Ξ : List (Ty B)} (r : Renaming Ξ τs) (h : ∀ τ ∈ Ξ, τ.IsGround),
      (fetchVals (M := M) (η := η) r h).AllQueriesSatisfy (M.tapeBelow n)
  | [], _, _ => allQueriesSatisfy_pure _ _
  | _ :: _, _, _ => allQueriesSatisfy_bind (allQueriesSatisfy_fetch _ _ _) fun _ =>
    allQueriesSatisfy_bind (allQueriesSatisfy_fetchVals n _ _) fun _ => allQueriesSatisfy_pure _ _

/-- The sampler of names of type `b` reads below `coinLen η b`. -/
theorem readsBelow_sampler (b : Ty B) (hb : b.order ≤ 1) :
    (sampler b hb : Machine M b.args b.res).ReadsBelow fun η => M.coinLen η b := fun _ =>
  allQueriesSatisfy_bind ((allQueriesSatisfy_readBits 0 _).mono
    (Model.tapeBelow_mono (Nat.zero_add _).le))
    fun _ => allQueriesSatisfy_bind (allQueriesSatisfy_fetchVals _ _ _) fun _ =>
      allQueriesSatisfy_pure _ _

/-- A machine reading below `bd` depends on the attacker tape only through its bits below
`bd η`. -/
theorem ReadsBelow.run_eq {A : Machine M τs β} (hA : A.ReadsBelow bd) {ρa ρa' : M.TapeA η}
    (hρ : ∀ i < bd η, M.readBit ρa i = M.readBit ρa' i) (e : Vals M η τs) :
    A.run η ρa e = A.run η ρa' e :=
  evalWithAnswerFn_eq_of_allQueriesSatisfy (fun t ht => by
    rcases t with i | q
    · exact hρ i ht
    · rfl) (hA η)

end Machine

/-- An attacker machine reading below `b` computes, at two tapes that agree below `b η`, the same
attacker function. -/
theorem AdvMachine.eval_eq_of_readsBelow {A : AdvMachine M τs β} {b : ℕ → ℕ}
    (hA : Machine.ReadsBelow A b) {ρa ρa' : M.TapeA η}
    (hρ : ∀ i < b η, M.readBit ρa i = M.readBit ρa' i) : A.eval η ρa = A.eval η ρa' := by
  simp only [AdvMachine.eval]
  congr 1
  funext e
  congr 1
  funext q
  exact hA.run_eq hρ _

end ReadBounds

/-! ## Query bounds -/

section QueryBounds

/-- At most `q η` queries to the inputs, on every path of the program, at every `η` (VCVio's
`IsQueryBoundP` at the input queries; tape reads are not counted). -/
@[expose] def Machine.QueryBound (A : Machine M τs β) (q : ℕ → ℕ) : Prop :=
  ∀ η, (A η).IsQueryBoundP (fun t => t.isRight = true) (q η)

/-- Every answer of the handler makes at most `k` queries to the inputs. -/
@[expose] def Handler.QueryBound (H : Handler M η τs τs') (k : ℕ) : Prop :=
  ∀ τ x q, (H τ x q).IsQueryBoundP (fun t => t.isRight = true) k

namespace Machine

theorem isQueryBoundP_read (i n : ℕ) :
    (read (M := M) (η := η) (τs := τs) i).IsQueryBoundP (fun t => t.isRight = true) n :=
  (isQueryBoundP_query_iff (spec := M.Iface η τs) _ (.inl i) n).2 (by simp)

theorem isQueryBoundP_ask (q : M.InQuery η τs) :
    (ask q).IsQueryBoundP (fun t => t.isRight = true) 1 :=
  (isQueryBoundP_query_iff (spec := M.Iface η τs) _ (.inr q) 1).2 fun _ => Nat.one_pos

theorem isQueryBoundP_fetch (y : ScopedVar τs a) (ha : a.IsGround) :
    (fetch (M := M) (η := η) y ha).IsQueryBoundP (fun t => t.isRight = true) 1 := by
  rw [fetch, isQueryBoundP_map_iff]
  exact isQueryBoundP_ask _

/-- Reading bits of the tape makes no input query. -/
theorem isQueryBoundP_readBits :
    ∀ n k : ℕ, (readBits (M := M) (η := η) (τs := τs) n k).IsQueryBoundP
      (fun t => t.isRight = true) 0
  | _, 0 => by rw [readBits]; simp
  | n, k + 1 => by
    rw [readBits]
    exact isQueryBoundP_bind_le (m := 0) (isQueryBoundP_read n 0) (fun _ _ =>
      isQueryBoundP_bind_le (m := 0) (isQueryBoundP_readBits (n + 1) k) (fun _ _ => by simp)
        (by omega)) (by omega)

private theorem isQueryBoundP_fetchVals : ∀ {Ξ : List (Ty B)} (r : Renaming Ξ τs)
    (h : ∀ τ ∈ Ξ, τ.IsGround),
    (fetchVals (M := M) (η := η) r h).IsQueryBoundP (fun t => t.isRight = true) Ξ.length
  | [], _, _ => by rw [fetchVals]; simp
  | _ :: _, _, _ => by
    rw [fetchVals]
    exact isQueryBoundP_bind_le (isQueryBoundP_fetch _ _) (fun _ _ =>
      isQueryBoundP_bind_le (m := 0) (isQueryBoundP_fetchVals _ _) (fun _ _ => by simp) le_rfl)
        (by simp [Nat.add_comm])

end Machine

namespace Handler

theorem queryBound_fwd (r : Renaming τs τs') : (fwd r : Handler M η τs τs').QueryBound 1 :=
  fun _ _ _ => Machine.isQueryBoundP_ask _

theorem queryBound_ofVals (v : Vals M η τs) (k : ℕ) :
    Handler.QueryBound (InputImpl.ofVals v : Handler M η τs τs') k :=
  fun _ _ _ => isQueryBoundP_pure _ _ _

theorem QueryBound.mono {H : Handler M η τs τs'} {k k' : ℕ} (h : H.QueryBound k) (hk : k ≤ k') :
    H.QueryBound k' :=
  fun τ x q => (h τ x q).mono hk

theorem QueryBound.cons {k : ℕ}
    {H : Vals M η a.args → OracleComp (M.Iface η τs') (a.res.Value M.carrier η)}
    {H' : Handler M η τs τs'} (h : ∀ q, (H q).IsQueryBoundP (fun t => t.isRight = true) k)
    (h' : H'.QueryBound k) : Handler.QueryBound (Env.cons H H' : Handler M η (a :: τs) τs') k := by
  intro _ x q
  cases x with
  | zero => exact h q
  | succ x => exact h' _ x q

theorem QueryBound.append {k : ℕ} {H₂ : Handler M η τs τs'} :
    ∀ {Ξ : List (Ty B)} {H₁ : Handler M η Ξ τs'}, H₁.QueryBound k → H₂.QueryBound k →
      Handler.QueryBound (Env.append H₁ H₂ : Handler M η (Ξ ++ τs) τs') k
  | [], _, _, h₂ => h₂
  | _ :: _, _, h₁, h₂ => by
    intro _ x q
    cases x with
    | zero => exact h₁ _ .zero q
    | succ x => exact QueryBound.append (fun _ y q => h₁ _ y.succ q) h₂ _ x q

/-- Interpreting a program through a handler multiplies its bound on input queries by the bound
on its answers. -/
theorem QueryBound.isQueryBoundP_simulateQ {k n : ℕ} {α : Type} {H : Handler M η τs τs'}
    (hH : H.QueryBound k) {oa : OracleComp (M.Iface η τs) α}
    (h : oa.IsQueryBoundP (fun t => t.isRight = true) n) :
    (simulateQ H.impl oa).IsQueryBoundP (fun t => t.isRight = true) (n * k) := by
  refine h.simulateQ_of_step_le (fun t ht => ?_) fun t ht => ?_
  · rcases t with i | ⟨τ, x, q⟩
    · exact absurd ht (by simp)
    · exact hH τ x q
  · rcases t with i | q
    · exact Machine.isQueryBoundP_read (M := M) (η := η) (τs := τs') i _
    · exact absurd rfl ht

end Handler

namespace Machine

variable {q q' : ℕ → ℕ}

theorem QueryBound.mono {A : Machine M τs β} (h : A.QueryBound q) (hq : ∀ η, q η ≤ q' η) :
    A.QueryBound q' :=
  fun η => (h η).mono (hq η)

theorem QueryBound.handle {A : Machine M τs β} {H : ∀ η, Handler M η τs τs'} {k : ℕ → ℕ}
    (hA : A.QueryBound q) (hH : ∀ η, (H η).QueryBound (k η)) :
    (A.handle H).QueryBound fun η => q η * k η :=
  fun η => (hH η).isQueryBoundP_simulateQ (hA η)

theorem QueryBound.rename {A : Machine M τs β} (hA : A.QueryBound q) (r : Renaming τs τs') :
    (A.rename r).QueryBound q :=
  (hA.handle fun _ => Handler.queryBound_fwd r).mono fun _ => (Nat.mul_one _).le

theorem QueryBound.app {A : Machine M (b :: τs) β} (hA : A.QueryBound q) (ha : a.IsGround) :
    (A.app ha).QueryBound fun η => q η * 2 :=
  hA.handle fun _ => Handler.QueryBound.cons
    (fun _ => isQueryBoundP_bind_le (isQueryBoundP_fetch _ ha) (fun _ _ => isQueryBoundP_ask _)
      le_rfl)
    ((Handler.queryBound_fwd _).mono (by norm_num))

theorem QueryBound.fn {A : Machine M (a :: τs) β} (hA : A.QueryBound q) (f : D.Fn a) :
    (A.fn f).QueryBound q :=
  (hA.handle fun _ => Handler.QueryBound.cons (fun _ => isQueryBoundP_pure _ _ _)
    (Handler.queryBound_fwd _)).mono fun _ => (Nat.mul_one _).le

theorem QueryBound.subst {as : List (Ty B)} {ρ : Ty B} {A : Machine M (Ty.arrows as ρ :: τs) β}
    {K : Machine M (as ++ (ρ.args ++ τs)) ρ.res} (hA : A.QueryBound q) (hK : K.QueryBound q') :
    (A.subst K).QueryBound fun η => q η * (q' η + 1) :=
  hA.handle fun η => Handler.QueryBound.cons
    (fun _ => (isQueryBoundP_map_iff _ _ _).2 ((Handler.QueryBound.isQueryBoundP_simulateQ (k := 1)
      ((Handler.queryBound_ofVals _ 1).append ((Handler.queryBound_ofVals _ 1).append
        (Handler.queryBound_fwd _))) (hK η)).mono (by omega)))
    ((Handler.queryBound_fwd _).mono (by omega))

theorem QueryBound.branch {x y : Machine M τs β} (hx : x.QueryBound q) (hy : y.QueryBound q') :
    (branch x y).QueryBound fun η => 1 + (q η + q' η) := fun η => by
  unfold Machine.branch
  refine isQueryBoundP_bind_le (isQueryBoundP_ask _) (fun c _ => ?_) le_rfl
  cases c
  · exact ((hy.rename _) η).mono (Nat.le_add_left _ _)
  · exact ((hx.rename _) η).mono (Nat.le_add_right _ _)

theorem queryBound_const (c : Bool) : (const c : Machine M τs .bool).QueryBound q :=
  fun _ => isQueryBoundP_pure _ _ _

/-- An input projection makes one input query. -/
theorem queryBound_input (y : ScopedVar τs a) (ha : a.IsGround) :
    (input y ha : Machine M τs a).QueryBound fun _ => 1 :=
  fun _ => isQueryBoundP_fetch y ha

/-- The equality test makes two input queries. -/
theorem queryBound_eqTest (hβ : β.IsGround) :
    (eqTest hβ : Machine M [β, β] .bool).QueryBound fun _ => 2 := fun _ => by
  unfold eqTest
  exact isQueryBoundP_bind_le (isQueryBoundP_fetch _ hβ) (fun _ _ =>
    isQueryBoundP_bind_le (m := 0) (isQueryBoundP_fetch _ hβ) (fun _ _ => by simp) le_rfl)
      (show 1 + (1 + 0) ≤ 2 by omega)

/-- Moving the tape reads makes no input query: a shifted machine keeps its query bound. -/
theorem QueryBound.shift {A : Machine M τs β} (hA : A.QueryBound q) (off : ℕ → ℕ) :
    (A.shift off).QueryBound q := fun η =>
  ((hA η).simulateQ_of_step_le (cost := 1) (fun t ht => by
    rcases t with i | q
    · exact absurd ht (by simp)
    · exact isQueryBoundP_ask q) fun t ht => by
    rcases t with i | q
    · exact isQueryBoundP_read (M := M) (η := η) (τs := τs) (off η + i) _
    · exact absurd rfl ht).mono (Nat.mul_one _).le

/-- The sampler of names of type `b` queries each of its inputs, the arguments of `b`, once. -/
theorem queryBound_sampler (b : Ty B) (hb : b.order ≤ 1) :
    (sampler b hb : Machine M b.args b.res).QueryBound fun _ => b.args.length := fun _ => by
  unfold sampler
  exact isQueryBoundP_bind_le (isQueryBoundP_readBits _ _) (fun _ _ =>
    isQueryBoundP_bind_le (m := 0) (isQueryBoundP_fetchVals _ _) (fun _ _ => by simp) le_rfl)
      (by simp)

end Machine

end QueryBounds

end Interop.Squirrel
