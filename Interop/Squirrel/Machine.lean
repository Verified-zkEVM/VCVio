/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Model
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

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

Two resource bounds describe a machine without fixing a model of time:

* `Machine.ReadsBelow A b`: every tape read of `A`, on every path, is below `b η` (VCVio's
  `AllQueriesSatisfy`). Then `A`'s run depends on `ρa` only through those bits
  (`Machine.ReadsBelow.run_eq`).
* `Machine.QueryBound A q`: on every path, at every `η`, `A` makes at most `q η` queries to its
  inputs (VCVio's `IsQueryBoundP`; tape reads are not counted).

A machine running in time `t(η)` meets both with `t`: it reads its tape below `t(η)` and makes at
most `t(η)` queries.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-C and Fig. 2.
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

variable {η : ℕ} {τs : List (Ty B)} {a β : Ty B}

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

/-! ## Read bounds -/

section ReadBounds

/-- The queries that read the tape below `n`; input queries are unrestricted. -/
@[expose] def Model.tapeBelow (M : Model D) {η : ℕ} {τs : List (Ty B)} (n : ℕ) :
    ℕ ⊕ M.InQuery η τs → Prop
  | .inl i => i < n
  | .inr _ => True

/-- Every tape read of `A`, on every path and at every `η`, is below `b η`. LICS23's machines read
`ρa` from a tape (§II-C.1), so one that runs in time `t` reads below `t`. -/
@[expose] def Machine.ReadsBelow (A : Machine M τs β) (b : ℕ → ℕ) : Prop :=
  ∀ η, (A η).AllQueriesSatisfy (M.tapeBelow (b η))

namespace Machine

variable {bd : ℕ → ℕ}

theorem ReadsBelow.mono {A : Machine M τs β} {b' : ℕ → ℕ} (h : A.ReadsBelow bd)
    (hb : ∀ η, bd η ≤ b' η) : A.ReadsBelow b' := fun η =>
  (h η).mono fun t ht => by
    rcases t with i | _
    · exact lt_of_lt_of_le ht (hb η)
    · trivial

/-- An input projection reads nothing of the tape. -/
theorem readsBelow_input (y : ScopedVar τs a) (ha : a.IsGround) :
    (input y ha : Machine M τs a).ReadsBelow bd := fun _ =>
  (allQueriesSatisfy_map_iff _ _ _).2 ((allQueriesSatisfy_query_iff _ _).2 trivial)

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

/-- At most `q η` queries to the inputs, on every path of the program, at every `η` (VCVio's
`IsQueryBoundP` at the input queries; tape reads are not counted). -/
@[expose] def Machine.QueryBound (A : Machine M τs β) (q : ℕ → ℕ) : Prop :=
  ∀ η, (A η).IsQueryBoundP (fun t => t.isRight = true) (q η)

namespace Machine

theorem QueryBound.mono {A : Machine M τs β} {q q' : ℕ → ℕ} (h : A.QueryBound q)
    (hq : ∀ η, q η ≤ q' η) : A.QueryBound q' :=
  fun η => (h η).mono (hq η)

/-- An input projection makes one input query. -/
theorem queryBound_input (y : ScopedVar τs a) (ha : a.IsGround) :
    (input y ha : Machine M τs a).QueryBound fun _ => 1 := fun _ => by
  rw [input, fetch, isQueryBoundP_map_iff]
  exact (isQueryBoundP_query_iff (spec := M.Iface _ τs) _ (.inr _) 1).2 fun _ => Nat.one_pos

end Machine

end Interop.Squirrel
