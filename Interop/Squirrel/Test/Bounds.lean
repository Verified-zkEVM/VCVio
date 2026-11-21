/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Machine

/-!
# Checks of the read and query bounds

The two bounds count different queries: a read bound counts tape reads, a query bound counts
input queries.

* `Machine.readZero`, the machine returning bit `0` of the attacker tape, reads below `1` and not
  below `0`, and makes no input query.
* The input projection `Machine.input` reads nothing of the tape, makes one input query, and does
  not meet the query bound `0`.
-/

public section

namespace SquirrelLogic

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B} {M : Model D} {τs : List (Ty B)}

/-- The machine that returns bit `0` of the attacker tape. -/
@[expose] def Machine.readZero : Machine M τs .bool := fun _ => Machine.read 0

/-- The machine reading bit `0` reads below `1`. -/
theorem Machine.readsBelow_readZero_one :
    (Machine.readZero : Machine M τs .bool).ReadsBelow fun _ => 1 :=
  fun _ => (OracleComp.allQueriesSatisfy_query_iff _ _).2 Nat.one_pos

/-- A read bound constrains a machine: the machine reading bit `0` does not read below `0`. -/
theorem Machine.not_readsBelow_readZero_zero :
    ¬ (Machine.readZero : Machine M τs .bool).ReadsBelow fun _ => 0 :=
  fun h => Nat.lt_irrefl 0
    ((OracleComp.allQueriesSatisfy_query_iff (spec := M.Iface 0 τs) (.inl 0) _).1 (h 0))

/-- Tape reads are not input queries: the machine reading bit `0` meets the query bound `0`. -/
theorem Machine.queryBound_readZero_zero :
    (Machine.readZero : Machine M τs .bool).QueryBound fun _ => 0 :=
  fun η => (OracleComp.isQueryBoundP_query_iff (spec := M.Iface η τs) _ (.inl 0) 0).2 fun h =>
    absurd h Bool.false_ne_true

/-- Input queries are not tape reads: the input projection reads below `0`. -/
theorem Machine.readsBelow_input_zero :
    (Machine.input .zero Ty.isGround_bool : Machine M [.bool] .bool).ReadsBelow fun _ => 0 :=
  Machine.readsBelow_input _ _

/-- The input projection makes one input query, so it meets the query bound `1`. -/
theorem Machine.queryBound_input_one :
    (Machine.input .zero Ty.isGround_bool : Machine M [.bool] .bool).QueryBound fun _ => 1 :=
  Machine.queryBound_input _ _

/-- A query bound constrains a machine: the input projection does not meet the query bound `0`. -/
theorem Machine.not_queryBound_input_zero :
    ¬ (Machine.input .zero Ty.isGround_bool : Machine M [.bool] .bool).QueryBound fun _ => 0 :=
  fun h => by
  have h0 := h 0
  rw [Machine.input, Machine.fetch, OracleComp.isQueryBoundP_map_iff, Machine.ask,
    OracleComp.isQueryBoundP_query_iff] at h0
  exact absurd (h0 rfl) (lt_irrefl 0)

end SquirrelLogic
