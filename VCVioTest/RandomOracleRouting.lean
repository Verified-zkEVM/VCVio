/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.ProgramLogic.RandomOracleRouting
public import Examples.ProgramLogic.RandomOracleWiring

/-! # Adaptive input routing and aliasing through ordinary imports -/

public section

open OracleComp OracleSpec
open OracleComp.RandomOracleRouting

namespace RandomOracleRoutingTest

/-- Two Boolean cells occupy distinct positions in a three-cell target oracle. -/
@[expose]
def encode (b : Bool) : Fin 3 := if b then 1 else 0

example : Function.Injective encode := by decide

-- The existing wired client makes adaptive and repeated queries.
example (input : Bool) :
    𝒟[(simulateQ randomOracle (route encode
      (Examples.RandomOracleWiring.network.oracleProgram
        Examples.RandomOracleWiring.implementation input))).run' ∅] =
    𝒟[(simulateQ randomOracle
      (Examples.RandomOracleWiring.network.oracleProgram
        Examples.RandomOracleWiring.implementation input)).run' ∅] :=
  evalDist_route_lazy encode (by decide) _

-- Disjoint encodings preserve arbitrary adaptive cross-domain clients.
example (program : OracleComp (Bool ⊕ Unit →ₒ Bool) Bool) :
    𝒟[(simulateQ randomOracle
      (route (Sum.elim encode (fun _ : Unit => (2 : Fin 3))) program)).run' ∅] =
    𝒟[(simulateQ randomOracle program).run' ∅] :=
  evalDist_route_sum encode (fun _ : Unit => (2 : Fin 3))
    (by decide) (by decide) (by decide) program

example :
    𝒟[(simulateQ randomOracle (route (fun _ : Bool => ())
      Examples.RandomOracleRouting.equalAnswers)).run' ∅] {true} -
    𝒟[(simulateQ randomOracle Examples.RandomOracleRouting.equalAnswers).run' ∅] {true} =
      (1 : ENNReal) / 2 := by
  rw [Examples.RandomOracleRouting.aliased_lazy_probability,
    Examples.RandomOracleRouting.separated_lazy_probability]
  norm_num

-- Structural routing is available outside Type 0, independently of table sampling.
example (table : ULift.{1} Bool → ULift.{1} Bool) :
    evalWithAnswerFn (QueryImpl.ofFn table)
      (route id (query (spec := ULift.{1} Bool →ₒ ULift.{1} Bool) ⟨true⟩ :
        OracleComp (ULift.{1} Bool →ₒ ULift.{1} Bool) (ULift.{1} Bool))) =
      table ⟨true⟩ := rfl

end RandomOracleRoutingTest
