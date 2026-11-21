/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Mixed

/-!
# Physical charges of mixed graph calls
-/

public section
open OracleSpec OracleComp CanonicalGraph.PairedQueries
open scoped OracleSpec.PrimitiveQuery

namespace VCVioTest.RandomOracleMixedQueries

/-- The test caller has two boolean rows for each natural-number input. -/
abbrev Caller := Mixed Nat (Bool × Bool) Nat Nat Bool

/-- A private start and a lazy touch lie between two full reads of the same input. -/
@[expose] def repeatWithInternal : OracleComp Caller Bool := do
  let _ ← liftM (Caller.query (.inl (.inr 7)))
  let start ← liftM (Caller.query (.inr (.inl 1)))
  let _ ← liftM (Caller.query (.inr (.inr (.inl (.inl 1)))))
  let _ ← liftM (Caller.query (.inl (.inr 7)))
  pure start

/-- A caller can ask for just one internal graph node. -/
@[expose] def nodeOnly : OracleComp Caller Bool :=
  liftM (Caller.query (.inr (.inr (.inr 3))))

/-- Assigning the private calls zero cost leaves exactly the two original full reads. -/
theorem repeat_cost :
    runMixed (Equiv.refl (Bool × Bool)) (fun _ => 0) repeatWithInternal =
      (fun x => (x, 2)) <$> simulateQ (expand (Equiv.refl (Bool × Bool))) repeatWithInternal := by
  simp [runMixed, repeatWithInternal, mixedCost, rawCost, QueryImpl.withAddCost,
    QueryImpl.withCost_apply, AddWriterT.runAdd, WriterT.run_bind, simulateQ_map, map_bind]

/-- A graph node read can carry the scheme's own charge without any public query. -/
theorem node_cost (charge : Nat) :
    runMixed (Equiv.refl (Bool × Bool)) (fun _ => charge) nodeOnly =
      (fun x => (x, charge)) <$> simulateQ (expand (Equiv.refl (Bool × Bool))) nodeOnly := by
  simp [runMixed, nodeOnly, mixedCost, QueryImpl.withAddCost, QueryImpl.withCost_apply,
    AddWriterT.runAdd, simulateQ_map]

end VCVioTest.RandomOracleMixedQueries
