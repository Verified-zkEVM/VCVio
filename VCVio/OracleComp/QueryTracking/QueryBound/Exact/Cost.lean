/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Exact
public import VCVio.OracleComp.QueryTracking.WriterCost.LawfulAttach

/-!
# Structural counts imply unit costs on support

A branch-uniform certificate gives an exact unit cost on every reachable interpreted result.
The source-index and runtime universes are independent. Only lawful attachment is required;
this one-way statement neither supplies reachable outputs nor recovers a structural certificate.
-/

public section
open OracleComp OracleSpec

namespace OracleComp.QueryBound.ExactQueryCount

/-- A structural count is exact on every reachable unit-cost runtime result. -/
theorem queryCostExactly.{i, z} :
  ∀ {ι : Type i} {spec : OracleSpec.{i, 0} ι} {m : Type → Type z}
    [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    {α : Type} (impl : QueryImpl spec m) {computation : OracleComp spec α} {count : Nat},
    ExactQueryCount computation count →
      AddWriterT.QueryCostExactly (simulateQ impl.withUnitCost computation) count := by
  intro ι spec m _ _ _ _ α impl computation count hexact
  induction hexact with
  | pure value =>
      simpa only [simulateQ_pure] using AddWriterT.LawfulAttach.queryCostExactly_pure (m := m) value
  | query input next nextCount hnext ih =>
      change AddWriterT.QueryCostExactly
        (simulateQ impl.withUnitCost (liftM (spec.query input) >>= next))
        (nextCount + 1)
      rw [simulateQ_bind, simulateQ_spec_query]
      have hquery : AddWriterT.QueryCostExactly (impl.withUnitCost input) 1 := by
        rw [QueryImpl.withUnitCost_apply]
        simpa only [Nat.add_zero] using AddWriterT.LawfulAttach.queryCostExactly_bind
          (AddWriterT.LawfulAttach.queryCostExactly_addTell (m := m) 1)
          (fun _ => AddWriterT.LawfulAttach.queryCostExactly_monadLift (impl input))
      simpa only [Nat.add_comm] using AddWriterT.LawfulAttach.queryCostExactly_bind hquery ih

end OracleComp.QueryBound.ExactQueryCount
