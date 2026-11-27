/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.MixedCap

/-!
# A refused full query after an internal touch

At zero budget a free internal touch is still recorded before the next full public read is refused.
-/

public section
open OracleSpec OracleComp CanonicalGraph.PairedQueries
open scoped OracleSpec.PrimitiveQuery

namespace VCVioTest.RandomOracleMixedCap
/-- The caller asks for full words or internal graph operations. -/
abbrev Caller := Mixed Nat (Bool × Bool) Nat Nat Bool

/-- A free internal touch survives a refused full query at zero budget.
Neither ordinary row is fetched, and a previously pending cell remains first. -/
theorem touch_before_refusal (G : CanonicalGraph (PairedSpec Nat Bool) Nat Nat Bool)
    (s : RelabelState (PairedSpec Nat Bool) Nat Nat Bool) :
    let cell : Nat ⊕ Nat := .inl 1
    let caller : OracleComp Caller (Bool × Bool) := do
      let _ ← liftM (Caller.query (.inr (.inr (.inl cell))))
      liftM (Caller.query (.inl (.inr 7)))
    (simulateQ G.deferredImpl (simulateQ (expand (Equiv.refl (Bool × Bool)))
      (WeightedCap.capCompOpt
        (mixedCost (H := Bool) (F := Bool × Bool) (fun _ => 0)) 0 caller))).run
        (s, [.inr 2]) = pure (none, (s, [.inr 2, cell])) := by
  intro cell caller
  have raw : WeightedCap.capCompOpt (spec := Caller)
      (mixedCost (H := Bool) (F := Bool × Bool) (fun _ => 0))
      0 (liftM (Caller.query (.inl (.inr 7))) : OracleComp Caller (Bool × Bool)) = pure none := by
    rfl
  simp [caller, WeightedCap.capCompOpt_query_bind, mixedCost, expand, internalRead,
    G.deferredImpl_run_touch, raw]

end VCVioTest.RandomOracleMixedCap
