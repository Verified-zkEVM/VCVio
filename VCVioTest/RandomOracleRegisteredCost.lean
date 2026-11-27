/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.MarkedReplies.Cost

/-!
# A warm lookup costs one physical query and zero watched queries

A warm lookup at an active key increments the total public-call counter without counting
a fresh target trial.
-/

public section

open OracleSpec OracleComp randomOracle.Targets

namespace VCVioTest.RandomOracleRegisteredCost

/-- A Boolean random oracle indexed by natural numbers. -/
abbrev H := Nat →ₒ Bool

/-- A repeated answer at an active key costs one physical query and creates no fresh match. -/
theorem warm_lookup (t : Nat) (n : Nat) :
    let s : State H Unit Bool :=
      ⟨(∅ : H.QueryCache).cacheQuery t true, fun _ => some true, 0, false⟩
    let reg : Register H Unit Unit Bool := fun _ _ old => old
    (counted reg (fun _ => some ()) (fun _ w => w) (.inl (.inr t))).run (s, n) =
      pure (true, (s, n + 1)) := by
  dsimp only
  rw [counted, QueryImpl.extendState_apply, public_run, QueryImpl.withCaching_run_some _
    (QueryCache.cacheQuery_self _ _ _), map_pure, pure_bind]
  simp [update, publicCost]

end VCVioTest.RandomOracleRegisteredCost
