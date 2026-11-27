/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.WeightedCap

/-!
# Zero-cost queries and repeated charged requests

A zero-cost query can choose a continuation even at zero budget. Two unit-cost reads of
the same address need two units, so a budget of one refuses the second.
-/

public section
open OracleSpec OracleComp

namespace OracleComp.WeightedCap.Test

/-- Both requests return a Boolean. Only `true` costs one unit. -/
abbrev Source := Bool →ₒ Bool

private def fee : Bool → Nat
  | false => 0
  | true => 1

/-- A free choice still takes place at zero budget, before a paid call would be refused. -/
example : capCompOpt fee 0 (do
      let choice ← liftM (Source.query false)
      if choice then liftM (Source.query true) else pure false) =
    (do
      let choice ← liftM (Source.query false)
      if choice then pure none else pure (some false) : OracleComp Source (Option Bool)) := by
  rw [capCompOpt_query_bind]
  simp only [fee, Nat.sub_zero]
  apply bind_congr
  intro x
  cases x <;> rfl

/-- The second request for the same charged key stops before its answer can be read. -/
example : capCompOpt fee 1 (do
      let _ ← liftM (Source.query true)
      let b ← liftM (Source.query true)
      pure b) =
    (do
      let _ ← liftM (Source.query true)
      pure none : OracleComp Source (Option Bool)) := rfl

end OracleComp.WeightedCap.Test
