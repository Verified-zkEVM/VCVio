/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Relabel

/-! # Relabelling query logs and extracting collisions

Checks for `VCVio.OracleComp.QueryTracking.LoggingOracle.Relabel` with `f n = n % 4` on `ℕ`, so
`5` and `1` collide and `5` and `2` do not.

Dropping either conjunct of the search in `QueryLog.collisionCandidate` breaks a check. Without
`e.1 ≠ msg` the search returns the forged message itself, `(5, 5)`, on the log `[5, 1]`; without
`f e.1 = f msg` it returns the unrelated earlier entry, `(5, 2)`, on the log `[2, 1]`.
-/

public section

open OracleSpec

namespace QueryLogRelabelTest

/-- The map whose collisions the checks extract. -/
def f (n : ℕ) : ℕ := n % 4

/-- Relabelling maps each logged input by `f` and keeps the responses. -/
example : QueryLog.relabel f ([⟨5, true⟩, ⟨2, false⟩] : QueryLog (ℕ →ₒ Bool)) =
    [⟨1, true⟩, ⟨2, false⟩] := rfl

/-- A logged input with the same image as `5` is extracted as a collision. -/
example : QueryLog.collisionCandidate f 5 ([⟨2, ()⟩, ⟨1, ()⟩] : QueryLog (ℕ →ₒ Unit)) = (5, 1) :=
  rfl

example : QueryLog.hasCollision f 5 ([⟨2, ()⟩, ⟨1, ()⟩] : QueryLog (ℕ →ₒ Unit)) = true := by
  decide

/-- An earlier entry equal to the forged message is skipped, so the later collision is found. -/
example : QueryLog.collisionCandidate f 5 ([⟨5, ()⟩, ⟨1, ()⟩] : QueryLog (ℕ →ₒ Unit)) = (5, 1) :=
  rfl

/-- An input with a different image is not a collision. -/
example : QueryLog.hasCollision f 5 ([⟨2, ()⟩] : QueryLog (ℕ →ₒ Unit)) = false := by
  decide

/-- A log holding only the forged message has no collision. -/
example : QueryLog.hasCollision f 5 ([⟨5, ()⟩] : QueryLog (ℕ →ₒ Unit)) = false := by
  decide

end QueryLogRelabelTest
