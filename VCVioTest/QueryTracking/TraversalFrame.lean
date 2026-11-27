/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal.Frame
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Complete observations of traversal frames

Repeated coordinates can read an unwritten cell while retaining all calls, the complete final
cell function, subsequent query effects, ordered execution, cost and the complete outer cache/state.
Neither the input domain nor the answer carrier is finite.
-/

public section

universe u

open OracleComp OracleSpec

namespace VCVioTest.TraversalFrame

/-- Initial cell values distinguish an untouched key from every overwritten response. -/
@[expose] def initial (key : Nat) : Nat := 10 * key + 5

/-- Every query reads the same frame cell while retaining its current coordinate. -/
@[expose] def input (node : Nat) (cells : Nat → Nat) : Nat × Nat := (node, cells 2)

/-- An answer overwrites its addressed cell without assuming the coordinate is new. -/
@[expose] def step (node : Nat) (cells : Nat → Nat) (answer : Nat) : Nat → Nat :=
  Function.update cells node answer

/-- Every supported traversal result retains its unwritten cell despite repeated writes. -/
theorem outside_on_every_run (final : Nat → Nat)
    (reachable : final ∈ support
      (RandomOracleTraversal.evaluate input step [0, 0, 1] initial)) : final 2 = 25 :=
  RandomOracleTraversal.read_outside_of_mem_support input id (fun _ answer => answer)
    [0, 0, 1] initial 2 (by
      intro node member same
      change node = 2 at same
      subst node
      simp at member) final reachable

/-- Replacing an unwritten read retains the full final cell function and a subsequent real query. -/
theorem complete_effectful_continuation :
    (do
      let final ← RandomOracleTraversal.evaluate input step [0, 0, 1] initial
      let answer ← query (spec := (Nat × Nat) →ₒ Nat) (final 2, final 0)
      pure (final, answer)) =
    (do
      let final ← RandomOracleTraversal.evaluate input step [0, 0, 1] initial
      let answer ← query (spec := (Nat × Nat) →ₒ Nat) (25, final 0)
      pure (final, answer)) :=
  RandomOracleTraversal.bind_read_outside input id (fun _ answer => answer)
    [0, 0, 1] initial 2 (by
      intro node member same
      change node = 2 at same
      subst node
      simp at member)
    (fun final value => do
      let answer ← query (spec := (Nat × Nat) →ₒ Nat) (value, final 0)
      pure (final, answer))

/-- Any cached or ordered-cost interpretation retains both complete cell and outer states. -/
theorem complete_outer_observation (m : Type → Type u) [Monad m]
    (Cache C : Type) [AddMonoid C]
    (handler : QueryImpl ((Nat × Nat) →ₒ Nat) (StateT Cache m))
    (cost : Nat × Nat → C) (cache : Cache) :
    ((simulateQ (handler.withAddCost cost) (do
      let final ← RandomOracleTraversal.evaluate input step [0, 0, 1] initial
      let answer ← query (spec := (Nat × Nat) →ₒ Nat) (final 2, final 0)
      pure (final, answer))).runAdd).run cache =
    ((simulateQ (handler.withAddCost cost) (do
      let final ← RandomOracleTraversal.evaluate input step [0, 0, 1] initial
      let answer ← query (spec := (Nat × Nat) →ₒ Nat) (25, final 0)
      pure (final, answer))).runAdd).run cache :=
  congrArg (fun program : OracleComp ((Nat × Nat) →ₒ Nat) ((Nat → Nat) × Nat) =>
    ((simulateQ (handler.withAddCost cost) program).runAdd).run cache)
    complete_effectful_continuation

end VCVioTest.TraversalFrame
