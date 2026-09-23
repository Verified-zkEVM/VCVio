/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.ListCache

/-!
# Association-list cache regressions

A counter distinguishes fresh draws from cache hits. The adaptive client queries
its first response and then revisits the original key, exposing both cache updates
and the fact that a repeated query performs no additional draw.
-/

public section

open OracleComp OracleSpec QueryImpl.ListCache

namespace ListCacheTests

@[expose] def fresh (_ : Nat) : StateM Nat Nat := do
  let r ← get
  modify (· + 1)
  return r

-- A duplicate key keeps the first binding, and a hit leaves both states unchanged.
example : ((handler fresh 1).run [(1, 7), (1, 3)]).run 20 =
    ((7, [(1, 7), (1, 3)]), 20) := rfl

example : ((handler fresh 2).run [(1, 7), (1, 3)]).run 20 =
    ((20, [(2, 20), (1, 7), (1, 3)]), 21) := rfl

example : ((handler fresh 2).run []).run 20 = ((20, [(2, 20)]), 21) := rfl

@[expose] def adaptive : OracleComp (Nat →ₒ Nat) (Nat × Nat × Nat) :=
  queryBind 2 fun first =>
    queryBind first fun second =>
      queryBind 2 fun repeated => pure (first, second, repeated)

example : ((simulateQ (handler fresh) adaptive).run []).run 20 =
    (((20, 21, 20), [(20, 21), (2, 20)]), 22) := rfl

example : ((simulateQ (handler fresh) adaptive).run [(2, 7), (2, 3)]).run 20 =
    (((7, 20, 7), [(7, 20), (2, 7), (2, 3)]), 21) := rfl

-- The same adaptive run through the function cache has the decoded joint state.
example :
    Prod.map id decode <$>
      (simulateQ (handler fresh) adaptive).run [(2, 7), (2, 3)] =
    (simulateQ (QueryImpl.withCaching fresh) adaptive).run (decode [(2, 7), (2, 3)]) :=
  adaptive_projection fresh adaptive _

-- Ordinary imports expose the reusable law at a nonzero Lean universe.
example (draw : QueryImpl (ULift.{1} Nat →ₒ ULift.{1} Nat) Id)
    (program : OracleComp (ULift.{1} Nat →ₒ ULift.{1} Nat) (ULift.{1} Bool))
    (cache : List (ULift.{1} Nat × ULift.{1} Nat)) :
    Prod.map id decode <$> (simulateQ (handler draw) program).run cache =
      (simulateQ draw.withCaching program).run (decode cache) :=
  adaptive_projection draw program cache

end ListCacheTests
