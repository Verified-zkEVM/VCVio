/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.VerificationBudget

/-!
# The total hash count

`countAllHashes` only adds bookkeeping to the returned value: it issues exactly the queries of
the underlying computation, in the same order, so the cache evolves identically and the count is
the number of hash queries made. This file states its step laws (`countAllHashes_pure`,
`countAllHashes_query_bind`, `countAllHashes_query`) and that the count is additive over
sequencing (`countAllHashes_bind`).
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.GrowthBudget

variable {α β : Type}

open Security GrowthCharge

/-- A pure computation makes no hash queries. -/
@[simp] theorem countAllHashes_pure {α : Type} (value : α) :
    countAllHashes (pure value : OracleComp OracleWorld α) = pure (value, 0) := by
  simp [countAllHashes]

/-- A query followed by a continuation is charged its `hashCost` on top of the continuation's
count. -/
theorem countAllHashes_query_bind {α : Type} (queried : OracleWorld.Domain)
    (next : OracleWorld.Range queried → OracleComp OracleWorld α) :
    countAllHashes (liftM (OracleWorld.query queried) >>= next) =
      liftM (OracleWorld.query queried) >>= fun answer =>
        (fun result => (result.1, hashCost queried + result.2)) <$>
          countAllHashes (next answer) := by
  simp only [countAllHashes, simulateQ_bind, simulateQ_spec_query, addCostOracle,
    QueryImpl.withAddCost, QueryImpl.withCost]
  simp [Functor.map_map, map_bind, bind_map_left]

/-- A single query is charged exactly its `hashCost`. -/
theorem countAllHashes_query (queried : OracleWorld.Domain) :
    countAllHashes (liftM (OracleWorld.query queried)) =
      liftM (OracleWorld.query queried) >>= fun answer =>
        (pure (answer, hashCost queried) :
          OracleComp OracleWorld (OracleWorld.Range queried × Nat)) := by
  conv_lhs => rw [show (liftM (OracleWorld.query queried) :
      OracleComp OracleWorld (OracleWorld.Range queried)) =
    liftM (OracleWorld.query queried) >>= pure from (bind_pure _).symm,
    countAllHashes_query_bind]
  simp [countAllHashes_pure]

/-- The total count is additive over sequencing: the count of `c >>= f` splits into the
count of `c` and the count of the continuation. -/
theorem countAllHashes_bind {α β : Type} (computation : OracleComp OracleWorld α)
    (continuation : α → OracleComp OracleWorld β) :
    countAllHashes (computation >>= continuation) =
      (countAllHashes computation >>= fun first =>
        countAllHashes (continuation first.1) >>= fun second =>
          (pure (second.1, first.2 + second.2) :
            OracleComp OracleWorld (β × Nat))) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [countAllHashes_pure]
  | query_bind queried next ih =>
    rw [bind_assoc, countAllHashes_query_bind, countAllHashes_query_bind]
    simp only [ih]
    simp [map_bind, bind_map_left, bind_assoc, Nat.add_assoc]

end SlhDsaSecurity.GrowthBudget
