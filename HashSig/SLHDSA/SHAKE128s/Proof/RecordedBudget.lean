/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedQueries
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedCharges
public import HashSig.SLHDSA.SHAKE128s.Proof.HonestGrowth
public import HashSig.SLHDSA.SHAKE128s.Proof.GraphStakes
public import HashSig.SLHDSA.SHAKE128s.Proof.ClaimedProbes

/-!
# The budget, carried to the recorded game

`RecordedQueries.card_toFinset_le_work` bounds the recorded set by the work this run charges.
This file supplies `map_countAllHashes`, the one bridge needed to carry a bound on the unwarmed,
unstripped, uninstrumented game to the recorded one: `WarmedGame.tail` is counted while the
stripped and recorded games are not. The counter only decorates the value, so forgetting it
returns the computation itself, and a supported uncounted run has a supported counted
counterpart.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.RecordedBudget

variable {α : Type}

open Security WarmedGame

/-- **Forgetting the count returns the computation.** -/
theorem map_countAllHashes {α : Type} (computation : OracleComp OracleWorld α) :
    Prod.fst <$> countAllHashes computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [GrowthBudget.countAllHashes_pure, map_pure]
  | query_bind queried next ih =>
    rw [GrowthBudget.countAllHashes_query_bind, map_bind]
    exact congrArg (Bind.bind _) (funext fun answer => by
      rw [Functor.map_map]
      exact ih answer)

attribute [local irreducible] WarmedGame.afterSeeds StrippedGame.strippedAfterSeeds
  RecordedQueries.recordedAfterSeeds Scheme.verify Scheme.keygenInternal Security.countQueries

end SLHDSA.SHAKE128s.RecordedBudget
