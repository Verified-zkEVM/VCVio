/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay

/-!
# A run that asks nothing new

After the canonical graph has been walked, the honest parties ask the oracle nothing it has
not already answered: every input key generation consults is a canonical input, and the walk
installed all of those. Such a run is not merely *determined* by the cache — it is a `pure`
computation. It samples nothing, and it leaves the cache exactly as it found it.

That is the lemma here, and it is what lets the honest phase be removed from the game rather
than merely analysed inside it. The removal is what the input side needs: the blind comparison
compares a run against the programmed cache with the same run against the cache stripped of
its seed-bearing entries, and those two runs agree only until something asks at a seed-bearing
input. Key generation asks at one immediately — every FORS and WOTS secret is
`PRF(PK.seed ‖ ADRS ‖ SK.seed)` — so with the honest phase still in the computation the
comparison says nothing at all. With it replaced by the table lookup it computes, the only
queries left at a seed-bearing input are the adversary's, which is the event to be charged.

Nothing is lost in the replacement: `run_eq_pure_of_cached` is an equality of computations,
not a hop between games.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CachedRun

open CacheReplay

/-- **A fully cached run is a pure computation.** If every input a hash-only computation
consults is already in the cache, running it against the oracle returns the replayed value and
the untouched cache, with no sampling at all. -/
theorem run_eq_pure_of_cached {α : Type} (computation : OracleComp HashSpec α)
    (cache : QueryCache HashSpec)
    (hcached : ∀ probe, QueriesUnder cache computation probe → cache probe ≠ none) :
    (simulateQ randomOracle computation).run cache =
      (pure ((simulateQ (replay cache) computation : Id α), cache) :
        ProbComp (α × QueryCache HashSpec)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; rfl
  | query_bind input next ih =>
    obtain ⟨value, hvalue⟩ :=
      Option.ne_none_iff_exists'.mp (hcached input (QueriesUnder.head input next))
    have hreplay : replay cache input = value := by simp [replay, hvalue]
    have hstep : (randomOracle input).run cache =
        (pure (value, cache) : ProbComp (HashOutput × QueryCache HashSpec)) := by
      rw [QueryImpl.withCaching_run_some _ hvalue]
    have hquery : simulateQ randomOracle
        (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) =
        randomOracle input := by simp
    rw [simulateQ_bind, hquery, StateT.run_bind, hstep, pure_bind]
    refine (ih value ?_).trans ?_
    · intro probe hprobe
      exact hcached probe (QueriesUnder.tail input probe next (by rw [hreplay]; exact hprobe))
    · congr 1
      rw [simulateQ_bind,
        show (simulateQ (replay cache)
            (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) : Id HashOutput)
          = value from by simp [replay, hvalue]]
      rfl

end SlhDsaSecurity.CachedRun
