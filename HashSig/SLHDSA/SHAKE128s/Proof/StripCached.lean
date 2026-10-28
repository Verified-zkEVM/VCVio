/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.HonestProbes

/-!
# Answering the honest phase from the table

`CachedRun.run_eq_pure_of_cached` removes a computation whose queries are *all* cached. The
honest phase is not quite that: signing makes two message-dependent calls — the randomizer and
the message digest — that no walk can have programmed, so signing is a few fresh queries
interleaved with a great many cached ones.

What the input half needs is still the same thing: the honest phase must not *ask* at a
seed-bearing input, because the blind comparison strips exactly those entries and any query at
one breaks the coupling. Stripping the computation rather than the cache does it. `stripImpl
cache` is the handler that answers from `cache` where it can and forwards the rest, and
`simulateQ (stripImpl cache)` is the computation with every already-answered query replaced by
its answer.

Two facts make it usable, and neither costs anything:

* `run_simulateQ_strip` — the stripped computation has the same run as the original, cache and
  all. It is an equality, not a hop.
* `queriesUnder_strip_none` — the stripped computation asks only at inputs the cache does not
  answer. In particular it never asks at a canonical input, so never at a seed-bearing one.

The restriction to the honest phase is the point: the adversary's own queries must *not* be
stripped, since a query of its own at a seed-bearing input is precisely the event being
charged. So this is applied to `Scheme.keygenInternal` and `Scheme.sign` inside the
experiment, not to the experiment.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.StripCached

open CacheReplay

/-- Answer from the cache where it can, and forward the rest. -/
@[expose] def stripImpl (cache : QueryCache HashSpec) : QueryImpl HashSpec (OracleComp HashSpec) :=
  fun input =>
    match cache input with
    | some value => pure value
    | none => query (spec := HashSpec) input

/-- **Stripping changes nothing about the run.** Stated against any cache extending the one
stripping consults, because the run's cache grows while that one stays fixed — which is also
what lets the honest phase be stripped once, against the walk's cache, and then run at
whatever the game has accumulated by the time it reaches it. -/
theorem run_simulateQ_strip {α : Type} (computation : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) :
    ∀ current : QueryCache HashSpec,
      (∀ input value, cache input = some value → current input = some value) →
      (simulateQ randomOracle (simulateQ (stripImpl cache) computation)).run current =
        (simulateQ randomOracle computation).run current := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro current _; simp [simulateQ_pure, StateT.run_pure]
  | query_bind input next ih =>
    intro current hsub
    have hreal : simulateQ randomOracle
        (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) =
        randomOracle input := by simp
    have hstripped : simulateQ (stripImpl cache)
        (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) =
        stripImpl cache input := by simp
    have hlhs : (simulateQ randomOracle (simulateQ (stripImpl cache)
          (liftM (OracleSpec.query input) >>= next))).run current =
        (simulateQ randomOracle (stripImpl cache input)).run current >>= fun step =>
          (simulateQ randomOracle (simulateQ (stripImpl cache) (next step.1))).run step.2 := by
      rw [simulateQ_bind, hstripped, simulateQ_bind, StateT.run_bind]
    have hrhs : (simulateQ randomOracle
          (liftM (OracleSpec.query input) >>= next)).run current =
        (randomOracle input).run current >>= fun step =>
          (simulateQ randomOracle (next step.1)).run step.2 := by
      rw [simulateQ_bind, hreal, StateT.run_bind]
    rw [hlhs, hrhs]
    cases hcache : cache input with
    | some value =>
      have hcurrent : current input = some value := hsub input value hcache
      rw [show stripImpl cache input = (pure value : OracleComp HashSpec HashOutput) from by
          simp [stripImpl, hcache],
        simulateQ_pure, StateT.run_pure, pure_bind,
        QueryImpl.withCaching_run_some _ hcurrent, pure_bind]
      exact ih value current hsub
    | none =>
      rw [show stripImpl cache input =
          (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) from by
        simp [stripImpl, hcache], hreal]
      cases hcurrent : current input with
      | some answer =>
        rw [QueryImpl.withCaching_run_some _ hcurrent, pure_bind, pure_bind]
        exact ih answer current hsub
      | none =>
        rw [QueryImpl.withCaching_run_none _ hcurrent]
        simp only [uniformSampleImpl, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
          pure_bind]
        refine bind_congr fun answer => ?_
        refine ih answer _ fun key value hkey => ?_
        by_cases heq : key = input
        · exact absurd (heq ▸ hkey) (by rw [hcache]; simp)
        · rw [QueryCache.cacheQuery_of_ne _ _ heq]
          exact hsub key value hkey

end SLHDSA.SHAKE128s.StripCached
