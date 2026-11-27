/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.ObserveTrials
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Counting fresh accepted random-oracle replies

An eligible cache miss counts as one trial while the trial count is below the cap.
Eligibility can depend on the cache before the query.
A repeated query returns the cached answer and leaves both counters alone.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace randomOracle.FreshTrials

variable {A Y : Type} [DecidableEq A] [DecidableEq Y] [SampleableType Y]

/-- The cache together with the number of monitored fresh trials and their successes. -/
abbrev State (A Y : Type) := (A →ₒ Y).QueryCache × ℕ × ℕ

/-- The original random oracle with two passive counters for eligible cache misses. -/
@[expose] def observe (q : ℕ) (accepted : Finset Y) (eligible : A → (A →ₒ Y).QueryCache → Bool) :
    QueryImpl (A →ₒ Y) (StateT (State A Y) ProbComp) :=
  BernoulliMoment.observe (A →ₒ Y).randomOracle q
    (fun a c => (c a).isNone && eligible a c) (fun _ y => decide (y ∈ accepted))

/-- Erasing the counters recovers the entire original run, including its final cache. -/
theorem forget {γ : Type} (q : ℕ) (accepted : Finset Y) (eligible : A → (A →ₒ Y).QueryCache → Bool)
    (oa : OracleComp (A →ₒ Y) γ) (c : (A →ₒ Y).QueryCache) (n v : ℕ) :
    Prod.map id Prod.fst <$> (simulateQ (observe q accepted eligible) oa).run (c, n, v) =
      (simulateQ randomOracle oa).run c :=
  extendState_run_proj_eq _ _ _ _ _

/-- Each counted cache miss is a Bernoulli trial with the fresh acceptance probability. -/
theorem countsTrials (q : ℕ) (accepted : Finset Y) (eligible : A → (A →ₒ Y).QueryCache → Bool)
    (p : ℝ) (rate : Pr{let y ← $ᵗ Y}[y ∈ accepted] = ENNReal.ofReal p) :
    BernoulliMoment.CountsTrials (observe q accepted eligible) (fun s => s.2.1) (fun s => s.2.2)
      p q := by
  apply BernoulliMoment.counts_observe
  intro a c active
  obtain ⟨cold, _⟩ := Bool.and_eq_true_iff.mp active
  rw [Option.isNone_iff_eq_none] at cold
  simpa [randomOracle.run_eq, cold] using rate

end randomOracle.FreshTrials
