/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Operational random-oracle controls

Free local coins and charged hash requests use different branches of one oracle sum.
`unifFwdImpl` forwards local coins and `randomOracle` caches hash answers. Adversaries receive
only the public address; the experiment owns the cache. The zero-query control exercises
`roSim.run'_bind_of_isQueryBoundP_zero`: an adversary with no hash budget leaves the cache
empty, so the checked cell is still a fresh bit.

Derived from Verified-zkEVM/leanth at 23929f8c922cd4461ab22dbfaa6520f3ad23a3b2,
`Leanth/XMSS/RandomOracle.lean:266-476`. These controls concern the operational oracle model
and structural query bound, independently of any signature scheme or compilation theorem.
-/

/- Original source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Stefano Rocca, Aristotle (Harmonic)
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
open scoped OracleSpec.PrimitiveQuery

namespace VCVioTest.RandomOracleControls

/-- Two public addresses, each containing one hidden Boolean oracle answer. -/
abbrev HashSpec : OracleSpec Bool := Bool →ₒ Bool

/-- Fresh local randomness on the left; charged cached requests on the right. -/
abbrev MainSpec : OracleSpec (Nat ⊕ Bool) := unifSpec + HashSpec

/-- Run the standard lazy oracle from an empty experiment-owned cache. -/
noncomputable def runROM {α : Type} (oa : OracleComp MainSpec α) : ProbComp α :=
  (simulateQ (unifFwdImpl HashSpec + HashSpec.randomOracle) oa).run' ∅

/-- A structural bound on charged requests, with no bound on free local coins. -/
abbrev IsHashQueryBound {α : Type} (oa : OracleComp MainSpec α) (q : ℕ) : Prop :=
  oa.IsQueryBoundP (· matches .inr _) q

/-- An adversary sees the public address, not the oracle table or its cache. -/
structure QueryGapAdversary (q : ℕ) where
  /-- The adversary's guess for the oracle answer at the public address. -/
  attack : Bool → OracleComp MainSpec Bool
  /-- Every attack satisfies the charged-query allowance. -/
  bound : ∀ t, IsHashQueryBound (attack t) q

/-- Read the hidden cell once and return its answer. -/
def oneQuery : QueryGapAdversary 1 where
  attack t := MainSpec.query (.inr t)
  bound _ := by simp [IsHashQueryBound]

/-- A charged request cannot be assigned structural budget zero. -/
theorem oneQuery_not_zero (t : Bool) : ¬ IsHashQueryBound (oneQuery.attack t) 0 := by
  simp [oneQuery, IsHashQueryBound]

/-- Local sampling remains available with charged budget zero. -/
theorem localCoin_zero_bound (n : ℕ) :
    IsHashQueryBound (MainSpec.query (.inl n) : OracleComp MainSpec (Fin (n + 1))) 0 := by
  simp [IsHashQueryBound]

/-- A local Boolean-sized coin has its exact uniform law. -/
theorem localCoin_uniform (x : Fin 2) :
    𝒟[(runROM (MainSpec.query (.inl 1) : OracleComp MainSpec (Fin 2)) :
      ProbComp (Fin 2))] {x} = 2⁻¹ := by
  simp [runROM, unifFwdImpl, StateT.run'_eq]

/-- Query one address twice and compare the two replies. -/
def repeatHash (t : Bool) : OracleComp MainSpec Bool := do
  let x ← MainSpec.query (.inr t)
  let y ← MainSpec.query (.inr t)
  return decide (x = y)

/-- The second query hits the cache, so repeated requests agree with probability one. -/
theorem repeatHash_consistent (t : Bool) : 𝒟[runROM (repeatHash t)] {true} = 1 := by
  simp [-Bool.univ_eq, runROM, repeatHash, StateT.run'_eq, StateT.run_bind]

/-- Query two public addresses and retain both answers. -/
def twoHashes (t u : Bool) : OracleComp MainSpec (Bool × Bool) := do
  let x ← MainSpec.query (.inr t)
  let y ← MainSpec.query (.inr u)
  return (x, y)

/-- Different cache misses give independent Boolean answers. -/
theorem twoHashes_independent (t u : Bool) (hne : u ≠ t) (x y : Bool) :
    𝒟[runROM (twoHashes t u)] {(x, y)} = 4⁻¹ := by
  have hrun : runROM (twoHashes t u) =
      (do let a ← $ᵗ Bool; let b ← $ᵗ Bool; pure (a, b) : ProbComp (Bool × Bool)) := by
    simp [runROM, twoHashes, StateT.run'_eq, StateT.run_bind,
      QueryCache.cacheQuery_of_ne, hne]
  rw [hrun, evalDist_pair]
  norm_num [← Set.singleton_prod_singleton, Measure.prod_prod,
    SampleableType.evalDist_uniformSample_singleton, ← ENNReal.mul_inv]

/-- Local randomness between two same-address requests does not change the cached answer. -/
def repeatHashWithCoin (t : Bool) : OracleComp MainSpec Bool := do
  let x ← MainSpec.query (.inr t)
  let _ ← MainSpec.query (.inl 1)
  let y ← MainSpec.query (.inr t)
  return decide (x = y)

/-- Free local randomness neither resets nor replaces the hash cache. -/
theorem repeatHashWithCoin_consistent (t : Bool) :
    𝒟[runROM (repeatHashWithCoin t)] {true} = 1 := by
  simp [-Bool.univ_eq, runROM, repeatHashWithCoin, StateT.run'_eq, StateT.run_bind,
    unifFwdImpl]

/-- Check the adversary's guess using the same oracle and the same cache. -/
def finishGuess (attack : OracleComp MainSpec Bool) (t : Bool) : OracleComp MainSpec Bool := do
  let guess ← attack
  let digest ← MainSpec.query (.inr t)
  return decide (guess = digest)

private theorem uniform_bool_guess (guess : Bool) :
    𝒟[(do let b ← $ᵗ Bool; pure (decide (guess = b)) : ProbComp Bool)] {true} = 2⁻¹ := by
  simpa only [pure_bind, eq_comm, one_div] using
    ProbComp.evalDist_decide_eq_uniformBool_half (fun _ ↦ pure guess) rfl

/-- Every structurally zero-query adversary guesses a fresh hidden bit with probability one
half, even when its control flow uses arbitrarily many free local random draws. -/
theorem zeroHashQuery_guess_probability (attack : OracleComp MainSpec Bool)
    (h : IsHashQueryBound attack 0) (t : Bool) :
    𝒟[runROM (finishGuess attack t)] {true} = 2⁻¹ := by
  -- The attack leaves the cache empty, so the checked cell is a fresh bit.
  have hrun : runROM (finishGuess attack t) = runROM attack >>= fun guess ↦
      (do let b ← $ᵗ Bool; pure (decide (guess = b)) : ProbComp Bool) := by
    rw [runROM, finishGuess, roSim.run'_bind_of_isQueryBoundP_zero _ (fun _ => rfl) h]
    simp [runROM, StateT.run'_eq]
  rw [hrun, evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable]
  simp only [uniform_bool_guess, lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one]

/-- The exact success probability of any zero-query adversary. -/
theorem queryGap_zero_exact (A : QueryGapAdversary 0) (t : Bool) :
    𝒟[runROM (finishGuess (A.attack t) t)] {true} = 2⁻¹ :=
  zeroHashQuery_guess_probability (A.attack t) (A.bound t) t

/-- One charged query recovers the checked answer with certainty. -/
theorem queryGap_one_exact (t : Bool) :
    𝒟[runROM (finishGuess (oneQuery.attack t) t)] {true} = 1 :=
  repeatHash_consistent t

/-- The structural budget changes attainable success in this fixed operational game. -/
theorem queryGap_one_strictly_better (A : QueryGapAdversary 0) (t : Bool) :
    𝒟[runROM (finishGuess (A.attack t) t)] {true} <
      𝒟[runROM (finishGuess (oneQuery.attack t) t)] {true} := by
  rw [queryGap_zero_exact, queryGap_one_exact]
  exact ENNReal.inv_lt_one.mpr (by norm_num)

end VCVioTest.RandomOracleControls
