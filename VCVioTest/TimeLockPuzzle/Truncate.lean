/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle.Truncate

/-!
# Delay security within a round bound on a toy puzzle

Checks of `TimeLockPuzzle.Adversary.truncate` and `TimeLockPuzzle.delayAdvantageWithin` through
ordinary imports, on a one-round toy puzzle over one oracle on `Bool`: the main statements
instantiate at the toy puzzle; an adversary whose online phase is a three-round chain, truncated
at one round, fits the budget `(1, 3)` and returns the fallback key; and at three rounds its
truncation is itself and its per-run event is its delay advantage.
-/

public section

namespace VCVioTest.TimeLockPuzzle.Truncate

open OracleComp OracleSpec ENNReal

/-- One oracle on `Bool`. -/
abbrev boolSpec : OracleSpec Bool := fun _ => Bool

/-- The answer at `false`, asked in one round. -/
def queryFalse : OracleComp (unifSpec + boolSpec.batch) Bool := do
  let us ← liftM ((unifSpec + boolSpec.batch).query (.inr [false]))
  pure (us ⟨0, Nat.zero_lt_one⟩)

/-- A one-round toy puzzle: the puzzle is trivial and the key is the oracle's answer at `false`. -/
def toy : TimeLockPuzzle boolSpec Unit Bool where
  gen := (fun k => ((), k)) <$> queryFalse
  solve _ := some <$> queryFalse

/-- A deterministic handler negating its point. -/
def notImpl : QueryImpl boolSpec Id := fun b => !b

/-- A deterministic handler for local coins, always answering `0`. -/
def zeroCoins : QueryImpl unifSpec Id := fun _ => (0 : Fin _)

/-- Three rounds, each querying the answer to the previous one. -/
def threeRounds : OracleComp (unifSpec + boolSpec.batch) Bool := do
  let a ← liftM ((unifSpec + boolSpec.batch).query (.inr [false]))
  let b ← liftM ((unifSpec + boolSpec.batch).query (.inr [a ⟨0, Nat.zero_lt_one⟩]))
  let c ← liftM ((unifSpec + boolSpec.batch).query (.inr [b ⟨0, Nat.zero_lt_one⟩]))
  pure (c ⟨0, Nat.zero_lt_one⟩)

/-- The adversary with no preprocessing whose online phase is the three-round chain. -/
def threeAdv : TimeLockPuzzle.Adversary boolSpec Unit Bool where
  State := Unit
  preprocess := pure ()
  online _ _ := threeRounds

theorem threeAdv_isQueryBound : threeAdv.IsQueryBound 0 (3, 3) :=
  ⟨by simp [threeAdv], fun _ _ => by simp [threeAdv, threeRounds]⟩

/-! ## The main statements at the toy puzzle -/

example (adv : TimeLockPuzzle.Adversary boolSpec Unit Bool) (r : ℕ) (k₀ : Bool) :
    TimeLockPuzzle.delayAdvantageWithin toy adv r ≤
      TimeLockPuzzle.delayAdvantage toy (adv.truncate r k₀) :=
  TimeLockPuzzle.delayAdvantageWithin_le_delayAdvantage_truncate toy adv r k₀

example (adv : TimeLockPuzzle.Adversary boolSpec Unit Bool) (r : ℕ) :
    TimeLockPuzzle.delayAdvantageWithin toy adv r ≤
      TimeLockPuzzle.delayAdvantage toy adv :=
  TimeLockPuzzle.delayAdvantageWithin_le_delayAdvantage toy adv r

/-- Delay security of the toy puzzle at `(r, q)` bounds the per-run event of every adversary
within the point budget `q`, with no bound on its rounds. -/
example {Q r q : ℕ} {ε : ℝ≥0∞} (hsec : TimeLockPuzzle.DelaySecure toy Q (r, q) ε)
    (adv : TimeLockPuzzle.Adversary boolSpec Unit Bool)
    (hpre : IsPreprocessingQueryBound adv.preprocess Q)
    (honline : ∀ σ puzzle, IsPointQueryBound (adv.online σ puzzle) q) :
    TimeLockPuzzle.delayAdvantageWithin toy adv r ≤ ε :=
  TimeLockPuzzle.delayAdvantageWithin_le_of_delaySecure hsec hpre honline

/-- The three-round adversary outputs the key within one round with probability at most `ε`,
whenever the toy puzzle is delay secure at `(1, 3)` against adversaries without preprocessing. -/
example {ε : ℝ≥0∞} (hsec : TimeLockPuzzle.DelaySecure toy 0 (1, 3) ε) :
    TimeLockPuzzle.delayAdvantageWithin toy threeAdv 1 ≤ ε :=
  TimeLockPuzzle.delayAdvantageWithin_le_of_delaySecure hsec threeAdv_isQueryBound.1
    fun σ puzzle => (threeAdv_isQueryBound.2 σ puzzle).isPointQueryBound

/-- The per-run event rewrites, through an ordinary import, to the probability that
`delayExperimentWithin` returns `true`. -/
example (adv : TimeLockPuzzle.Adversary boolSpec Unit Bool) (r : ℕ) :
    TimeLockPuzzle.delayAdvantageWithin toy adv r =
      (ProbCompRuntime.rom _).evalDist (toy.delayExperimentWithin adv r) {true} := by
  rw [TimeLockPuzzle.delayAdvantageWithin_eq]

/-! ## Truncating the three-round adversary after one round -/

/-- The truncation fits one round and three points, with no preprocessing queries. -/
example (k₀ : Bool) : (threeAdv.truncate 1 k₀).IsQueryBound 0 (1, 3) :=
  TimeLockPuzzle.Adversary.isQueryBound_truncate threeAdv_isQueryBound.1
    (fun σ puzzle => (threeAdv_isQueryBound.2 σ puzzle).isPointQueryBound) 1 k₀

/-- Its online phase submits the first round and returns the fallback. -/
example (k₀ : Bool) :
    (threeAdv.truncate 1 k₀).online () () = (do
      let _ ← liftM ((unifSpec + boolSpec.batch).query (.inr [false]))
      pure k₀) := by
  simp only [TimeLockPuzzle.Adversary.truncate, threeAdv, threeRounds,
    truncate_succ_query_bind_inr, truncate_zero_query_bind_inr]

/-- Under the negating handler the full online phase returns `true` after three rounds. -/
example : runCountingRounds (zeroCoins + notImpl).batch' (threeAdv.online () ()) = (true, 3) := by
  simp only [threeAdv, threeRounds, runCountingRounds_query_bind, runCountingRounds_pure]
  rfl

/-- Its truncation after one round returns the fallback `false` instead. -/
example :
    simulateQ (zeroCoins + notImpl).batch' ((threeAdv.truncate 1 false).online () ()) = false := by
  simp only [TimeLockPuzzle.Adversary.truncate, threeAdv, threeRounds,
    truncate_succ_query_bind_inr, truncate_zero_query_bind_inr]
  rfl

/-! ## The three-round adversary within three rounds -/

/-- Within three rounds the adversary is its own truncation. -/
example (k₀ : Bool) : threeAdv.truncate 3 k₀ = threeAdv :=
  TimeLockPuzzle.Adversary.truncate_eq_self threeAdv_isQueryBound k₀

/-- Within three rounds its per-run event is its delay advantage. -/
example : TimeLockPuzzle.delayAdvantageWithin toy threeAdv 3 =
    TimeLockPuzzle.delayAdvantage toy threeAdv :=
  TimeLockPuzzle.delayAdvantageWithin_eq_delayAdvantage toy threeAdv_isQueryBound

end VCVioTest.TimeLockPuzzle.Truncate
