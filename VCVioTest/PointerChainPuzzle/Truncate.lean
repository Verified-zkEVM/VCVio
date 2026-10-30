/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Truncate

/-!
# Truncating a program at a round bound

Checks of `OracleComp.truncate` on small concrete programs: a three-round chain cut after one
round returns the fallback; a fair coin choosing between one and three rounds returns `true`
within one round with probability `1 / 2`, and so does its truncation after one round; a program
within the bound is unchanged; and uniform queries do not count as rounds.
-/

public section

namespace VCVioTest.PointerChainPuzzle.Truncate

open OracleComp OracleSpec

/-- One oracle on `Bool`. -/
abbrev boolSpec : OracleSpec Bool := fun _ => Bool

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

theorem threeRounds_isOnlineQueryBound : IsOnlineQueryBound threeRounds (3, 3) := by
  simp [threeRounds]

/-! ## Cutting off a longer program -/

/-- Cut after one round, the chain submits that round and returns the fallback. -/
example (k₀ : Bool) :
    truncate 1 k₀ threeRounds = (do
      let _ ← liftM ((unifSpec + boolSpec.batch).query (.inr [false]))
      pure k₀) := by
  simp only [threeRounds, truncate_succ_query_bind_inr, truncate_zero_query_bind_inr]

/-- The full chain returns `true` under the negating handler. -/
example : simulateQ (zeroCoins + notImpl).batch' threeRounds = true := rfl

/-- Its truncation after one round returns the fallback `false` instead. -/
example : simulateQ (zeroCoins + notImpl).batch' (truncate 1 false threeRounds) = false := by
  simp only [threeRounds, truncate_succ_query_bind_inr, truncate_zero_query_bind_inr]
  rfl

/-- The truncation fits one round, with the point budget of the chain. -/
example (k₀ : Bool) : IsOnlineQueryBound (truncate 1 k₀ threeRounds) (1, 3) :=
  threeRounds_isOnlineQueryBound.isPointQueryBound.isOnlineQueryBound_truncate

/-- Counting rounds along the run: the chain outputs `true` after three completed rounds. -/
example : runCountingRounds (zeroCoins + notImpl).batch' threeRounds = (true, 3) := by
  simp only [threeRounds, runCountingRounds_query_bind, runCountingRounds_pure]
  rfl

/-! ## Probability kept by the truncation -/

/-- Uniform local coins, and rounds answered by negating every point. -/
def coinImpl : QueryImpl (unifSpec + boolSpec.batch) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    fun ts => (pure (notImpl.batch ts).run : ProbComp (boolSpec.batch.Range ts))

/-- A single round, returning `true`. -/
def oneRound : OracleComp (unifSpec + boolSpec.batch) Bool := do
  let _ ← liftM ((unifSpec + boolSpec.batch).query (.inr [false]))
  pure true

/-- A fair coin choosing between one round and the three-round chain; both return `true`. -/
def coinRounds : OracleComp (unifSpec + boolSpec.batch) Bool := do
  let b ← liftM ((unifSpec + boolSpec.batch).query (.inl 1))
  if b.val = 0 then oneRound else threeRounds

/-- Cut after one round, the coin keeps the one-round branch and cuts the three-round branch. -/
lemma truncate_coinRounds :
    truncate 1 false coinRounds = (do
      let b ← liftM ((unifSpec + boolSpec.batch).query (.inl 1))
      if b.val = 0 then oneRound else do
        let _ ← liftM ((unifSpec + boolSpec.batch).query (.inr [false]))
        pure false) := by
  simp only [coinRounds, truncate_query_bind_inl, apply_ite (truncate 1 false), oneRound,
    threeRounds, truncate_succ_query_bind_inr, truncate_zero_query_bind_inr, truncate_pure]

/-- The program returns `true` within one completed round with probability `1 / 2`. -/
example : Pr{let z ← runCountingRounds coinImpl coinRounds}[z.2 ≤ 1 ∧ z.1 = true] = 1 / 2 := by
  simp only [coinRounds, oneRound, threeRounds, runCountingRounds_query_bind,
    apply_ite (runCountingRounds coinImpl), runCountingRounds_pure]
  simp [coinImpl, notImpl, ← apply_ite (pure : Bool × ℕ → ProbComp (Bool × ℕ)),
    apply_ite Prod.fst, apply_ite Prod.snd, apply_ite (· ≤ 1), and_iff_left_of_imp Or.inl,
    prEvent_liftM_query_eq_card_div, Finset.filter_eq']

/-- Its truncation after one round returns `true` with probability `1 / 2`. -/
example : Pr{let x ← simulateQ coinImpl (truncate 1 false coinRounds)}[x = true] = 1 / 2 := by
  simp [truncate_coinRounds, oneRound, coinImpl, ← apply_ite (pure : Bool → ProbComp Bool),
    prEvent_liftM_query_eq_card_div, Finset.filter_eq']

/-! ## Programs within the bound -/

/-- A program within three rounds is its own truncation at three rounds. -/
example (k₀ : Bool) : truncate 3 k₀ threeRounds = threeRounds :=
  truncate_eq_self_of_isOnlineQueryBound threeRounds_isOnlineQueryBound

/-- Hence it has the same distribution under every handler. -/
example {m : Type → Type} [Monad m] [EvalDistSemantics m]
    (impl : QueryImpl (unifSpec + boolSpec.batch) m) (k₀ : Bool) :
    𝒟[simulateQ impl (truncate 3 k₀ threeRounds)] = 𝒟[simulateQ impl threeRounds] := by
  rw [truncate_eq_self_of_isOnlineQueryBound threeRounds_isOnlineQueryBound]

/-- Under the negating handler, the truncation after three rounds still returns `true`. -/
example : simulateQ (zeroCoins + notImpl).batch' (truncate 3 false threeRounds) = true := by
  rw [truncate_eq_self_of_isOnlineQueryBound threeRounds_isOnlineQueryBound]
  rfl

/-! ## Uniform queries are not rounds -/

/-- Local coins around a single round. -/
def coinsAroundRound : OracleComp (unifSpec + boolSpec.batch) Bool := do
  let _ ← liftM ((unifSpec + boolSpec.batch).query (.inl 5))
  let us ← liftM ((unifSpec + boolSpec.batch).query (.inr [true]))
  let _ ← liftM ((unifSpec + boolSpec.batch).query (.inl 1))
  pure (us ⟨0, by decide⟩)

/-- With one round allowed, the coins on both sides of the round are kept. -/
example (k₀ : Bool) : truncate 1 k₀ coinsAroundRound = coinsAroundRound :=
  truncate_eq_self_of_isOnlineQueryBound (q := 1) (by simp [coinsAroundRound])

/-- Counting rounds along the run: the coins add nothing to the count. -/
example : (runCountingRounds (zeroCoins + notImpl).batch' coinsAroundRound).2 = 1 := by
  simp only [coinsAroundRound, runCountingRounds_query_bind, runCountingRounds_pure]
  rfl

/-- With no round allowed, the coins before the round are kept and the round is cut. -/
example (k₀ : Bool) :
    truncate 0 k₀ coinsAroundRound = (do
      let _ ← liftM ((unifSpec + boolSpec.batch).query (.inl 5))
      pure k₀) := by
  simp only [coinsAroundRound, truncate_query_bind_inl, truncate_zero_query_bind_inr]

/-- A program of uniform queries alone is unchanged even with no round allowed. -/
example (k₀ : Fin 4) :
    truncate (spec := boolSpec) 0 k₀ (liftM ((unifSpec + boolSpec.batch).query (.inl 3))) =
      liftM ((unifSpec + boolSpec.batch).query (.inl 3)) :=
  truncate_eq_self_of_isOnlineQueryBound (q := 0) (by simp)

end VCVioTest.PointerChainPuzzle.Truncate
