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
round returns the fallback, a program within the bound is unchanged, and uniform queries do not
count as rounds.
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

/-- Under any handler, outputs of the chain within one round are outputs of its truncation. -/
example {m : Type → Type} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] (impl : QueryImpl (unifSpec + boolSpec.batch) m) (p : Bool → Prop) :
    Pr{let z ← runCountingRounds impl threeRounds}[z.2 ≤ 1 ∧ p z.1] ≤
      Pr{let x ← simulateQ impl (truncate 1 false threeRounds)}[p x] :=
  prEvent_runCountingRounds_le_truncate impl threeRounds p

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
