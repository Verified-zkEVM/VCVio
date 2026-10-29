/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle.Truncate

/-!
# Rounds beside a free summand holding more than local coins

Checks, through ordinary imports, that the round model charges only the batch summand when the
other summand holds local coins together with a challenge oracle `Bool →ₒ Bool`, as the online
phase of a hiding game does. A program that queries the challenge oracle around one round of one
point has online budget `(1, 1)`, and no smaller one; its challenge queries cost nothing, before
and after `unbatch`; a handler answering the challenge oracle by a local coin keeps the budget;
a two-phase adversary whose online phase is that program, with output `Bool`, has its budget; and
its truncation behaves as the truncation of a delay adversary does. The delay adversary is the
two-phase adversary on local coins, and is built and read with the structure's own syntax.
-/

public section

namespace VCVioTest.TimeLockPuzzle.FreeSummand

open OracleComp OracleSpec

/-- One oracle on `Bool`, asked in rounds. -/
abbrev boolSpec : OracleSpec Bool := fun _ => Bool

/-- The free summand: local coins and a challenge oracle on `Bool`. -/
abbrev freeSpec : OracleSpec (ℕ ⊕ Bool) := unifSpec + (Bool →ₒ Bool)

/-- A challenge query, one round holding its answer, and a challenge query on the round's
answer, whose negation is the output. -/
def prog : OracleComp (freeSpec + boolSpec.batch) Bool := do
  let c ← liftM ((freeSpec + boolSpec.batch).query (.inl (.inr true)))
  let us ← liftM ((freeSpec + boolSpec.batch).query (.inr [c]))
  let d ← liftM ((freeSpec + boolSpec.batch).query (.inl (.inr (us ⟨0, Nat.zero_lt_one⟩))))
  pure !d

/-- A deterministic handler for local coins, always answering `0`. -/
def zeroCoins : QueryImpl unifSpec Id := fun _ => (0 : Fin _)

/-- A deterministic challenge oracle returning its query. -/
def echoImpl : QueryImpl (Bool →ₒ Bool) Id := fun b => b

/-- A deterministic handler negating its point. -/
def notImpl : QueryImpl boolSpec Id := fun b => !b

/-! ## Budgets: challenge queries are free -/

/-- The program costs one round of one point; its two challenge queries cost nothing. -/
theorem prog_isOnlineQueryBound : IsOnlineQueryBound prog (1, 1) := by
  simp [prog]

/-- It still costs its round. -/
example : ¬ IsOnlineQueryBound prog (0, 1) := by
  simp [prog]

/-- And its point. -/
example : ¬ IsOnlineQueryBound prog (1, 0) := by
  simp [prog]

/-- Challenge queries alone cost neither rounds nor points. -/
example : IsOnlineQueryBound (do
    let c ← liftM ((freeSpec + boolSpec.batch).query (.inl (.inr true)))
    liftM ((freeSpec + boolSpec.batch).query (.inl (.inr c))) :
      OracleComp (freeSpec + boolSpec.batch) Bool) (0, 0) := by
  simp

/-- The point budget alone. -/
example : IsPointQueryBound prog 1 :=
  prog_isOnlineQueryBound.isPointQueryBound

/-- Local coins, lifted past the challenge oracle into the online phase, submit no rounds. -/
example (oa : ProbComp Bool) :
    IsOnlineQueryBound (liftComp oa (freeSpec + boolSpec.batch)) (0, 0) :=
  isOnlineQueryBound_liftComp oa (0, 0)

/-- A program on the challenge oracle alone, lifted into the online phase, submits no rounds. -/
example (oa : OracleComp (Bool →ₒ Bool) Bool) :
    IsOnlineQueryBound (liftComp oa (freeSpec + boolSpec.batch)) (0, 0) :=
  isOnlineQueryBound_liftComp oa (0, 0)

/-! ## Rewriting the round as single queries -/

/-- `unbatch` keeps a challenge query as it is. -/
example (b : Bool) :
    simulateQ boolSpec.unbatch
        (liftM ((freeSpec + boolSpec.batch).query (.inl (.inr b))) :
          OracleComp (freeSpec + boolSpec.batch) Bool) =
      (liftM ((freeSpec + boolSpec).query (.inl (.inr b))) :
        OracleComp (freeSpec + boolSpec) Bool) := by
  simp

/-- Unbatched, the program makes one query to `boolSpec`; its challenge queries are free. -/
example : IsQueryBoundP (simulateQ boolSpec.unbatch prog) (·.isRight) 1 :=
  prog_isOnlineQueryBound.isQueryBoundP_simulateQ_unbatch

/-- No query to `boolSpec` is not enough. -/
example : ¬ IsQueryBoundP (simulateQ boolSpec.unbatch prog) (·.isRight) 0 := by
  simp [prog, isQueryBoundP_query_bind_iff]

/-- The batched handler: the challenge echoes `true`, the round negates it, the challenge echoes
`false`, and the output is its negation. -/
example : simulateQ ((zeroCoins + echoImpl) + notImpl).batch' prog = true := rfl

/-- Unbatching first and running the single queries gives the same result. -/
example : simulateQ ((zeroCoins + echoImpl) + notImpl) (simulateQ boolSpec.unbatch prog) =
    true := by
  rw [QueryImpl.simulateQ_simulateQ_unbatch]
  rfl

/-- The run completes one round. -/
example : runCountingRounds ((zeroCoins + echoImpl) + notImpl).batch' prog = (true, 1) := by
  simp only [prog, runCountingRounds_query_bind, runCountingRounds_pure]
  rfl

/-! ## Changing the free summand -/

/-- Answer the challenge oracle by a local coin, and pass local coins and rounds through. -/
def coinChallenger :
    QueryImpl (freeSpec + boolSpec.batch) (OracleComp (unifSpec + boolSpec.batch))
  | .inl (.inl n) => liftM ((unifSpec + boolSpec.batch).query (.inl n))
  | .inl (.inr _) =>
      (fun i : Fin 2 => decide (i = 1)) <$> liftM ((unifSpec + boolSpec.batch).query (.inl 1))
  | .inr ts => liftM ((unifSpec + boolSpec.batch).query (.inr ts))

/-- The handler sends each free query to a program without rounds and each round to itself, so
the program run through it, now on local coins only, keeps the budget `(1, 1)`. -/
example : IsOnlineQueryBound (simulateQ coinChallenger prog) (1, 1) :=
  prog_isOnlineQueryBound.simulateQ_of_step fun t => by
    rcases t with (n | b) | ts <;> simp [coinChallenger]

/-! ## A two-phase adversary with a challenge oracle -/

/-- The adversary with no preprocessing whose online phase is `prog`: its free oracles include the
challenge oracle and its output is a bit. -/
def hideAdv : TimeLockPuzzle.TwoPhaseAdversary freeSpec boolSpec Unit Bool where
  State := Unit
  preprocess := pure ()
  online _ _ := prog

theorem hideAdv_isQueryBound : hideAdv.IsQueryBound 0 (1, 1) :=
  ⟨by simp [hideAdv], fun _ _ => prog_isOnlineQueryBound⟩

/-- Truncated at zero rounds, it fits no round and one point. -/
example (k₀ : Bool) : (hideAdv.truncate 0 k₀).IsQueryBound 0 (0, 1) :=
  TimeLockPuzzle.TwoPhaseAdversary.isQueryBound_truncate hideAdv_isQueryBound.1
    (fun σ puzzle => (hideAdv_isQueryBound.2 σ puzzle).isPointQueryBound) 0 k₀

/-- Its online phase keeps the first challenge query, which costs no round, and returns the
fallback where the round would be submitted. -/
example (k₀ : Bool) :
    (hideAdv.truncate 0 k₀).online () () = (do
      let _ ← liftM ((freeSpec + boolSpec.batch).query (.inl (.inr true)))
      pure k₀) := by
  simp only [TimeLockPuzzle.TwoPhaseAdversary.truncate, hideAdv, prog,
    truncate_query_bind_inl, truncate_zero_query_bind_inr]

/-- Under the deterministic handlers the truncation returns the fallback `false` instead of
`true`. -/
example : simulateQ ((zeroCoins + echoImpl) + notImpl).batch'
    ((hideAdv.truncate 0 false).online () ()) = false := by
  simp only [TimeLockPuzzle.TwoPhaseAdversary.truncate, hideAdv, prog,
    truncate_query_bind_inl, truncate_zero_query_bind_inr]
  rfl

/-- Within one round the adversary is its own truncation. -/
example (k₀ : Bool) : hideAdv.truncate 1 k₀ = hideAdv :=
  TimeLockPuzzle.TwoPhaseAdversary.truncate_eq_self hideAdv_isQueryBound k₀

/-! ## The delay adversary is the case on local coins -/

example : TimeLockPuzzle.Adversary boolSpec Unit Bool =
    TimeLockPuzzle.TwoPhaseAdversary unifSpec boolSpec Unit Bool := rfl

/-- The anonymous constructor builds a delay adversary. -/
def constAdv : TimeLockPuzzle.Adversary boolSpec Unit Bool := ⟨Unit, pure (), fun _ _ => pure true⟩

/-- Its fields and budget are read as for any two-phase adversary. -/
example : constAdv.IsQueryBound 0 (0, 0) :=
  ⟨by simp [constAdv], fun _ _ => by simp [constAdv]⟩

example : constAdv.online () () = pure true := rfl

end VCVioTest.TimeLockPuzzle.FreeSummand
