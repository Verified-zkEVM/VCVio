/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle.LogSide

/-!
# Logging the side points of a two-phase adversary: checks

A toy sum of a puzzle oracle `ℕ →ₒ Fin 256` and a side oracle `ℕ →ₒ Fin 8`, and an adversary
whose preprocessing phase queries the side point `5` and whose online phase submits the single
mixed round `[.inl 3, .inr 5, .inl 3, .inr 6, .inr 5]`. Run deterministically, the instrumented
adversary logs `[5]` in preprocessing and `[5, 5, 6, 5]` in all: the repeated side point is kept
each time, and the order of the queries is kept across both phases. The instrumented adversary has
exactly the budgets of the adversary, one preprocessing query and one round of five points.
Against a toy puzzle lifted to the sum, forgetting the log gives back the delay experiment against
the adversary, the log holds at most six points, and in the random oracle model the cached side
points are the logged ones.
-/

public section

open OracleComp OracleSpec TimeLockPuzzle

namespace VCVioTest.TimeLockPuzzle.LogSide

/-- The puzzle oracle. -/
abbrev puzSpec : OracleSpec ℕ := ℕ →ₒ Fin 256

/-- The side oracle. -/
abbrev sideSpec : OracleSpec ℕ := ℕ →ₒ Fin 8

/-- The mixed round: the puzzle point `3` twice, and the side points `5`, `6`, `5`. -/
abbrev mixed : List (ℕ ⊕ ℕ) := [.inl 3, .inr 5, .inl 3, .inr 6, .inr 5]

/-! ## The adversary and its log -/

/-- Preprocessing queries the side point `5`; the online phase submits the mixed round. -/
@[expose]
def srcAdv : TwoPhaseAdversary unifSpec (puzSpec + sideSpec) Unit Unit where
  State := Unit
  preprocess := (fun _ => ()) <$>
    liftM ((unifSpec + (puzSpec + sideSpec)).query (.inr (.inr 5)))
  online _ _ := (fun _ => ()) <$>
    liftM ((unifSpec + (puzSpec + sideSpec).batch).query (.inr mixed))

/-- The answer `0` at every point of the sum. -/
def zeroAnswer : (t : ℕ ⊕ ℕ) → (puzSpec + sideSpec).Range t
  | .inl _ => (0 : Fin 256)
  | .inr _ => (0 : Fin 8)

/-- The preprocessing oracles, answering `0` everywhere. -/
def preImpl : QueryImpl (unifSpec + (puzSpec + sideSpec)) Id
  | .inl n => pure (0 : Fin (n + 1))
  | .inr t => pure (zeroAnswer t)

/-- The online oracles, answering `0` everywhere. -/
def onImpl : QueryImpl (unifSpec + (puzSpec + sideSpec).batch) Id
  | .inl n => pure (0 : Fin (n + 1))
  | .inr ts => pure fun j => zeroAnswer ts[j]

/-- The log of the instrumented adversary after its preprocessing phase. -/
def preLog : List ℕ :=
  ((simulateQ preImpl srcAdv.logSide.preprocess).run).2

/-- The log of the instrumented adversary after both phases. -/
def fullLog : List ℕ :=
  let σ := (simulateQ preImpl srcAdv.logSide.preprocess).run
  ((simulateQ onImpl (srcAdv.logSide.online σ ())).run).2

/-- Preprocessing logs its side point. -/
theorem preLog_eq : preLog = [5] := by
  decide

/-- Both phases log `[5, 5, 6, 5]`: the side point `5` of preprocessing, then the side points of
the mixed round in its order, the repeated point `5` kept. -/
theorem fullLog_eq : fullLog = [5, 5, 6, 5] := by
  decide

/-! ## Budgets -/

/-- The adversary makes one preprocessing query and submits one round of five points. -/
theorem srcAdv_isQueryBound : srcAdv.IsQueryBound 1 (1, 5) := by
  refine ⟨by simp [srcAdv], fun _ _ => ?_⟩
  simp [srcAdv, IsOnlineQueryBound]

/-- The instrumented adversary keeps the budget. -/
theorem logSide_srcAdv_isQueryBound : srcAdv.logSide.IsQueryBound 1 (1, 5) :=
  TwoPhaseAdversary.isQueryBound_logSide srcAdv_isQueryBound

/-- Its preprocessing query is still needed. -/
theorem not_isPreprocessingQueryBound_logSide_srcAdv :
    ¬ IsPreprocessingQueryBound srcAdv.logSide.preprocess 0 := by
  simp [TwoPhaseAdversary.logSide, srcAdv, sideLogPreImpl]

/-- Its five points are still needed. -/
theorem not_isOnlineQueryBound_logSide_srcAdv (σ : srcAdv.logSide.State) :
    ¬ IsOnlineQueryBound (srcAdv.logSide.online σ ()) (1, 4) := by
  simp [TwoPhaseAdversary.logSide, srcAdv, sideLogOnImpl, IsOnlineQueryBound]

/-! ## The delay experiment -/

/-- A toy puzzle over `puzSpec`: the key is the answer at the point `0`, found in one round. -/
def toyPuzzle : TimeLockPuzzle puzSpec Unit (Fin 256) where
  gen := (fun us => ((), us ⟨0, by simp⟩)) <$>
    liftM ((unifSpec + puzSpec.batch).query (.inr [0]))
  solve _ := (fun us => some (us ⟨0, by simp⟩)) <$>
    liftM ((unifSpec + puzSpec.batch).query (.inr [0]))

/-- Forgetting the log, the delay experiment of the lifted puzzle against the instrumented
adversary is the one against the adversary. -/
example : (fun z => (z.1.1, z.2)) <$>
      (toyPuzzle.liftSpec (puzSpec + sideSpec)).guessExperiment srcAdv.logSide =
    (toyPuzzle.liftSpec (puzSpec + sideSpec)).guessExperiment srcAdv :=
  map_guessExperiment_logSide _ _

/-- On every outcome, the log holds at most `1 + 5` points. -/
example {z : (Unit × List ℕ) × Fin 256}
    (hz : z ∈ support ((toyPuzzle.liftSpec (puzSpec + sideSpec)).guessExperiment srcAdv.logSide)) :
    z.1.2.length ≤ 6 :=
  length_le_of_mem_support_guessExperiment_logSide _ srcAdv_isQueryBound hz

/-- In the random oracle model from the empty cache, the side point `6` is cached at the end
exactly when it is logged. -/
example {z : ((Unit × List ℕ) × Fin 256) × (puzSpec + sideSpec).QueryCache}
    (hz : z ∈ support ((simulateQ (puzSpec + sideSpec).romImpl
      ((toyPuzzle.liftSpec (puzSpec + sideSpec)).guessExperiment srcAdv.logSide)).run ∅)) :
    (z.2 (.inr 6)).isSome ↔ 6 ∈ z.1.1.2 :=
  cache_inr_isSome_iff_mem_log _ _ hz 6

end VCVioTest.TimeLockPuzzle.LogSide
