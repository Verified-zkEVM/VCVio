/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle.Lift

/-!
# Lifting a time-lock puzzle and simulating a side oracle: checks

A toy sum of a puzzle oracle `ℕ →ₒ ℕ` and a side oracle `ℕ →ₒ Fin 8`, and an adversary whose
preprocessing phase queries the side point `5` and whose online phase submits the single mixed
round `[.inl 3, .inr 5, .inl 3, .inr 6, .inr 5]`. Run deterministically, with local coins read off
a counter so that every fresh side draw gets a new value, its simulation submits exactly one round,
`[3, 3]`, with the repeated point kept, reassembles the answer tuple in the round's order, and
answers both occurrences of `5` with the value drawn in preprocessing. The online budget `(1, 5)`
of the adversary becomes `(1, 2)` for the simulation. A toy puzzle lifted to the sum submits the
translated round and keeps its honest budget.
-/

public section

open OracleComp OracleSpec TimeLockPuzzle

namespace VCVioTest.TimeLockPuzzle.Lift

/-- The puzzle oracle. -/
abbrev puzSpec : OracleSpec ℕ := ℕ →ₒ ℕ

/-- The side oracle, with answers that can be sampled. -/
abbrev sideSpec : OracleSpec ℕ := ℕ →ₒ Fin 8

/-- The mixed round: the puzzle point `3` twice, and the side points `5`, `6`, `5`. -/
abbrev mixed : List (ℕ ⊕ ℕ) := [.inl 3, .inr 5, .inl 3, .inr 6, .inr 5]

/-- The answers to a round of the sum, read as natural numbers in the round's order. -/
def toList : (ts : List (ℕ ⊕ ℕ)) → (puzSpec + sideSpec).batch.Range ts → List ℕ
  | [], _ => []
  | .inl _ :: ts, us => (us ⟨0, by simp⟩ : ℕ) :: toList ts fun j => us j.succ
  | .inr _ :: ts, us => (us ⟨0, by simp⟩ : Fin 8).val :: toList ts fun j => us j.succ

/-! ## Reassembling a mixed round -/

/-- The puzzle answers go to the puzzle positions and the side answers to the side positions, each
in order. -/
theorem toList_batchMerge_mixed :
    toList mixed (batchMerge (spec := puzSpec) (side := sideSpec) mixed
      (fun j => [103, 203][j]) (fun j => [7, 4, 1][j])) = [103, 7, 203, 4, 1] := by
  decide

/-! ## The adversary and its simulation -/

/-- Preprocessing queries the side point `5` and keeps its answer; the online phase submits the
mixed round and returns the kept answer with the round's answers. -/
@[expose]
def srcAdv : TwoPhaseAdversary unifSpec (puzSpec + sideSpec) Unit (ℕ × List ℕ) where
  State := Fin 8
  preprocess := liftM ((unifSpec + (puzSpec + sideSpec)).query (.inr (.inr 5)))
  online v _ := (fun us => (v.val, toList mixed us)) <$>
    liftM ((unifSpec + (puzSpec + sideSpec).batch).query (.inr mixed))

/-- Local coins read off a counter, which then moves on. -/
def counterCoins {σ : Type} (get : σ → ℕ) (set : ℕ → σ → σ) : QueryImpl unifSpec (StateT σ Id) :=
  fun n => StateT.mk fun s => pure (⟨get s % (n + 1), Nat.mod_lt _ n.succ_pos⟩, set (get s + 1) s)

/-- The puzzle oracle `t ↦ t + 100`, one point at a time. -/
def puzPoint : QueryImpl puzSpec (StateT ℕ Id) := fun t => pure (t + 100)

/-- The preprocessing oracles: coins from the counter, and the puzzle oracle `t ↦ t + 100`. -/
def preImpl : QueryImpl (unifSpec + puzSpec) (StateT ℕ Id) :=
  counterCoins id (fun k _ => k) + puzPoint

/-- Rounds of the puzzle oracle answered by `t ↦ t + 100` and recorded in a log. -/
def puzRounds : QueryImpl puzSpec.batch (StateT (ℕ × List (List ℕ)) Id) :=
  fun ts => StateT.mk fun s =>
    pure ((fun j => ts[j] + 100 : puzSpec.batch.Range ts), (s.1, ts :: s.2))

/-- The online oracles: coins from the counter, and rounds answered by `t ↦ t + 100` and recorded
in a log. -/
def onImpl : QueryImpl (unifSpec + puzSpec.batch) (StateT (ℕ × List (List ℕ)) Id) :=
  counterCoins (σ := ℕ × List (List ℕ)) Prod.fst (fun k s => (k, s.2)) + puzRounds

/-- Run the simulation from coin counter `3`: preprocessing, then the online phase on its state;
return the output and the rounds submitted, in order. -/
def runSimulation : (ℕ × List ℕ) × List (List ℕ) :=
  let adv := srcAdv.simulateSide
  let (σ, k) := ((simulateQ preImpl adv.preprocess).run 3).run
  let (out, _, rounds) := ((simulateQ onImpl (adv.online σ ())).run (k, [])).run
  (out, rounds.reverse)

/-- One round `[3, 3]` is submitted, with the repeated point kept. Preprocessing draws `3` at the
side point `5`; online, the fresh side point `6` draws the next coin, `4`, and both occurrences of
`5` get `3` from the private cache. The answer tuple is in the order of the mixed round. -/
theorem runSimulation_eq : runSimulation = ((3, [103, 3, 103, 4, 3]), [[3, 3]]) := by
  decide

/-! ## Budgets -/

/-- The adversary makes one preprocessing query and submits one round of five points. -/
theorem srcAdv_isQueryBound : srcAdv.IsQueryBound 1 (1, 5) := by
  refine ⟨by simp [srcAdv], fun v _ => ?_⟩
  simp [srcAdv, IsOnlineQueryBound]

/-- Its five points are needed. -/
example (v : Fin 8) : ¬ IsOnlineQueryBound (srcAdv.online v ()) (1, 4) := by
  simp [srcAdv, IsOnlineQueryBound]

/-- The simulation keeps the budget. -/
example : srcAdv.simulateSide.IsQueryBound 1 (1, 5) :=
  TwoPhaseAdversary.isQueryBound_simulateSide srcAdv_isQueryBound

/-- Its round holds only the two puzzle points: the online budget is `(1, 2)`. -/
theorem simulateSide_srcAdv_isQueryBound : srcAdv.simulateSide.IsQueryBound 1 (1, 2) := by
  refine ⟨(TwoPhaseAdversary.isQueryBound_simulateSide srcAdv_isQueryBound).1, fun σ _ => ?_⟩
  simp only [TwoPhaseAdversary.simulateSide, srcAdv, simulateQ_map, simulateQ_spec_query,
    StateT.run'_eq, StateT.run_map, IsOnlineQueryBound, isQueryBound_map_iff]
  exact isOnlineQueryBound_sideOnlineImpl_inr_run mixed σ.2

/-! ## Lifting a puzzle -/

/-- A toy puzzle over `puzSpec`: the key is the answer at the point `0`, found in one round. -/
def toyPuzzle : TimeLockPuzzle puzSpec Unit ℕ where
  gen := (fun us => ((), us ⟨0, by simp⟩)) <$>
    liftM ((unifSpec + puzSpec.batch).query (.inr [0]))
  solve _ := (fun us => some (us ⟨0, by simp⟩)) <$>
    liftM ((unifSpec + puzSpec.batch).query (.inr [0]))

/-- The toy generator submits one round of one point. -/
theorem toyPuzzle_isGenQueryBound : toyPuzzle.IsGenQueryBound (1, 1) := by
  simp [toyPuzzle, IsGenQueryBound, IsOnlineQueryBound]

/-- Lifted to the sum, it keeps the budget. -/
example : (toyPuzzle.liftSpec (puzSpec + sideSpec)).IsGenQueryBound (1, 1) :=
  toyPuzzle_isGenQueryBound.liftSpec

/-- An answer at a point of the sum: `t + 100` at a puzzle point, `0` at a side point. -/
def sumAnswer : (t : ℕ ⊕ ℕ) → (puzSpec + sideSpec).Range t
  | .inl t => t + 100
  | .inr _ => (0 : Fin 8)

/-- Rounds of the sum answered by `sumAnswer` and recorded in a log. -/
def sumRounds : QueryImpl (puzSpec + sideSpec).batch (StateT (List (List (ℕ ⊕ ℕ))) Id) :=
  fun ts => StateT.mk fun log =>
    pure ((fun j => sumAnswer ts[j] : (puzSpec + sideSpec).batch.Range ts), ts :: log)

/-- Rounds of the sum recorded in a log; coins are never asked. -/
def sumImpl : QueryImpl (unifSpec + (puzSpec + sideSpec).batch)
    (StateT (List (List (ℕ ⊕ ℕ))) Id) :=
  counterCoins (σ := List (List (ℕ ⊕ ℕ))) (fun _ => 0) (fun _ log => log) + sumRounds

/-- Lifted to the sum, the generator submits the single round `[.inl 0]` and returns the answer
there as the key. -/
theorem run_simulateQ_liftSpec_gen :
    ((simulateQ sumImpl (toyPuzzle.liftSpec (puzSpec + sideSpec)).gen).run []).run =
      (((), 100), [[.inl 0]]) := by
  decide

end VCVioTest.TimeLockPuzzle.Lift
