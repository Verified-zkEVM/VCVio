/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSealHidingBridge

/-!
# The adversary adapter for any free summand: checks

A toy encoding of the typed oracle `ℕ →ₒ Fin 8` into the raw oracle `ℕ →ₒ Fin 8`: the typed
point `t` at the raw input `2 * t`, odd raw inputs encoding no typed point. A raw adversary over the
hiding adversary's free summand, local coins and the left-or-right challenge oracle, queries the
odd input `5` in preprocessing; online, it asks the challenge `(3, 4)` and submits the raw round
`[2, 5, 2, 5]`.

Run deterministically, with local coins read off a counter, the adapted adversary forwards the
challenge once, submits exactly one typed round `[1, 1]`, with the repeated point kept, and
answers both occurrences of `5` with the value drawn in preprocessing. Its online budget is
`(1, 2)` where the raw adversary's is `(1, 4)`, and the encryption budget `1` carries over. The
coin lift into the free summand lands on the coin summand, so private draws are never challenge
queries.
-/

public section

open OracleComp OracleSpec TimeLockPuzzle

namespace VCVioTest.LeanSealHidingBridge

/-! ## The coin lift -/

/-- The coin lift into the hiding adversary's free summand lands on the coin summand. -/
example {Msg C : Type} (k : ℕ) :
    (liftM (unifSpec.query k) : OracleQuery (unifSpec + LeftOrRight.spec Msg C) (Fin (k + 1))) =
      (unifSpec + LeftOrRight.spec Msg C).query (.inl k) := rfl

/-! ## A toy encoding -/

/-- The typed oracle. -/
abbrev typSpec : OracleSpec ℕ := ℕ →ₒ Fin 8

/-- The raw oracle. -/
abbrev rawSpec : OracleSpec ℕ := ℕ →ₒ Fin 8

/-- The typed point `t` at the raw input `2 * t`; an odd raw input encodes no typed point. Typed
answers are whole raw values. -/
@[expose]
noncomputable def toyEnc : RandomOracleEncoding typSpec ℕ (Fin 8) :=
  .ofSplit (Tail := fun _ => Unit) (fun t => 2 * t)
    (fun x => if x % 2 = 0 then some (x / 2) else none)
    (by
      intro x t h
      split_ifs at h with hx
      cases h
      omega)
    (fun t => by simp) (fun _ => (Equiv.prodPUnit _).symm)

/-- The raw round: the encoding `2` of the typed point `1` twice, and the odd input `5` twice. -/
abbrev rawRound : List ℕ := [2, 5, 2, 5]

/-- Its inputs that encode typed points: the typed round `[1, 1]`. -/
example : rawRound.filterMap toyEnc.route = [1, 1] := by decide

/-! ## The raw adversary and its adaptation -/

/-- The free summand of hiding adversaries with messages and ciphertexts in `ℕ`. -/
abbrev freeSpec : OracleSpec (ℕ ⊕ ℕ × ℕ) := unifSpec + LeftOrRight.spec ℕ ℕ

/-- Preprocessing queries the odd input `5` and keeps its answer; online, the adversary asks the
challenge `(3, 4)`, submits the raw round, and returns the challenge answer with the kept answer
followed by the round's answers. -/
@[expose]
def srcAdv : TwoPhaseAdversary freeSpec rawSpec Unit (Option ℕ × List ℕ) where
  State := Fin 8
  preprocess := liftM ((unifSpec + rawSpec).query (.inr 5))
  online v _ := do
    let c ← (liftM ((freeSpec + rawSpec.batch).query (.inl (.inr (3, 4)))) :
      OracleComp (freeSpec + rawSpec.batch) (Option ℕ))
    let us ← liftM ((freeSpec + rawSpec.batch).query (.inr rawRound))
    pure (c, v.val :: List.ofFn fun j => (us j : Fin 8).val)

/-- Local coins read off a counter, which then moves on. -/
def counterCoins {σ : Type} (get : σ → ℕ) (set : ℕ → σ → σ) : QueryImpl unifSpec (StateT σ Id) :=
  fun n => StateT.mk fun s => pure (⟨get s % (n + 1), Nat.mod_lt _ n.succ_pos⟩, set (get s + 1) s)

/-- The typed oracle `t ↦ t + 5 mod 8`. -/
def typAnswer (t : ℕ) : Fin 8 := ⟨(t + 5) % 8, Nat.mod_lt _ (by decide)⟩

/-- The preprocessing oracles: coins from the counter, and the typed oracle. -/
def preImpl : QueryImpl (unifSpec + typSpec) (StateT ℕ Id) :=
  counterCoins id (fun k _ => k) +
    (fun t => pure (typAnswer t) : QueryImpl typSpec (StateT ℕ Id))

/-- The online state: the coin counter, the typed rounds and the challenges, latest first. -/
abbrev OnState := ℕ × List (List ℕ) × List (ℕ × ℕ)

/-- Challenges answered by `(m₀, m₁) ↦ 10 m₀ + m₁` and recorded in the log. -/
def challenges : QueryImpl (LeftOrRight.spec ℕ ℕ) (StateT OnState Id) :=
  fun mm => StateT.mk fun s => pure (some (10 * mm.1 + mm.2), (s.1, s.2.1, mm :: s.2.2))

/-- Typed rounds answered by the typed oracle and recorded in the log. -/
def typRounds : QueryImpl typSpec.batch (StateT OnState Id) :=
  fun ts => StateT.mk fun s =>
    pure ((fun j => typAnswer ts[j] : typSpec.batch.Range ts), (s.1, ts :: s.2.1, s.2.2))

/-- The online oracles: coins from the counter, challenges, and typed rounds. -/
def onImpl : QueryImpl (freeSpec + typSpec.batch) (StateT OnState Id) :=
  (counterCoins (σ := OnState) Prod.fst (fun k s => (k, s.2)) + challenges) + typRounds

/-- Run the adapted adversary from coin counter `3`: preprocessing, then the online phase on its
state; return the output, the typed rounds and the challenges, in order. -/
noncomputable def runAdapted : (Option ℕ × List ℕ) × List (List ℕ) × List (ℕ × ℕ) :=
  let adv := toyEnc.adaptTwoPhase srcAdv
  let (σ, k) := ((simulateQ preImpl adv.preprocess).run 3).run
  let (out, _, rounds, chals) := ((simulateQ onImpl (adv.online σ ())).run (k, [], [])).run
  (out, rounds.reverse, chals.reverse)

/-- The challenge is forwarded once and answered `34`. One typed round `[1, 1]` is submitted, with
the repeated point kept, and both occurrences of `2` get the typed answer `6` there. Preprocessing
draws `3` at the odd input `5`, and both occurrences of `5` get `3` from the private cache. -/
theorem runAdapted_eq : runAdapted = ((some 34, [3, 6, 3, 6, 3]), [[1, 1]], [(3, 4)]) := by
  decide

/-! ## Budgets -/

/-- The raw adversary makes one preprocessing query and submits one round of four inputs. -/
theorem srcAdv_isQueryBound : srcAdv.IsQueryBound 1 (1, 4) := by
  refine ⟨by simp [srcAdv], fun v _ => ?_⟩
  simp [srcAdv, IsOnlineQueryBound]

/-- The adapter keeps the budget. -/
example : (toyEnc.adaptTwoPhase srcAdv).IsQueryBound 1 (1, 4) :=
  toyEnc.isQueryBound_adaptTwoPhase srcAdv_isQueryBound

/-- The typed round holds only the two typed points: the online budget is `(1, 2)`. -/
theorem adaptTwoPhase_srcAdv_isQueryBound :
    (toyEnc.adaptTwoPhase srcAdv).IsQueryBound 1 (1, 2) := by
  refine ⟨(toyEnc.isQueryBound_adaptTwoPhase srcAdv_isQueryBound).1, fun σ _ => ?_⟩
  simp only [RandomOracleEncoding.adaptTwoPhase, srcAdv, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind]
  refine isOnlineQueryBound_bind_le (0, 0) (1, 2) ?_ (fun z => ?_) ⟨by omega, by omega⟩
  · exact (toyEnc.isOnlineQueryBound_freeOnlineImpl _ _).mono le_rfl
  · refine isOnlineQueryBound_bind_le (1, 2) (0, 0) ?_ (fun _ => ?_) ⟨le_rfl, le_rfl⟩
    · exact toyEnc.isOnlineQueryBound_freeOnlineImpl_inr_run rawRound z.2
    · simp [IsOnlineQueryBound]

/-- The hiding adversary of `srcAdv`: it guesses `true` when its challenge is answered. -/
@[expose]
def hideAdv : HidingAdversary rawSpec Unit ℕ ℕ := srcAdv.mapOutput fun out => out.1.isSome

/-- It makes one challenge query. -/
theorem hideAdv_makesAtMostQueries : hideAdv.MakesAtMostQueries 1 := by
  intro v _
  simp [hideAdv, TwoPhaseAdversary.mapOutput, srcAdv]

/-- The hiding adapter keeps the encryption budget. -/
example : (toyEnc.adaptHidingAdversary hideAdv).MakesAtMostQueries 1 :=
  toyEnc.makesAtMostQueries_adaptHidingAdversary hideAdv_makesAtMostQueries

end VCVioTest.LeanSealHidingBridge
