/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle.Hiding

/-!
# The capped challenger of the hiding game

Checks, through ordinary imports, the capped left-or-right oracle, the challenge-cap adapter and
the capped hiding game on toy examples.

* **The capped oracle.** Four requests on lists of bits with the length as leakage, against a cap
  of two: the first is encrypted, the second has unequal leakage and is answered `none` without
  moving the counter, the third is encrypted, and the fourth, with equal leakage, finds the cap
  exhausted and is answered `none`. With the cap `0` every request is answered `none`.
* **The adapter.** The same four requests run through `HidingAdversary.capChallengesImpl`: only
  the accepted ones are forwarded to the challenge oracle, and the others are answered locally.
  With the cap `0` nothing is forwarded.
* **The capped game.** Against the revealing puzzle and the one-bit pad, an adversary that makes
  two challenge requests, and so is not within the encryption budget `1`, wins the capped game
  with cap `1` with advantage `1`; with cap `0` its advantage is `0`, by the bridge to the
  uncapped game and the zero-query lemma.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory TimeLockPuzzle

namespace VCVioTest.TimeLockPuzzle.HidingCap

/-! ## The capped oracle -/

/-- Encryption of lists of bits by flipping every bit. -/
def flipEnc (msg : List Bool) : Id (List Bool) := pure (msg.map (!·))

/-- The challenge requests of the traces: the second pair has unequal lengths, and the fourth has
equal lengths. -/
def requests {m : Type → Type} [Monad m]
    (challenge : List Bool × List Bool → m (Option (List Bool))) :
    m (List (Option (List Bool))) := do
  let c₁ ← challenge ([true], [false])
  let c₂ ← challenge ([], [true])
  let c₃ ← challenge ([false, false], [true, true])
  let c₄ ← challenge ([true], [true])
  pure [c₁, c₂, c₃, c₄]

/-- A pair with unequal leakage is answered `none`, and the counter stays at `0`. -/
example (b : Bool) :
    (LeftOrRight.cappedOracle flipEnc List.length 2 b ([], [true])).run 0 = pure (none, 0) :=
  LeftOrRight.run_cap_apply_of_leak_ne _ _ _ _ (by simp)

/-- With the cap `0` every request is answered `none`. -/
example (b : Bool) (mm : List Bool × List Bool) (j : ℕ) :
    (LeftOrRight.cappedOracle flipEnc List.length 0 b mm).run j = pure (none, j) :=
  LeftOrRight.run_cap_apply_of_le _ _ _ _ (Nat.zero_le j)

/-- Against the cap `2` at hidden bit `true`: the first and third requests are encrypted, the
second (unequal lengths) and the fourth (cap exhausted) are answered `none`, and the counter ends
at `2`. -/
example : (requests (LeftOrRight.cappedOracle flipEnc List.length 2 true)).run 0 =
    pure ([some [true], none, some [false, false], none], 2) := by
  simp [requests, LeftOrRight.run_cappedOracle_apply, flipEnc]

/-- Against the cap `0` every request is answered `none` and the counter stays at `0`. -/
example (b : Bool) : (requests (LeftOrRight.cappedOracle flipEnc List.length 0 b)).run 0 =
    pure ([none, none, none, none], 0) := by
  simp [requests, LeftOrRight.run_cappedOracle_apply]

/-! ## The adapter -/

/-- One random bit: the oracle `H : Unit → Bool`. -/
abbrev keySpec : OracleSpec Unit := Unit →ₒ Bool

/-- The oracles of a hiding adversary on lists of bits: local coins, the challenge oracle, and
rounds to `H`. -/
abbrev advSpec : OracleSpec ((ℕ ⊕ (List Bool × List Bool)) ⊕ List Unit) :=
  (unifSpec + LeftOrRight.spec (List Bool) (List Bool)) + keySpec.batch

/-- A challenge request of the adversary. -/
def challenge (mm : List Bool × List Bool) : OracleComp advSpec (Option (List Bool)) :=
  liftM (advSpec.query (.inl (.inr mm)))

/-- The adapter's handler on the four requests, with the cap `2`: the first and third are
forwarded, the second (unequal lengths) and the fourth (cap exhausted) are answered locally with
`none`, and the counter ends at `2`. -/
example : (simulateQ (HidingAdversary.capChallengesImpl (spec := keySpec) List.length 2)
      (requests challenge)).run 0 = (do
        let c₁ ← challenge ([true], [false])
        let c₃ ← challenge ([false, false], [true, true])
        pure ([c₁, none, c₃, none], 2)) := by
  simp [requests, challenge, HidingAdversary.capChallengesImpl, LeftOrRight.run_cap_apply]

/-- With the cap `0` nothing is forwarded. -/
example : (simulateQ (HidingAdversary.capChallengesImpl (spec := keySpec) List.length 0)
      (requests challenge)).run 0 = pure ([none, none, none, none], 0) := by
  simp [requests, challenge, HidingAdversary.capChallengesImpl, LeftOrRight.run_cap_apply]

/-- The adversary that makes the four requests and guesses whether the last one was answered. -/
def requestAdv : HidingAdversary keySpec Unit (List Bool) (List Bool) where
  State := Unit
  preprocess := pure ()
  online _ _ := do
    let cs ← requests challenge
    pure (cs.getLastD none).isSome

/-- It makes four challenge requests, so it is not within the encryption budget `2`. -/
example : ¬ requestAdv.MakesAtMostQueries 2 := fun h => by
  simpa [requestAdv, requests, challenge] using h () ()

/-- Its adapted form is within the budget `2`, and within the budget of no round. -/
example : (requestAdv.capChallenges List.length 2).MakesAtMostQueries 2 ∧
    (requestAdv.capChallenges List.length 2).IsQueryBound 0 (0, 0) :=
  ⟨requestAdv.makesAtMostQueries_capChallenges _ _,
    HidingAdversary.isQueryBound_capChallenges
      ⟨by simp [requestAdv], fun _ _ => by simp [requestAdv, requests, challenge]⟩ _ _⟩

/-! ## The capped game -/

/-- The puzzle that reveals its key: one round asking `H ()`, whose answer is both the puzzle and
the key. -/
def reveal : TimeLockPuzzle keySpec Bool Bool where
  gen := do
    let k ← queryPoint ()
    pure (k, k)
  solve z := pure (some z)

/-- The one-bit pad over the puzzle's oracles, under a one-bit key. -/
def pad : DEMScheme (OracleComp (unifSpec + keySpec)) Bool Bool Bool where
  encrypt k msg := pure (k ^^ msg)
  decrypt k c := pure (k ^^ c)

/-- The free oracles of a hiding adversary on bits: local coins and the challenge oracle. -/
abbrev freeSpec : OracleSpec (ℕ ⊕ (Bool × Bool)) := unifSpec + LeftOrRight.spec Bool Bool

/-- The adversary that asks twice for the encryption of `false` or `true` and decrypts, with the
revealed key, the last answer it receives. -/
def twiceAdv : HidingAdversary keySpec Bool Bool Bool where
  State := Unit
  preprocess := pure ()
  online _ z := do
    let c₁ : Option Bool ← liftM ((freeSpec + keySpec.batch).query (.inl (.inr (false, true))))
    let c₂ : Option Bool ← liftM ((freeSpec + keySpec.batch).query (.inl (.inr (false, true))))
    pure (z ^^ (c₂.getD (c₁.getD false)))

/-- It makes two challenge requests, more than the cap `1`. -/
example : ¬ twiceAdv.MakesAtMostQueries 1 := fun h => by
  simpa [twiceAdv] using h () true

/-- Against any fixed answer table for `H`, the capped challenger with cap `1` answers the first
request and refuses the second, and the guess is the hidden bit. -/
lemma simulateQ_cappedHidingExperiment_twiceAdv (f : QueryImpl keySpec Id) (b : Bool) :
    simulateQ (unifFwdAnswerImpl f)
        (reveal.cappedHidingExperiment (pad.comap Prod.snd) (fun _ => ()) 1 twiceAdv b) =
      pure b := by
  simp [cappedHidingExperiment, twiceAdv, reveal, pad, QueryImpl.simulateQ_simulateQ_unbatch,
    LeftOrRight.run_cappedOracle_apply]

/-- In the random oracle model the guess is the hidden bit with probability `1`. -/
lemma rom_evalDist_cappedHidingExperiment_twiceAdv (b : Bool) :
    (ProbCompRuntime.rom keySpec).evalDist
      (reveal.cappedHidingExperiment (pad.comap Prod.snd) (fun _ => ()) 1 twiceAdv b) {b} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← Set.ofPred_eq_eq_singleton,
    evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  simp [simulateQ_cappedHidingExperiment_twiceAdv]

/-- With the cap `1`, the adversary making two requests has capped hiding advantage `1`. -/
theorem cappedHidingAdvantage_twiceAdv_one :
    reveal.cappedHidingAdvantage (pad.comap Prod.snd) (fun _ => ()) 1 twiceAdv = 1 := by
  set μ := fun b => (ProbCompRuntime.rom keySpec).evalDist
    (reveal.cappedHidingExperiment (pad.comap Prod.snd) (fun _ => ()) 1 twiceAdv b)
  have h₁ : μ true {true} = 1 := rom_evalDist_cappedHidingExperiment_twiceAdv true
  have h₀ : μ false {true} = 0 := by
    have hsum := Measure.apply_true_add_apply_false (μ false)
    rw [rom_evalDist_cappedHidingExperiment_twiceAdv false] at hsum
    have hle : μ false {true} + 1 ≤ 0 + 1 := by
      rw [hsum, zero_add]
      exact ProbCompRuntime.evalDist_apply_univ_le_one _ _
    exact le_antisymm ((ENNReal.add_le_add_iff_right one_ne_top).1 hle) zero_le
  rw [cappedHidingAdvantage_eq]
  change ENNReal.absDiff (μ true {true}) (μ false {true}) = 1
  rw [h₁, h₀]
  simp [ENNReal.absDiff]

/-- With the cap `0` the challenger answers nothing, so the capped hiding advantage is `0`: the
capped game is the hiding game of the adapted adversary, which makes no challenge query. -/
theorem cappedHidingAdvantage_twiceAdv_zero :
    reveal.cappedHidingAdvantage (pad.comap Prod.snd) (fun _ => ()) 0 twiceAdv = 0 := by
  rw [cappedHidingAdvantage_eq_hidingAdvantage_capChallenges]
  exact hidingAdvantage_eq_zero_of_makesAtMostQueries_zero _ _ _
    (twiceAdv.makesAtMostQueries_capChallenges _ 0)

/-! ## No challenge query, no advantage -/

/-- The adversary that reads `H ()` in one online round and flips a coin, and guesses their
exclusive or, without asking the challenge oracle. -/
def peekAdv : HidingAdversary keySpec Bool Bool Bool where
  State := Unit
  preprocess := pure ()
  online _ _ := do
    let r : Fin 2 ← liftM ((freeSpec + keySpec.batch).query (.inl (.inl 1)))
    let us ← liftM ((freeSpec + keySpec.batch).query (.inr [()]))
    pure (decide (r = 1) ^^ us ⟨0, Nat.zero_lt_one⟩)

/-- It makes no challenge query. -/
theorem peekAdv_makesAtMostQueries : peekAdv.MakesAtMostQueries 0 := fun _ _ => by
  simp [peekAdv]

/-- So its hiding advantage is `0`, even against the revealing puzzle. -/
theorem hidingAdvantage_peekAdv :
    hidingAdvantage reveal (pad.comap Prod.snd) (fun _ => ()) peekAdv = 0 :=
  hidingAdvantage_eq_zero_of_makesAtMostQueries_zero _ _ _ peekAdv_makesAtMostQueries

end VCVioTest.TimeLockPuzzle.HidingCap
