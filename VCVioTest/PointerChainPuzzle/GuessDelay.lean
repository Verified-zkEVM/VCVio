/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Delay

/-!
# The delay theorem for several guesses on small parameters

Checks of the delay development for online phases with outputs of any type, through the public
API, for two chains of one step (`n = 2`, `m = 1`) over `S = Fin 11`, `L = Fin 5` and
`Salt = Ctx = Fin 3`:

* `prEvent_guessExperiment_scheme_le` with one guess (`q = 1`) gives the bound of
  `delayAdvantage_scheme_le`, `Q_on / 5 + Q_pre / 15 + ((Q_pre + Q_on) 9 + 81 + 1) / 11`, and with
  `q` guesses the last term `1` becomes `q`;
* the bound of `delayAdvantage_scheme_le` follows from `prEvent_guessExperiment_scheme_le` at the
  adversary that submits its output as its one guess (`mapOutput`);
* an adversary built with `TwoPhaseAdversary.mapOutput` keeps its budget
  (`isQueryBound_mapOutput`), and its delay experiment is the image of the original one
  (`guessExperiment_mapOutput`);
* `seed_eq_seedOf` and `idealExperiment_eq_map_toResult` at a concrete adversary.

The answer types are sampled through `SampleableType.Fin`, so loading this module enumerates no
type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.GuessDelay

/-- States are `Fin 11`. -/
abbrev S := Fin 11

/-- Links are `Fin 5`. -/
abbrev L := Fin 5

/-- Salts and contexts are `Fin 3`. -/
abbrev Salt := Fin 3

/-- The context of a salt. -/
def mkCtx (salt : Salt) : Salt := salt + 1

/-- The initial accumulator of a context. -/
def initAcc (ctx : Salt) : S := ⟨ctx.val + 6, by omega⟩

/-- Adding one is injective on `Fin 3`. -/
lemma mkCtx_injective : Function.Injective mkCtx := fun a b h => by
  simpa [mkCtx] using h

/-! ## One guess and several guesses -/

/-- With one guess, the delay theorem for guesses has the bound of `delayAdvantage_scheme_le`. -/
lemma prEvent_guessExperiment_one_le
    {adv : TimeLockPuzzle.TwoPhaseAdversary unifSpec (oracleSpec 2 S L Salt Salt)
      (Puzzle 2 S L Salt) (Fin 1 → S)}
    {Qpre Qon : ℕ} (hadv : adv.IsQueryBound Qpre (6, Qon)) :
    Pr{let z ← (simulateQ (oracleSpec 2 S L Salt Salt).romImpl
        ((scheme 2 1 mkCtx initAcc).guessExperiment adv)).run' ∅}[∃ i, z.1 i = z.2] ≤
      (Qon : ℝ≥0∞) / 5 + Qpre / (3 * 5) + ((Qpre + Qon) * 9 + 9 ^ 2 + 1) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  simpa [hP] using
    prEvent_guessExperiment_scheme_le (m := 1) (initAcc := initAcc) mkCtx_injective hadv

/-- The bound of `delayAdvantage_scheme_le`, derived from the delay theorem for guesses: a delay
adversary submits its output as its one guess (`mapOutput`), within the same budget
(`isQueryBound_mapOutput`), and the delay advantage is the probability that this guess is the key
(`guessExperiment_mapOutput`, `delayAdvantage_eq_prEvent_guessExperiment`). -/
lemma delayAdvantage_le_of_prEvent_guessExperiment_scheme_le
    {adv : TimeLockPuzzle.Adversary (oracleSpec 2 S L Salt Salt) (Puzzle 2 S L Salt) S}
    {Qpre Qon : ℕ} (hadv : adv.IsQueryBound Qpre (6, Qon)) :
    (scheme 2 1 mkCtx initAcc).delayAdvantage adv ≤
      (Qon : ℝ≥0∞) / 5 + Qpre / (3 * 5) + ((Qpre + Qon) * 9 + 9 ^ 2 + 1) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  have h := prEvent_guessExperiment_scheme_le (m := 1) (initAcc := initAcc) mkCtx_injective
    (TimeLockPuzzle.TwoPhaseAdversary.isQueryBound_mapOutput (fun s (_ : Fin 1) => s) hadv)
  rw [TimeLockPuzzle.guessExperiment_mapOutput, simulateQ_map] at h
  rw [TimeLockPuzzle.delayAdvantage_eq_prEvent_guessExperiment]
  simpa [hP, StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map, Function.comp_def]
    using h

/-- With `q` guesses, the last term `1` becomes `q`. -/
example {q : ℕ}
    {adv : TimeLockPuzzle.TwoPhaseAdversary unifSpec (oracleSpec 2 S L Salt Salt)
      (Puzzle 2 S L Salt) (Fin q → S)}
    {Qpre Qon : ℕ} (hadv : adv.IsQueryBound Qpre (6, Qon)) :
    Pr{let z ← (simulateQ (oracleSpec 2 S L Salt Salt).romImpl
        ((scheme 2 1 mkCtx initAcc).guessExperiment adv)).run' ∅}[∃ i, z.1 i = z.2] ≤
      (Qon : ℝ≥0∞) / 5 + Qpre / (3 * 5) + ((Qpre + Qon) * 9 + 9 ^ 2 + q) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  simpa [hP] using
    prEvent_guessExperiment_scheme_le (m := 1) (initAcc := initAcc) mkCtx_injective hadv

/-! ## Adversaries built with `mapOutput` -/

/-- An adversary with no preprocessing that outputs a fixed state at once. -/
def constAdv : TimeLockPuzzle.Adversary (oracleSpec 2 S L Salt Salt) (Puzzle 2 S L Salt) S where
  State := Unit
  preprocess := pure ()
  online _ _ := pure 0

/-- The constant adversary makes no queries. -/
lemma constAdv_isQueryBound (b : ℕ × ℕ) : constAdv.IsQueryBound 0 b :=
  ⟨trivial, fun _ _ => isOnlineQueryBound_pure _ _⟩

/-- The constant adversary, guessing its state once and its successor once. -/
def twoGuessAdv : TimeLockPuzzle.TwoPhaseAdversary unifSpec (oracleSpec 2 S L Salt Salt)
    (Puzzle 2 S L Salt) (Fin 2 → S) :=
  constAdv.mapOutput fun s i => s + Fin.castLE (by decide) i

/-- `mapOutput` keeps the budget. -/
lemma twoGuessAdv_isQueryBound (b : ℕ × ℕ) : twoGuessAdv.IsQueryBound 0 b :=
  TimeLockPuzzle.TwoPhaseAdversary.isQueryBound_mapOutput _ (constAdv_isQueryBound b)

/-- The delay experiment of `twoGuessAdv` is the image of the delay experiment of `constAdv`. -/
lemma guessExperiment_twoGuessAdv :
    (scheme 2 1 mkCtx initAcc).guessExperiment twoGuessAdv =
      (fun z => (fun i : Fin 2 => z.1 + Fin.castLE (by decide) i, z.2)) <$>
        (scheme 2 1 mkCtx initAcc).guessExperiment constAdv :=
  TimeLockPuzzle.guessExperiment_mapOutput _ _ _

/-- Two guesses with no queries find the key with probability at most `(81 + 2) / 11`. -/
lemma prEvent_guessExperiment_twoGuessAdv_le :
    Pr{let z ← (simulateQ (oracleSpec 2 S L Salt Salt).romImpl
        ((scheme 2 1 mkCtx initAcc).guessExperiment twoGuessAdv)).run' ∅}[∃ i, z.1 i = z.2] ≤
      ((9 : ℝ≥0∞) ^ 2 + 2) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  simpa [hP] using prEvent_guessExperiment_scheme_le (m := 1) (initAcc := initAcc)
    mkCtx_injective (twoGuessAdv_isQueryBound (_, 0))

/-! ## The seed and the ideal experiment at a concrete adversary -/

/-- The seed of the constant adversary is the seed of its preprocessing phase. -/
lemma seed_constAdv : seed constAdv 1 = seedOf constAdv.preprocess 1 :=
  seed_eq_seedOf constAdv 1

/-- The ideal experiment of the constant adversary is the projection of its ideal outcome. -/
lemma idealExperiment_constAdv :
    idealExperiment constAdv 1 mkCtx initAcc =
      IdealOutcome.toResult <$> idealOutcomeExperiment constAdv 1 mkCtx initAcc :=
  idealExperiment_eq_map_toResult constAdv 1 mkCtx initAcc

end VCVioTest.PointerChainPuzzle.GuessDelay
