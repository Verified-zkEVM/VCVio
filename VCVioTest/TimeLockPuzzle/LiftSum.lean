/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle.Lift
public import VCVio.Schemes.PointerChainPuzzle.Delay

/-!
# Delay security for an independent sum: checks

The pointer-chain puzzle with two chains of one step (`n = 2`, `m = 1`) over `S = Fin 11`,
`L = Fin 5` and `Salt = Ctx = Fin 3`, lifted to the sum of its oracles and a side oracle
`ℕ →ₒ Fin 8`:

* the lifted puzzle is delay secure with the bound of the puzzle,
  `Q_on / 5 + Q_pre / 15 + ((Q_pre + Q_on) 9 + 81 + 1) / 11`, through `delaySecure_liftSpec_add`;
* an adversary against the lifted puzzle that queries the side oracle in preprocessing and submits
  one mixed round of a side point and a puzzle point has budget `(1, (1, 2))`, so its advantage is
  at most `2 / 5 + 1 / 15 + (3 · 9 + 81 + 1) / 11`, transferred from the puzzle through
  `delayAdvantage_liftSpec_add` and `isQueryBound_simulateSide`;
* the law of the lifted guess experiment, for outputs of any type.

The answer types are sampled through `SampleableType.Fin`, so loading this module enumerates no
type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle TimeLockPuzzle
open scoped ENNReal

namespace VCVioTest.TimeLockPuzzle.LiftSum

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

/-- The oracles of the puzzle. -/
abbrev puzSpec : OracleSpec (Point 2 S L Salt Salt) := oracleSpec 2 S L Salt Salt

/-- The side oracle, independent of the puzzle. -/
abbrev sideSpec : OracleSpec ℕ := ℕ →ₒ Fin 8

/-- The puzzle: two chains of one step. -/
abbrev puzzle : _root_.TimeLockPuzzle puzSpec (Puzzle 2 S L Salt) S :=
  scheme 2 1 mkCtx initAcc

/-! ## Delay security of the lifted puzzle -/

/-- The lifted puzzle is delay secure with the bound of the puzzle. -/
theorem delaySecure_liftSpec_puzzle (Qpre Qon : ℕ) :
    (puzzle.liftSpec (puzSpec + sideSpec)).DelaySecure Qpre (6, Qon)
      ((Qon : ℝ≥0∞) / 5 + Qpre / (3 * 5) + ((Qpre + Qon) * 9 + 9 ^ 2 + 1) / 11) := by
  have hP : solvePoints 2 1 = 9 := rfl
  have hK : keyRound 2 1 - 1 = 6 := rfl
  refine delaySecure_liftSpec_add ?_
  simpa [hP, hK] using delaySecure_scheme (n := 2) (m := 1) (initAcc := initAcc) (S := S)
    (L := L) mkCtx_injective Qpre Qon

/-! ## A concrete adversary using the side oracle -/

/-- The mixed round: the side point `5` and the step point of chain `0` at salt `0` and state
`0`. -/
abbrev mixed : List (Point 2 S L Salt Salt ⊕ ℕ) := [.inr 5, .inl (.step 0 0 0)]

/-- Preprocessing queries the side point `5`; the online phase submits the mixed round and
guesses the answer at the step point. -/
@[expose]
def mixedAdv : Adversary (puzSpec + sideSpec) (Puzzle 2 S L Salt) S where
  State := Fin 8
  preprocess := liftM ((unifSpec + (puzSpec + sideSpec)).query (.inr (.inr 5)))
  online _ _ := (fun us => (us ⟨1, by simp⟩ : S)) <$>
    liftM ((unifSpec + (puzSpec + sideSpec).batch).query (.inr mixed))

/-- The adversary makes one preprocessing query and submits one round of two points, within the
budget of `6` rounds. -/
theorem mixedAdv_isQueryBound : mixedAdv.IsQueryBound 1 (6, 2) := by
  refine ⟨by simp [mixedAdv], fun _ _ => ?_⟩
  simp [mixedAdv, IsOnlineQueryBound]

/-- Its advantage against the lifted puzzle is at most the bound of the puzzle at `Q_pre = 1` and
`Q_on = 2`: the side queries are answered privately by its simulation, within the same budget. -/
theorem delayAdvantage_liftSpec_mixedAdv_le :
    (puzzle.liftSpec (puzSpec + sideSpec)).delayAdvantage mixedAdv ≤
      (2 : ℝ≥0∞) / 5 + 1 / (3 * 5) + ((1 + 2) * 9 + 9 ^ 2 + 1) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  rw [delayAdvantage_liftSpec_add]
  simpa [hP] using delayAdvantage_scheme_le (m := 1) (initAcc := initAcc) mkCtx_injective
    (TwoPhaseAdversary.isQueryBound_simulateSide mixedAdv_isQueryBound)

/-! ## The law of the lifted guess experiment -/

/-- For outputs of any type, the lifted guess experiment against `adv` has the law of the guess
experiment of the puzzle against `adv.simulateSide`. -/
example {Out : Type}
    (adv : TwoPhaseAdversary unifSpec (puzSpec + sideSpec) (Puzzle 2 S L Salt) Out) :
    (simulateQ (puzSpec + sideSpec).romImpl
        ((puzzle.liftSpec (puzSpec + sideSpec)).guessExperiment adv)).run' ∅ =ᵈ
      (simulateQ puzSpec.romImpl (puzzle.guessExperiment adv.simulateSide)).run' ∅ :=
  evalDist_guessExperiment_liftSpec_add puzzle adv

end VCVioTest.TimeLockPuzzle.LiftSum
