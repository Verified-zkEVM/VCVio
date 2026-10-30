/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSealDelay

/-!
# The delay theorem for leanSeal: checks

Checks of the byte-level delay theorem through its public API:

* the sizes of the byte types and the injectivity of the context;
* the theorem at the parameters of the round table of leanSeal's security notes (`n = 3`
  chains of `m = 2` steps) with leanSeal's default link width `b = 24`: the key is derived in
  round `13`, the solver uses `16` answers, and an adversary outputs the key within `12` completed
  rounds with probability at most
  `Q_on / 2^192 + Q_pre / 2^320 + (16 (Q_pre + Q_on) + 257) / 2^256`;
* the corollary under `Valid`, with the parameter check discharged by `decide`, there and at
  leanSeal's reference parameters `n = 16`, `m = 2^29`, `b = 24`;
* for one chain the link term is absent.

No declaration of this module enumerates a type when the module is loaded.
-/

public section

open OracleComp OracleSpec TimeLockPuzzle PointerChainPuzzle PointerChainPuzzle.LeanSeal
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.LeanSealDelay

/-! ## Sizes and the context -/

/-- States, contexts and keys number `2^256`, salts `2^128` and 24-byte links `2^192`. -/
example : Fintype.card (Bytes 32) = 2 ^ 256 ∧ Fintype.card (Bytes 16) = 2 ^ 128 ∧
    Fintype.card (Bytes 24) = 2 ^ 192 :=
  ⟨card_bytes 32, card_bytes 16, card_bytes 24⟩

/-- The context determines the salt, at every parameter set. -/
example : Function.Injective (ctx 24 3 2) := ctx_injective 24 3 2

/-! ## The round table of leanSeal's security notes, with 24-byte links -/

/-- Three chains of two steps: the key is derived in round `13` and the solver uses `16`
answers. -/
example : keyRound 3 2 = 13 ∧ solvePoints 3 2 = 16 := ⟨rfl, rfl⟩

/-- Delay security of leanSeal over the single oracle at `n = 3`, `m = 2`, `b = 24`, against
adversaries within `12` online rounds. -/
example (Qpre Qon : ℕ) :
    DelaySecure (byteScheme 24 3 2) Qpre (12, Qon)
      ((Qon : ℝ≥0∞) / 2 ^ 192 + Qpre / 2 ^ 320 + ((Qpre + Qon) * 16 + 16 ^ 2 + 1) / 2 ^ 256) := by
  have hP : solvePoints 3 2 = 16 := rfl
  have hK : keyRound 3 2 - 1 = 12 := rfl
  simpa [hP, hK] using delaySecure_byteScheme 2 (b := 24) (n := 3) (by norm_num) (by norm_num)
    Qpre Qon

/-- The paper's form at `n = 3`, `m = 2`, `b = 24`: with no bound on its rounds, an adversary
outputs the key within `12` completed rounds with probability at most
`Q_on / 2^192 + Q_pre / 2^320 + ((Q_pre + Q_on) 16 + 16² + 1) / 2^256`. -/
example {adv : Adversary byteSpec (Puzzle 24 3) (Bytes 32)} {Qpre Qon : ℕ}
    (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ puzzle, IsPointQueryBound (adv.online σ puzzle) Qon) :
    delayAdvantageWithin (byteScheme 24 3 2) adv 12 ≤
      (Qon : ℝ≥0∞) / 2 ^ 192 + Qpre / 2 ^ 320 + ((Qpre + Qon) * 16 + 16 ^ 2 + 1) / 2 ^ 256 := by
  have hP : solvePoints 3 2 = 16 := rfl
  have hK : keyRound 3 2 - 1 = 12 := rfl
  simpa [hP, hK] using delayAdvantageWithin_byteScheme_le 2 (by norm_num) (by norm_num) hpre
    honline

/-- The same through the corollary under `Valid`, the parameter check decided. -/
example {adv : Adversary byteSpec (Puzzle 24 3) (Bytes 32)} {Qpre Qon : ℕ}
    (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ puzzle, IsPointQueryBound (adv.online σ puzzle) Qon) :
    delayAdvantageWithin (byteScheme 24 3 2) adv 12 ≤
      (Qon : ℝ≥0∞) / 2 ^ 192 + Qpre / 2 ^ 320 + ((Qpre + Qon) * 16 + 16 ^ 2 + 1) / 2 ^ 256 := by
  have hP : solvePoints 3 2 = 16 := rfl
  have hK : keyRound 3 2 - 1 = 12 := rfl
  simpa [hP, hK] using delayAdvantageWithin_byteScheme_le_of_valid (by decide : Valid 24 3 2)
    hpre honline

/-! ## leanSeal's reference parameters -/

/-- The reference parameters `n = 16`, `m = 2^29`, `b = 24` pass leanSeal's parameter check. -/
example : Valid 24 16 (2 ^ 29) := by decide

/-- The paper's form at the reference parameters, through the corollary under `Valid`. -/
example {adv : Adversary byteSpec (Puzzle 24 16) (Bytes 32)} {Qpre Qon : ℕ}
    (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ puzzle, IsPointQueryBound (adv.online σ puzzle) Qon) :
    delayAdvantageWithin (byteScheme 24 16 (2 ^ 29)) adv (keyRound 16 (2 ^ 29) - 1) ≤
      (Qon : ℝ≥0∞) / 2 ^ 192 + Qpre / 2 ^ 320 +
        ((Qpre + Qon) * solvePoints 16 (2 ^ 29) + (solvePoints 16 (2 ^ 29) : ℝ≥0∞) ^ 2 + 1) /
          2 ^ 256 := by
  simpa using delayAdvantageWithin_byteScheme_le_of_valid (by decide : Valid 24 16 (2 ^ 29))
    hpre honline

/-! ## One chain -/

/-- For one chain the link term is absent. -/
example {b m : ℕ} (hb : b ≤ 32) {adv : Adversary byteSpec (Puzzle b 1) (Bytes 32)} {Qpre Qon : ℕ}
    (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ puzzle, IsPointQueryBound (adv.online σ puzzle) Qon) :
    delayAdvantageWithin (byteScheme b 1 m) adv (keyRound 1 m - 1) ≤
      Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * solvePoints 1 m + (solvePoints 1 m : ℝ≥0∞) ^ 2 + 1) / 2 ^ 256 := by
  simpa using delayAdvantageWithin_byteScheme_le m hb (by norm_num) hpre honline

end VCVioTest.PointerChainPuzzle.LeanSealDelay
