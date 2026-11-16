/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Delay

/-!
# The delay theorem on small parameters

Checks of the delay theorem of the pointer-chain puzzle through its public API:

* the round-bounded form `delayAdvantage_scheme_le` for two chains of one step (`n = 2`, `m = 1`)
  over `S = Fin 11`, `L = Fin 5` and `Salt = Ctx = Fin 3`, where an adversary within
  `keyRound 2 1 - 1 = 6` rounds has advantage at most
  `Q_on / 5 + Q_pre / 15 + ((Q_pre + Q_on) 9 + 81 + 1) / 11`, and the same bound as delay
  security;
* for one chain (`n = 1`) the link term `Q_on / |L|` is absent;
* the paper's form `delayAdvantageWithin_scheme_le`, for an adversary with no round bound;
* the bound with the paper's constants at the leanSeal parameters `n = 3`, `m = 2` and link width
  `b = 4`, where `P = 16`: `Q_on / 2^32 + Q_pre / 2^160 + (16 Q + 257) / 2^256`.

The answer types are sampled through `SampleableType.Fin`, so loading this module enumerates no
type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.Delay

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

/-! ## The generic theorem at small parameters -/

/-- Two chains of one step: the key is derived in round `keyRound 2 1 = 7` and the solver uses
`solvePoints 2 1 = 9` answers. -/
example : keyRound 2 1 = 7 ∧ solvePoints 2 1 = 9 := ⟨rfl, rfl⟩

/-- The delay theorem for two chains of one step, against an adversary within `6` rounds. -/
example {adv : TimeLockPuzzle.Adversary (oracleSpec 2 S L Salt Salt) (Puzzle 2 S L Salt) S}
    {Qpre Qon : ℕ} (hadv : adv.IsQueryBound Qpre (6, Qon)) :
    (scheme 2 1 mkCtx initAcc).delayAdvantage adv ≤
      (Qon : ℝ≥0∞) / 5 + Qpre / (3 * 5) + ((Qpre + Qon) * 9 + 9 ^ 2 + 1) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  simpa [hP] using delayAdvantage_scheme_le (m := 1) (initAcc := initAcc) mkCtx_injective hadv

/-- The same bound as delay security. -/
example (Qpre Qon : ℕ) :
    TimeLockPuzzle.DelaySecure (scheme 2 1 mkCtx initAcc (L := L)) Qpre (6, Qon)
      ((Qon : ℝ≥0∞) / 5 + Qpre / (3 * 5) + ((Qpre + Qon) * 9 + 9 ^ 2 + 1) / 11) := by
  have hP : solvePoints 2 1 = 9 := rfl
  have hK : keyRound 2 1 - 1 = 6 := rfl
  simpa [hP, hK] using delaySecure_scheme (n := 2) (m := 1) (initAcc := initAcc) (S := S) (L := L)
    mkCtx_injective Qpre Qon

/-- For one chain the link term is absent. -/
example {S L Salt Ctx : Type} [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
    [SampleableType S] [SampleableType L] [SampleableType Salt] [Fintype S] [Fintype L]
    [Fintype Salt] [Finite Ctx] [AddCommGroup L] {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S}
    (hctx : Function.Injective mkCtx)
    {adv : TimeLockPuzzle.Adversary (oracleSpec 1 S L Salt Ctx) (Puzzle 1 S L Salt) S}
    {Qpre Qon : ℕ} (hadv : adv.IsQueryBound Qpre (keyRound 1 m - 1, Qon)) :
    (scheme 1 m mkCtx initAcc).delayAdvantage adv ≤
      Qpre / (Fintype.card Salt * Fintype.card L) +
        ((Qpre + Qon) * solvePoints 1 m + (solvePoints 1 m : ℝ≥0∞) ^ 2 + 1) / Fintype.card S := by
  simpa using delayAdvantage_scheme_le hctx hadv

/-! ## The paper's form, with no round bound -/

/-- An adversary within `Q_pre` preprocessing queries and `Q_on` online points, with no bound on
its rounds, outputs the key within `6` completed rounds with probability at most the same bound. -/
example {adv : TimeLockPuzzle.Adversary (oracleSpec 2 S L Salt Salt) (Puzzle 2 S L Salt) S}
    {Qpre Qon : ℕ} (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ P, IsPointQueryBound (adv.online σ P) Qon) :
    TimeLockPuzzle.delayAdvantageWithin (scheme 2 1 mkCtx initAcc) adv 6 ≤
      (Qon : ℝ≥0∞) / 5 + Qpre / (3 * 5) + ((Qpre + Qon) * 9 + 9 ^ 2 + 1) / 11 := by
  have hP : solvePoints 2 1 = 9 := rfl
  have hK : keyRound 2 1 - 1 = 6 := rfl
  simpa [hP, hK] using delayAdvantageWithin_scheme_le (m := 1) (initAcc := initAcc) mkCtx_injective
    hpre honline

/-! ## The paper's constants at the leanSeal parameters -/

/-- Three chains of two steps: the key is derived in round `keyRound 3 2 = 13` and the solver uses
`solvePoints 3 2 = 16` answers. -/
example : keyRound 3 2 = 13 ∧ solvePoints 3 2 = 16 := ⟨rfl, rfl⟩

/-- With `|S| = 2^256`, `|L| = 2^32` (`b = 4`) and `|Salt| = 2^128`, the bound for three chains of
two steps is `Q_on / 2^32 + Q_pre / 2^160 + (16 (Q_pre + Q_on) + 257) / 2^256`. -/
example {S L Salt : Type} [Fintype S] [Fintype L] [Fintype Salt]
    (hS : Fintype.card S = 2 ^ 256) (hL : Fintype.card L = 2 ^ (8 * 4))
    (hSalt : Fintype.card Salt = 2 ^ 128) (Qpre Qon : ℕ) :
    (if 2 ≤ 3 then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * solvePoints 3 2 + (solvePoints 3 2 : ℝ≥0∞) ^ 2 + 1) /
            Fintype.card S =
      (Qon : ℝ≥0∞) / 2 ^ 32 + Qpre / 2 ^ 160 + (16 * (Qpre + Qon) + 257) / 2 ^ 256 := by
  rw [bound_eq_paper_of_card hS hL hSalt, show solvePoints 3 2 = 16 from rfl]
  norm_num [div_eq_mul_inv]
  ring

/-- The paper's form of the delay theorem at the leanSeal parameters with `b = 4`. -/
example {S L Salt Ctx : Type} [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
    [SampleableType S] [SampleableType L] [SampleableType Salt] [Fintype S] [Fintype L]
    [Fintype Salt] [Finite Ctx] [AddCommGroup L] {mkCtx : Salt → Ctx} {initAcc : Ctx → S}
    (hctx : Function.Injective mkCtx) (hS : Fintype.card S = 2 ^ 256)
    (hL : Fintype.card L = 2 ^ (8 * 4)) (hSalt : Fintype.card Salt = 2 ^ 128)
    {adv : TimeLockPuzzle.Adversary (oracleSpec 3 S L Salt Ctx) (Puzzle 3 S L Salt) S}
    {Qpre Qon : ℕ} (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ P, IsPointQueryBound (adv.online σ P) Qon) :
    TimeLockPuzzle.delayAdvantageWithin (scheme 3 2 mkCtx initAcc) adv 12 ≤
      (Qon : ℝ≥0∞) / 2 ^ 32 + Qpre / 2 ^ 160 +
        ((Qpre + Qon) * 16 + 16 ^ 2 + 1) / 2 ^ 256 := by
  have hP : solvePoints 3 2 = 16 := rfl
  have hK : keyRound 3 2 - 1 = 12 := rfl
  simpa [hP, hK] using delayAdvantageWithin_scheme_le_paper (m := 2) hctx hS hL hSalt hpre honline

end VCVioTest.PointerChainPuzzle.Delay
