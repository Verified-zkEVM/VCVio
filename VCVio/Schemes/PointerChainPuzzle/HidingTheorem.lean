/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingNonce
public import VCVio.Schemes.PointerChainPuzzle.HidingIdeal

/-!
# The hiding theorem of time-lock encryption with the pointer-chain puzzle

This file proves the hiding theorem of time-lock encryption with the pointer-chain puzzle over
typed random oracles: the leanSeal paper's Theorem `thm:hiding`. The scheme encrypts with the
envelope keyed by subkeys derived from the puzzle key and a fresh nonce (`sealScheme`, `sealDEM`);
the hiding game leaks the message length (`plaintextLength`). Write `P = solvePoints n m` and
`Q = Q_pre + Q_on`. For injective `mkCtx`, finite `Ctx`, a PRF whose key is uniform, and a hiding
adversary with at most `Q_pre` preprocessing queries, an online phase within `keyRound n m - 1`
rounds holding at most `Q_on` points, and at most `q_enc` challenge queries, the hiding advantage
`|Pr[Hide_1 = 1] - Pr[Hide_0 = 1]|` is at most

```
2 ([n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + (Q (P + 1) + P²) / |S|
     + q_enc² / (2 |N|) + Adv^PRF(D*))
```

(`hidingAdvantage_sealScheme_le`), where `Adv^PRF(D*)` is the advantage of the explicit
distinguisher `hidingDistinguisher` against `2 q_enc` independent keys of the PRF. With the paper's
sizes `|S| = 2^256`, `|L| = 2^(8b)`, `|Salt| = 2^128` and `|N| = 2^128` and `P' = P + 2 q_enc`,
it is at most

```
2 ([n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + (Q P' + P'²) / 2^256 + q_enc² / 2^129
     + Adv^PRF(D*))
```

(`hidingAdvantage_sealScheme_le_paper`), and the same bound holds in the paper's game, whose
challenger answers every request beyond the `q_enc`-th accepted one with `none` and assumes no
encryption budget (`cappedHidingAdvantage_sealScheme_le_paper`).

## The hybrids

At each hidden bit `b` the proof passes through four games.

* `G₀`: the hiding experiment of `sealScheme` (`TimeLockPuzzle.hidingExperiment`).
* `G₁`: the challenger takes the subkeys of each encryption from a private random function of its
  nonce, not from the subkey oracles at the key (`privateExperiment`). The two games differ only
  once the cache holds a subkey point at the key (`BadK`), so
  `|G₀ - G₁| ≤ Pr_{G₁}[BadK]` (`absDiff_hidingExperiment_privateExperiment_le`). In `G₁` every such
  point is a guess of the key by the adversary, and the delay theorem with `Q` guesses bounds
  `BadK` by `[n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + (Q P + P² + Q) / |S|`
  (`prEvent_privateExperiment_badK_le`).
* `G₁½`: the `j`-th encryption takes fresh subkeys, whatever its nonce (`counterExperiment`). The
  games differ only when two of the at most `q_enc` uniform nonces collide, so
  `|G₁ - G₁½| ≤ q_enc² / (2 |N|)`.
* `G₂`: the `j`-th encryption takes its keystream from PRF instance `(0, j)` and its tag from
  instance `(1, j)` under independent keys (`indexedRun` in the real world of `prf.multiKey`), which
  is `G₁½` in law for a uniform PRF key; together `|G₁ - G₂| ≤ q_enc² / (2 |N|)`
  (`absDiff_privateExperiment_indexed_le`).
* The ideal world: with random functions as instances, every envelope is uniform given the message
  length, so the indexed run does not depend on `b`
  (`prfIdealExperiment_indexedRun_true_eq_false`). The distinguisher `D*` guesses `b` by running
  the indexed hybrid at a uniform bit, so `|G₂(1) - G₂(0)| ≤ 2 Adv^PRF(D*)`
  (`absDiff_indexed_le_prfAdvantage`).

The triangle inequality through `G₁(1)`, `G₂(1)`, `G₂(0)` and `G₁(0)` gives the theorem. The
paper's constants follow by monotonicity in `q_enc ≥ 1`, since
`Q (P + 2 q_enc) + (P + 2 q_enc)² - (Q (P + 1) + P²) = Q (2 q_enc - 1) + 4 P q_enc + 4 q_enc²`;
an adversary with no challenge query has no advantage
(`TimeLockPuzzle.hidingAdvantage_eq_zero_of_makesAtMostQueries_zero`). In the paper's game the
adapter `TimeLockPuzzle.HidingAdversary.capChallenges` forwards at most `q_enc` accepted requests
and keeps the round budgets, and its hiding advantage is the capped one
(`TimeLockPuzzle.cappedHidingAdvantage_eq_hidingAdvantage_capChallenges`).

## Paper citation table

The leanSeal paper's statement, with the declarations that formalize it.

| Paper | Declaration |
| --- | --- |
| `thm:hiding` | `hidingAdvantage_sealScheme_le` |
| `thm:hiding`, paper's constants | `hidingAdvantage_sealScheme_le_paper` |
| `thm:hiding`, as hiding security | `hidingSecure_sealScheme` |
| `thm:hiding`, the paper's capped challenger | `cappedHidingAdvantage_sealScheme_le_paper` |
| `thm:hiding`, leanSeal's bytes (SPEC §8) | `LeanSeal.hidingAdvantage_byteScheme_le` |

## Main statements

* `PointerChainPuzzle.hidingAdvantage_sealScheme_le`: the hiding theorem with the generic sizes.
* `PointerChainPuzzle.hidingAdvantage_sealScheme_le_paper`: the hiding theorem with the paper's
  sizes.
* `PointerChainPuzzle.hidingSecure_sealScheme`: `TimeLockPuzzle.HidingSecure` with the generic
  bound, for a bound on the PRF advantage of every distinguisher `D*`.
* `PointerChainPuzzle.cappedHidingAdvantage_sealScheme_le_paper`: the hiding theorem with the
  paper's sizes in the paper's capped game, with no encryption budget.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle PRFScheme
open scoped ENNReal

namespace PointerChainPuzzle

open LeanSeal Envelope

variable {n m : ℕ} {S L Salt Ctx N K : Type}

variable (prf : PRFScheme K ByteArray (Bytes 32)) {w : ℕ} (codec : FixedCodec N w)
  (encodePuzzle : Puzzle n S L Salt → ByteArray)

variable [NeZero n] [AddCommGroup L] [DecidableEq S] [DecidableEq L] [DecidableEq Salt]
  [DecidableEq Ctx] [DecidableEq N] [SampleableType S] [SampleableType Salt] [SampleableType L]
  [SampleableType N] [SampleableType K]

/-- **The hiding theorem (`thm:hiding`).** For injective `mkCtx`, a PRF with a uniform key, and a
hiding adversary with at most `Q_pre` preprocessing queries, an online phase within
`keyRound n m - 1` rounds holding at most `Q_on` points, and at most `qEnc` challenge queries, the
hiding advantage of `sealScheme` with `sealDEM` is at most
`2 ([n ≥ 2] Q_on / |L| + Q_pre / (|Salt| |L|) + (Q (P + 1) + P²) / |S| + qEnc² / (2 |N|) + ε)`,
with `P = solvePoints n m`, `Q = Q_pre + Q_on`, and `ε` the advantage of `hidingDistinguisher`
against `2 qEnc` independent keys of the PRF.

At each hidden bit, the hiding experiment is within `BadK` of the private-subkey hybrid
(`absDiff_hidingExperiment_privateExperiment_le`, `prEvent_privateExperiment_badK_le`), which is
within `qEnc² / (2 |N|)` of the indexed hybrid (`absDiff_privateExperiment_indexed_le`); the
indexed hybrids at the two bits are within twice the PRF advantage
(`absDiff_indexed_le_prfAdvantage`). -/
theorem hidingAdvantage_sealScheme_le [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    [Fintype N] (hprf : prf.UniformKey) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (hctx : Function.Injective mkCtx)
    {adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray}
    {Qpre Qon qEnc : ℕ} (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon))
    (henc : adv.MakesAtMostQueries qEnc) :
    hidingAdvantage (sealScheme n m mkCtx initAcc N K) (sealDEM prf codec encodePuzzle)
        plaintextLength adv ≤
      2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * (solvePoints n m + 1) + (solvePoints n m : ℝ≥0∞) ^ 2) /
            Fintype.card S +
          (qEnc : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) +
          prfAdvantage (prf.multiKey (Fin (2 * qEnc)))
            (hidingDistinguisher m codec encodePuzzle qEnc mkCtx initAcc adv)) := by
  set B : ℝ≥0∞ := (if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
    Qpre / (Fintype.card Salt * Fintype.card L) +
      ((Qpre + Qon) * (solvePoints n m + 1) + (solvePoints n m : ℝ≥0∞) ^ 2) / Fintype.card S
  set D : ℝ≥0∞ := (qEnc : ℝ≥0∞) ^ 2 / (2 * Fintype.card N)
  set E : ℝ≥0∞ := prfAdvantage (prf.multiKey (Fin (2 * qEnc)))
    (hidingDistinguisher m codec encodePuzzle qEnc mkCtx initAcc adv)
  set g₀ : Bool → ℝ≥0∞ := fun b => (ProbCompRuntime.rom (sealSpec n S L Salt Ctx N K)).evalDist
    ((sealScheme n m mkCtx initAcc N K).hidingExperiment
      (sealDEM (Ctx := Ctx) prf codec encodePuzzle) plaintextLength adv b) {true}
  set g₁ : Bool → ℝ≥0∞ := fun b => Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
    (privateExperiment m prf codec encodePuzzle mkCtx initAcc adv b)).run' ∅}[z.1 = true]
  set g₂ : Bool → ℝ≥0∞ := fun b => Pr{let g ← ((prf.multiKey (Fin (2 * qEnc))).prfRealExperiment
    (indexedRun m codec encodePuzzle qEnc mkCtx initAcc adv b))}[g = true]
  -- `G₀ → G₁`: the private-subkey hop and the `BadK` bound, read on the guess alone.
  have h₀₁ (b : Bool) : ENNReal.absDiff (g₀ b) (g₁ b) ≤ B := by
    have hg₁ : g₁ b = Pr{let z ← (simulateQ (sealSpec n S L Salt Ctx N K).romImpl
        (privateExperiment m prf codec encodePuzzle mkCtx initAcc adv b)).run ∅}[z.1.1 = true] := by
      simp only [g₁, StateT.run'_eq, prEvent_map]
    rw [hg₁]
    refine (absDiff_hidingExperiment_privateExperiment_le prf codec encodePuzzle mkCtx initAcc adv
      b).trans ((prEvent_privateExperiment_badK_le (m := m) prf codec encodePuzzle mkCtx initAcc
        hctx hadv b).trans (le_of_eq ?_))
    simp only [B]
    congr 2
    ring
  -- `G₁ → G₂`: the nonce hop and the indexed PRF instances.
  have h₁₂ (b : Bool) : ENNReal.absDiff (g₁ b) (g₂ b) ≤ D :=
    absDiff_privateExperiment_indexed_le prf codec encodePuzzle qEnc mkCtx initAcc adv hprf henc b
  -- `G₂(1) → G₂(0)`: the PRF step.
  have h₂₂ : ENNReal.absDiff (g₂ true) (g₂ false) ≤ 2 * E :=
    absDiff_indexed_le_prfAdvantage codec encodePuzzle qEnc mkCtx initAcc adv prf
  rw [hidingAdvantage_eq]
  change ENNReal.absDiff (g₀ true) (g₀ false) ≤ 2 * (B + D + E)
  calc ENNReal.absDiff (g₀ true) (g₀ false)
      ≤ ENNReal.absDiff (g₀ true) (g₁ true) + ENNReal.absDiff (g₁ true) (g₂ true) +
          ENNReal.absDiff (g₂ true) (g₂ false) + ENNReal.absDiff (g₂ false) (g₁ false) +
          ENNReal.absDiff (g₁ false) (g₀ false) := by
        refine (ENNReal.absDiff_triangle _ (g₁ false) _).trans (add_le_add ?_ le_rfl)
        refine (ENNReal.absDiff_triangle _ (g₂ false) _).trans (add_le_add ?_ le_rfl)
        refine (ENNReal.absDiff_triangle _ (g₂ true) _).trans (add_le_add ?_ le_rfl)
        exact ENNReal.absDiff_triangle _ _ _
    _ ≤ B + D + 2 * E + D + B :=
        add_le_add (add_le_add (add_le_add (add_le_add (h₀₁ true) (h₁₂ true)) h₂₂)
          ((ENNReal.absDiff_comm _ _).trans_le (h₁₂ false)))
          ((ENNReal.absDiff_comm _ _).trans_le (h₀₁ false))
    _ = 2 * (B + D + E) := by ring

/-- **The hiding theorem (`thm:hiding`) with the paper's constants.** With `|S| = 2^256`,
`|L| = 2^(8b)`, `|Salt| = 2^128` and `|N| = 2^128`, and `P' = P + 2 qEnc` for
`P = solvePoints n m`, the hiding advantage is at most
`2 ([n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + (Q P' + P'²) / 2^256 + qEnc² / 2^129 + ε)`.

For `qEnc ≥ 1` this is `hidingAdvantage_sealScheme_le` at these sizes, since
`Q (P + 1) + P² ≤ Q P' + P'²`; for `qEnc = 0` the adversary has no advantage
(`TimeLockPuzzle.hidingAdvantage_eq_zero_of_makesAtMostQueries_zero`). -/
theorem hidingAdvantage_sealScheme_le_paper [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    [Fintype N] (hprf : prf.UniformKey) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (hctx : Function.Injective mkCtx) {b : ℕ} (hS : Fintype.card S = 2 ^ 256)
    (hL : Fintype.card L = 2 ^ (8 * b)) (hSalt : Fintype.card Salt = 2 ^ 128)
    (hN : Fintype.card N = 2 ^ 128)
    {adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray}
    {Qpre Qon qEnc : ℕ} (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon))
    (henc : adv.MakesAtMostQueries qEnc) :
    hidingAdvantage (sealScheme n m mkCtx initAcc N K) (sealDEM prf codec encodePuzzle)
        plaintextLength adv ≤
      2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * (solvePoints n m + 2 * qEnc) +
            ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 +
        prfAdvantage (prf.multiKey (Fin (2 * qEnc)))
          (hidingDistinguisher m codec encodePuzzle qEnc mkCtx initAcc adv)) := by
  rcases Nat.eq_zero_or_pos qEnc with rfl | hq
  · rw [hidingAdvantage_eq_zero_of_makesAtMostQueries_zero _ _ _ henc]
    exact bot_le
  refine (hidingAdvantage_sealScheme_le prf codec encodePuzzle hprf mkCtx initAcc hctx hadv
    henc).trans ?_
  rw [hS, hL, hSalt, hN]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_add, show (2 : ℝ≥0∞) * 2 ^ 128 = 2 ^ 129 by norm_num]
  have hP : (solvePoints n m : ℝ≥0∞) + 1 ≤ solvePoints n m + 2 * qEnc := by
    gcongr
    exact_mod_cast (by omega : 1 ≤ 2 * qEnc)
  have hP2 : (solvePoints n m : ℝ≥0∞) ^ 2 ≤ ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2 := by
    gcongr
    exact_mod_cast Nat.le_add_right _ _
  gcongr 2 * (_ + _ + (_ * ?_ + ?_) / _ + _ + _)

/-- **Hiding security (`thm:hiding`).** If every hiding adversary's distinguisher
`hidingDistinguisher` has PRF advantage at most `ε` against `2 qEnc` independent keys, then
`sealScheme` with `sealDEM` is hiding against adversaries with at most `Q_pre` preprocessing
queries, an online phase within `keyRound n m - 1` rounds holding at most `Q_on` points, and at
most `qEnc` challenge queries, with the bound of `hidingAdvantage_sealScheme_le`. -/
theorem hidingSecure_sealScheme [Finite Ctx] [Fintype S] [Fintype L] [Fintype Salt]
    [Fintype N] (hprf : prf.UniformKey) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (hctx : Function.Injective mkCtx) (Qpre Qon qEnc : ℕ) {ε : ℝ≥0∞}
    (hε : ∀ adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext
      ByteArray, prfAdvantage (prf.multiKey (Fin (2 * qEnc)))
        (hidingDistinguisher m codec encodePuzzle qEnc mkCtx initAcc adv) ≤ ε) :
    HidingSecure (sealScheme n m mkCtx initAcc N K) (sealDEM prf codec encodePuzzle)
      plaintextLength Qpre (keyRound n m - 1, Qon) qEnc
      (2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / Fintype.card L else 0) +
        Qpre / (Fintype.card Salt * Fintype.card L) +
          ((Qpre + Qon) * (solvePoints n m + 1) + (solvePoints n m : ℝ≥0∞) ^ 2) /
            Fintype.card S +
          (qEnc : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + ε)) := fun adv hadv henc =>
  (hidingAdvantage_sealScheme_le prf codec encodePuzzle hprf mkCtx initAcc hctx hadv henc).trans
    (by gcongr; exact hε adv)

/-- **The hiding theorem (`thm:hiding`) in the paper's game.** With the paper's capped challenger
(`TimeLockPuzzle.cappedHidingAdvantage`), which answers every request beyond the `qEnc`-th
accepted one with `none`, no encryption budget is assumed: the bound of
`hidingAdvantage_sealScheme_le_paper` holds, with the distinguisher built from the adapter
`adv.capChallenges plaintextLength qEnc`, which makes at most `qEnc` challenge queries and keeps
the round budgets (`TimeLockPuzzle.cappedHidingAdvantage_eq_hidingAdvantage_capChallenges`). -/
theorem cappedHidingAdvantage_sealScheme_le_paper [Finite Ctx] [Fintype S] [Fintype L]
    [Fintype Salt] [Fintype N] (hprf : prf.UniformKey) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (hctx : Function.Injective mkCtx) {b : ℕ} (hS : Fintype.card S = 2 ^ 256)
    (hL : Fintype.card L = 2 ^ (8 * b)) (hSalt : Fintype.card Salt = 2 ^ 128)
    (hN : Fintype.card N = 2 ^ 128)
    {adv : HidingAdversary (sealSpec n S L Salt Ctx N K) (Puzzle n S L Salt) Plaintext ByteArray}
    {Qpre Qon : ℕ} (qEnc : ℕ) (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) :
    (sealScheme n m mkCtx initAcc N K).cappedHidingAdvantage (sealDEM prf codec encodePuzzle)
        plaintextLength qEnc adv ≤
      2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * (solvePoints n m + 2 * qEnc) +
            ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 +
        prfAdvantage (prf.multiKey (Fin (2 * qEnc)))
          (hidingDistinguisher m codec encodePuzzle qEnc mkCtx initAcc
            (adv.capChallenges plaintextLength qEnc))) := by
  rw [cappedHidingAdvantage_eq_hidingAdvantage_capChallenges]
  exact hidingAdvantage_sealScheme_le_paper prf codec encodePuzzle hprf mkCtx initAcc hctx hS hL
    hSalt hN (HidingAdversary.isQueryBound_capChallenges hadv plaintextLength qEnc)
    (HidingAdversary.makesAtMostQueries_capChallenges adv plaintextLength qEnc)

end PointerChainPuzzle
