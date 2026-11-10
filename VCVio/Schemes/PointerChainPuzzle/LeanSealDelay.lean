/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSealBridge
public import VCVio.Schemes.PointerChainPuzzle.Delay

/-!
# The delay theorem for leanSeal

This file proves the delay theorem of leanSeal at the byte level: the theorem of leanSeal's SPEC
§8 ("The delay theorem") and the leanSeal paper's Theorem `thm:delay`, for leanSeal's own byte
encoding (`byteScheme`) rather than for the pointer-chain puzzle over independent typed oracles.

## Idealization

All of SHA-256 is one random oracle on byte strings, `byteSpec = ByteArray →ₒ Bytes 32`. The
puzzle hashes every typed point at its hash input (`hashInput`): a chain step at its 52-byte
input, every other point at a length-prefixed label followed by fixed-width fields. Domain
separation between the six typed oracles comes from these input lengths and labels alone. Nothing
is assumed of the compression function, and nothing is proved about SHA-256 beyond computing it.

## The theorem

Write `T_key = keyRound n m = n (m + 2) + 1` and `P = solvePoints n m = n (m + 3) + 1`. For a link
width `b ≤ 32` and fewer than `2^32` chains, in particular for every parameter set leanSeal accepts
(`Valid b n m`), and for every byte-level adversary with at most `Q_pre` preprocessing queries and
at most `Q_on` online point queries, in any number of rounds, the probability that its online
phase outputs the key within fewer than `T_key` completed rounds is at most

```
[n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + ((Q_pre + Q_on) P + P² + 1) / 2^256
```

(`delayAdvantageWithin_byteScheme_le`, `delayAdvantageWithin_byteScheme_le_of_valid`). This is the
bound of SPEC §8 and of `thm:delay`.

The proof composes three results. The delay theorem of the typed pointer-chain puzzle at the byte
types (`delaySecure_scheme_paper`) applies because the context of a salt determines the salt
(`ctx_injective`) and `Bytes k` has `2^(8k)` elements (`card_bytes`). The adapter turns a
byte-level adversary into a typed one within the same budgets
(`RandomOracleEncoding.isQueryBound_adaptAdversary`) that wins at least as often
(`delayAdvantage_byteScheme_le`). Together they give delay security of `byteScheme`
(`delaySecure_byteScheme`), and the truncated adversary removes the bound on the rounds
(`TimeLockPuzzle.delayAdvantageWithin_le_of_delaySecure`).

## Paper citation table

The leanSeal paper's statement at leanSeal's bytes, with the declarations that formalize it and
the steps that carry the typed theorem over.

| Paper | Declaration |
| --- | --- |
| `thm:delay`, leanSeal's bytes (SPEC §8) | `delayAdvantageWithin_byteScheme_le` |
| `thm:delay`, at valid parameters | `delayAdvantageWithin_byteScheme_le_of_valid` |
| `thm:delay`, within the rounds | `delaySecure_byteScheme`, `delaySecure_byteScheme_of_valid` |
| `thm:delay`, typed, paper's constants | `delaySecure_scheme_paper` |
| A1, independent oracles by domain separation (SPEC §1, §3) | `hashInput_injective`, `not_clash` |
| The byte adversary as a typed one | `delayAdvantage_byteScheme_le` |
| The sizes `2^256`, `2^(8b)`, `2^128` | `card_bytes` |

### Definitions to check

To trust the rows above, read these definitions and compare each with the source named.

* The game: `TimeLockPuzzle.delayAdvantageWithin` against the event of `thm:delay`, as for the
  typed theorem (`VCVio.Schemes.PointerChainPuzzle.Delay`).
* The oracle: `byteSpec` against SHA-256 as one random oracle on byte strings (A1, SPEC §8).
* The adversary class: `TimeLockPuzzle.Adversary byteSpec (Puzzle b n) (Bytes 32)` against the
  attacker `(A_0, A_1)` of `sec:theorem`, with SHA-256 its only oracle.
* The budgets: `IsPreprocessingQueryBound` and `IsPointQueryBound` against `Q_pre` and `Q_on`,
  here counting queries to SHA-256.
* The scheme: `byteScheme` against SPEC §4 and §5; `simulateQ_byteScheme_gen` and
  `simulateQ_byteScheme_solve` equate it with the executable leanSeal of `LeanSeal.lean`.
* The encoding: `hashInput` and `encoding` against the chain step of SPEC §3 and the labelled
  hash `TH` of SPEC §1, and the mask as the first `b` bytes of its hash (SPEC §4).
* The parameters and constants: `Valid` against SPEC §2, `ctx` against the context of SPEC §4,
  and `keyRound`, `solvePoints` against `T_key` and `P` of SPEC §8.

## Main statements

* `PointerChainPuzzle.LeanSeal.card_bytes`: `Bytes k` has `2^(8k)` elements.
* `PointerChainPuzzle.LeanSeal.ctx_injective`: the context determines the salt.
* `PointerChainPuzzle.LeanSeal.delaySecure_byteScheme`: delay security of leanSeal over the single
  oracle against adversaries within `T_key - 1` online rounds, at the paper's bound.
* `PointerChainPuzzle.LeanSeal.delayAdvantageWithin_byteScheme_le`: the paper's form, with no bound
  on the rounds of the adversary.
* `PointerChainPuzzle.LeanSeal.delaySecure_byteScheme_of_valid`,
  `PointerChainPuzzle.LeanSeal.delayAdvantageWithin_byteScheme_le_of_valid`: the same under
  leanSeal's parameter check `Valid b n m`.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle
open scoped ENNReal

namespace PointerChainPuzzle.LeanSeal

/-! ## Sizes and the context -/

/-- Byte strings of length `k` number `2^(8k)`. -/
theorem card_bytes (k : ℕ) : Fintype.card (Bytes k) = 2 ^ (8 * k) := by
  rw [Fintype.card_congr (Bytes.equivVector.trans (arrayVectorEquivFin UInt8 k)),
    Fintype.card_fun, Fintype.card_fin, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8,
    pow_mul]

/-- The context of a puzzle determines its salt: the salt is copied verbatim into the last
16 bytes of the context. -/
theorem ctx_injective (b n m : ℕ) : Function.Injective (ctx b n m) := by
  intro salt salt' h
  have hl : ctxList b n m salt = ctxList b n m salt' := by
    simpa [ctx] using congrArg (fun x : Bytes 32 => x.toVector.toList) h
  simp only [ctxList, List.append_cancel_left_eq] at hl
  exact Bytes.ext (Vector.toList_inj.mp hl)

/-! ## The delay theorem -/

variable {b n : ℕ}

/-- **The delay theorem for leanSeal, within the rounds.** With SHA-256 one random oracle on byte
strings, for `b ≤ 32` and fewer than `2^32` chains, leanSeal is delay secure against byte-level
adversaries with at most `Q_pre` preprocessing queries and at most `keyRound n m - 1` online rounds
holding at most `Q_on` points, with the bound
`[n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + ((Q_pre + Q_on) P + P² + 1) / 2^256`, where
`P = solvePoints n m`. -/
theorem delaySecure_byteScheme (m : ℕ) [NeZero n] (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (Qpre Qon : ℕ) :
    DelaySecure (byteScheme b n m) Qpre (keyRound n m - 1, Qon)
      ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) / 2 ^ 256) :=
  fun adv hadv => (delayAdvantage_byteScheme_le hb hn m adv).trans <|
    delaySecure_scheme_paper (ctx_injective b n m) (card_bytes 32) (card_bytes b) (card_bytes 16)
      Qpre Qon _ ((encoding hb hn).isQueryBound_adaptAdversary hadv)

/-- **The delay theorem for leanSeal (SPEC §8, the paper's `thm:delay`).** With SHA-256 one random
oracle on byte strings, for `b ≤ 32` and fewer than `2^32` chains, a byte-level adversary with at
most `Q_pre` preprocessing queries whose online phase holds at most `Q_on` points, in any number of
rounds, outputs the key within fewer than `T_key = n (m + 2) + 1` completed rounds with probability
at most `[n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + ((Q_pre + Q_on) P + P² + 1) / 2^256`, where
`P = n (m + 3) + 1`. -/
theorem delayAdvantageWithin_byteScheme_le (m : ℕ) [NeZero n] (hb : b ≤ 32) (hn : n < 2 ^ 32)
    {adv : Adversary byteSpec (Puzzle b n) (Bytes 32)} {Qpre Qon : ℕ}
    (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ puzzle, IsPointQueryBound (adv.online σ puzzle) Qon) :
    delayAdvantageWithin (byteScheme b n m) adv (keyRound n m - 1) ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) / 2 ^ 256 :=
  delayAdvantageWithin_le_of_delaySecure (delaySecure_byteScheme m hb hn Qpre Qon) hpre honline

/-! ## Every parameter set leanSeal accepts -/

/-- Valid parameters have a link width of at most 32 bytes. -/
lemma Valid.le_32 {m : ℕ} (hv : Valid b n m) : b ≤ 32 := hv.2.1

/-- Valid parameters have fewer than `2^32` chains. -/
lemma Valid.lt_two_pow_32 {m : ℕ} (hv : Valid b n m) : n < 2 ^ 32 :=
  lt_of_le_of_lt hv.2.2.2.1 (Nat.pow_lt_pow_right (by norm_num) (by norm_num))

/-- **The delay theorem for leanSeal within the rounds, at valid parameters.** For every parameter
set leanSeal accepts, leanSeal over the single oracle is delay secure against adversaries within
`Q_pre` preprocessing queries and `keyRound n m - 1` online rounds holding at most `Q_on` points,
at the bound of `delaySecure_byteScheme`. -/
theorem delaySecure_byteScheme_of_valid {m : ℕ} [NeZero n] (hv : Valid b n m) (Qpre Qon : ℕ) :
    DelaySecure (byteScheme b n m) Qpre (keyRound n m - 1, Qon)
      ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) / 2 ^ 256) :=
  delaySecure_byteScheme m hv.le_32 hv.lt_two_pow_32 Qpre Qon

/-- **The delay theorem for leanSeal (SPEC §8, the paper's `thm:delay`), at valid parameters.**
For every parameter set leanSeal accepts, a byte-level adversary with at most `Q_pre`
preprocessing queries and at most `Q_on` online points outputs the key within fewer than
`T_key = n (m + 2) + 1` completed rounds with probability at most the bound of
`delayAdvantageWithin_byteScheme_le`. -/
theorem delayAdvantageWithin_byteScheme_le_of_valid {m : ℕ} [NeZero n] (hv : Valid b n m)
    {adv : Adversary byteSpec (Puzzle b n) (Bytes 32)} {Qpre Qon : ℕ}
    (hpre : IsPreprocessingQueryBound adv.preprocess Qpre)
    (honline : ∀ σ puzzle, IsPointQueryBound (adv.online σ puzzle) Qon) :
    delayAdvantageWithin (byteScheme b n m) adv (keyRound n m - 1) ≤
      (if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * solvePoints n m + (solvePoints n m : ℝ≥0∞) ^ 2 + 1) / 2 ^ 256 :=
  delayAdvantageWithin_byteScheme_le m hv.le_32 hv.lt_two_pow_32 hpre honline

end PointerChainPuzzle.LeanSeal
