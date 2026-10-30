/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingTheorem
public import VCVio.Schemes.PointerChainPuzzle.LeanSealDelay
public import VCVio.Schemes.PointerChainPuzzle.LeanSealHidingBridge
public import VCVio.Schemes.PointerChainPuzzle.LeanSealHidingEncoding

/-!
# The hiding theorem for leanSeal

This file proves the hiding theorem of time-lock encryption with leanSeal at the byte level: the
hiding bound of leanSeal's SPEC §8 ("Hiding the contents") and the leanSeal paper's Theorem
`thm:hiding`, for leanSeal's own puzzle encoding (`byteScheme`) and envelope (`byteEnvelope`)
rather than for the pointer-chain seal over independent typed oracles.

## Idealization

All of SHA-256 is one random oracle on byte strings, `byteSpec = ByteArray →ₒ Bytes 32`. Both the
puzzle's hash inputs and the two subkey derivations of the envelope,
`TH("leanseal/v1/enc", K ‖ η)` and `TH("leanseal/v1/mac", K ‖ η)`, query it. HMAC-SHA256
(`hmacPRF`) is computed outside the oracle and is the pseudorandom function of the envelope.

## The theorem

Write `T_key = keyRound n m`, `P = solvePoints n m` and `P' = P + 2 Q_enc`. For a link width
`b ≤ 32` and fewer than `2^32` chains, in particular for every parameter set leanSeal accepts
(`Valid b n m`), and for every byte-level hiding adversary with at most `Q_pre` preprocessing
queries, an online phase within `T_key - 1` rounds holding at most `Q_on` points, and at most
`Q_enc` challenge queries, the hiding advantage is at most

```
2 ([n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128 + 8b) + ((Q_pre + Q_on) P' + P'²) / 2^256
     + Q_enc² / 2^129 + Adv^PRF)
```

(`hidingAdvantage_byteScheme_le`, `hidingAdvantage_byteScheme_le_of_valid`), where `Adv^PRF` is
the advantage of the explicit distinguisher `byteHidingDistinguisher` against HMAC-SHA256 under
`2 Q_enc` independent keys. The same bound holds in the paper's game, whose challenger answers
every request beyond the `Q_enc`-th accepted one with `none` and assumes no encryption budget
(`cappedHidingAdvantage_byteScheme_le`, `cappedHidingAdvantage_byteScheme_le_of_valid`).

The proof composes three results. The extended encoding `sealEncoding` of the oracles with subkeys
into `byteSpec` never clashes, and the byte-level generator and encryption are the typed ones with
their queries encoded (`byteScheme_gen_eq`, `byteEnvelope_encrypt_eq`), so the byte-level hiding
advantage is the typed hiding advantage of the adapted adversary
(`hidingAdvantage_byteScheme_eq`). The adapter keeps the budgets
(`RandomOracleEncoding.isQueryBound_adaptTwoPhase`,
`RandomOracleEncoding.makesAtMostQueries_adaptHidingAdversary`). The typed hiding theorem with the
paper's constants (`hidingAdvantage_sealScheme_le_paper`) applies at leanSeal's types because the
context of a salt determines the salt (`ctx_injective`), `Bytes k` has `2^(8k)` elements
(`card_bytes`) and the HMAC key is uniform (`hmacPRF_uniformKey`).

## Scope

Running time is not modelled. The bound is an explicit reduction: it names the PRF distinguisher
but bounds neither its running time nor its relation to the paper's time-bounded `Adv^PRF`, which
SPEC §8 takes over adversaries in time `t + O(Q + P')`. Hiding security
(`hidingSecure_byteScheme`) assumes the PRF bound for the distinguishers of all byte-level
adversaries, including those outside the budgets; `hidingSecure_byteScheme_of_budget` assumes it
only for adversaries within the budgets. Query budgets do not bound local computation, so even the
budgeted premise covers exhaustive attacks; a computational corollary also needs an efficiency
restriction on the adversary and a running-time bound for the named distinguisher.

## Paper citation table

The leanSeal paper's statement, with the declarations that formalize it at leanSeal's bytes.

| Paper | Declaration |
| --- | --- |
| `thm:hiding`, leanSeal's bytes (SPEC §8) | `hidingAdvantage_byteScheme_le` |
| `thm:hiding`, every parameter set leanSeal accepts | `hidingAdvantage_byteScheme_le_of_valid` |
| `thm:hiding`, as hiding security | `hidingSecure_byteScheme`, `hidingSecure_byteScheme_of_valid` |
| `thm:hiding`, as hiding security, budgeted PRF premise | `hidingSecure_byteScheme_of_budget` |
| `thm:hiding`, the paper's capped challenger | `cappedHidingAdvantage_byteScheme_le` |
| `thm:hiding`, capped, valid parameters | `cappedHidingAdvantage_byteScheme_le_of_valid` |
| The game | `TimeLockPuzzle.hidingExperiment`, `LeftOrRight.oracle` |
| The budgets | `TwoPhaseAdversary.IsQueryBound`, `HidingAdversary.MakesAtMostQueries` |

### Definitions to check

To trust the rows above, read these definitions and compare each with the source named.

* The game: `TimeLockPuzzle.hidingExperiment` and `TimeLockPuzzle.hidingAdvantage` against
  `Hide_β` and `Adv^hide` of `def:hiding` (`fig:games`); `TimeLockPuzzle.cappedHidingExperiment`
  against its oracle `Enc` as written.
* The challenge oracle: `LeftOrRight.oracle` with `plaintextLength` against `Enc` of `fig:games`,
  which answers `⊥` when `|M₀| ≠ |M₁|`.
* The adversary class: `TimeLockPuzzle.HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray`
  against the attacker `(A_0, A_1)` of `def:hiding`, with SHA-256 and `Enc` as its oracles.
* The budgets: `TwoPhaseAdversary.IsQueryBound` at `(keyRound n m - 1, Q_on)` against `Q_pre`,
  `Q_on` and "stops within fewer than `T_key` oracle rounds" (`def:hiding`);
  `HidingAdversary.MakesAtMostQueries` against the `Q_enc` envelopes.
* The scheme: `byteScheme` as for the delay theorem, and `byteEnvelope` against `Seal(K, η, M)`
  of `fig:games`, the envelope of SPEC §6.2 and §7.
* The PRF: `hmacPRF`, `PRFScheme.multiKey` and `prfAdvantage` against A4 and `def:prf`.
* The encoding: `sealEncoding` against the labelled hashes `TH("leanseal/v1/enc", K ‖ η)` and
  `TH("leanseal/v1/mac", K ‖ η)` of SPEC §7, beside the puzzle's hash inputs (SPEC §1, §3).
* The constants: `Valid` against SPEC §2, and `card_bytes` for the sizes `2^256`, `2^(8b)` and
  `2^128` of hashes, links, salts and 16-byte nonces, so `Q_enc² / (2 |N|) = Q_enc² / 2^129`.

Scope of every row: running time is not modelled, the PRF term is the advantage of the named
distinguisher `byteHidingDistinguisher`, and `hidingSecure_byteScheme`'s PRF premise covers all
byte-level adversaries (`hidingSecure_byteScheme_of_budget` only budgeted ones).

## Main statements

* `PointerChainPuzzle.LeanSeal.hidingAdvantage_byteScheme_eq`: the byte-level hiding advantage is
  the typed hiding advantage of the adapted adversary.
* `PointerChainPuzzle.LeanSeal.byteHidingDistinguisher`: the PRF distinguisher of the byte-level
  theorem.
* `PointerChainPuzzle.LeanSeal.hidingAdvantage_byteScheme_le`: the hiding theorem for leanSeal.
* `PointerChainPuzzle.LeanSeal.hidingSecure_byteScheme`,
  `PointerChainPuzzle.LeanSeal.hidingSecure_byteScheme_of_budget`: hiding security at the paper's
  constants.
* `PointerChainPuzzle.LeanSeal.cappedHidingAdvantage_byteScheme_le`: the hiding theorem in the
  paper's capped game.
* `PointerChainPuzzle.LeanSeal.hidingAdvantage_byteScheme_le_of_valid`,
  `PointerChainPuzzle.LeanSeal.hidingSecure_byteScheme_of_valid`,
  `PointerChainPuzzle.LeanSeal.cappedHidingAdvantage_byteScheme_le_of_valid`: the same under
  leanSeal's parameter check `Valid b n m`.
-/

public section

open OracleSpec OracleComp TimeLockPuzzle PRFScheme
open scoped ENNReal

namespace PointerChainPuzzle.LeanSeal

open Envelope

variable {b n : ℕ}

/-! ## The byte-level experiment against the typed one -/

/-- **The byte-level hiding experiment against the typed one.** For `b ≤ 32` and fewer than
`2^32` chains, the hiding advantage of a byte-level adversary against leanSeal's puzzle and byte
envelope over `byteSpec` is the typed hiding advantage of its adapted adversary against the
typed scheme with subkeys. -/
theorem hidingAdvantage_byteScheme_eq (hb : b ≤ 32) (hn : n < 2 ^ 32) (m : ℕ) [NeZero n]
    (adv : HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray) :
    hidingAdvantage (byteScheme b n m) (byteEnvelope b n m) plaintextLength adv =
      hidingAdvantage (typedSealScheme b n m) (typedSealDEM b n m) plaintextLength
        ((sealEncoding hb hn).adaptHidingAdversary adv) :=
  (sealEncoding hb hn).hidingAdvantage_eq_hidingAdvantage_adaptHidingAdversary plaintextLength
    (byteScheme_gen_eq hb hn m) (byteEnvelope_encrypt_eq hb hn m) (not_clash_sealEncoding hb hn)
    adv

/-- The PRF distinguisher of the byte-level hiding theorem: the typed distinguisher
`hidingDistinguisher` run on the adapted adversary. It runs the byte-level adversary, answering
its raw queries through the extended encoding and a private lazy random oracle, samples the typed
oracles itself, and forwards the keystream and tag evaluations of encryption `j` to PRF instances
`(0, j)` and `(1, j)`. -/
@[expose]
noncomputable def byteHidingDistinguisher (hb : b ≤ 32) (hn : n < 2 ^ 32) (m : ℕ) [NeZero n]
    (qEnc : ℕ) (adv : HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray) :
    PRFScheme.PRFAdversary (Fin (2 * qEnc) × ByteArray) (Bytes 32) :=
  hidingDistinguisher m (FixedCodec.bytes 16) (encode m) qEnc (ctx b n m) id
    ((sealEncoding hb hn).adaptHidingAdversary adv)

/-! ## The hiding theorem -/

/-- **The hiding theorem for leanSeal (the paper's `thm:hiding`, SPEC §8).** With SHA-256 one
random oracle on byte strings and HMAC-SHA256 computed outside it, for `b ≤ 32` and fewer than
`2^32` chains, a byte-level adversary with at most `Q_pre` preprocessing queries, an online phase
within `T_key - 1` rounds holding at most `Q_on` points, and at most `Q_enc` challenge queries has
hiding advantage at most
`2 ([n ≥ 2] Q_on / 2^(8b) + Q_pre / 2^(128+8b) + (Q P' + P'²) / 2^256 + Q_enc² / 2^129 + Adv^prf)`,
with `P' = P + 2 Q_enc` and `Adv^prf` the advantage of the explicit distinguisher
`byteHidingDistinguisher` against HMAC-SHA256 under `2 Q_enc` independent keys.

Scope: running time is not modelled. The bound is an explicit reduction: it names the PRF
distinguisher `byteHidingDistinguisher` but says nothing about its running time, so the paper's
time bound on the PRF adversary is not part of this statement. -/
theorem hidingAdvantage_byteScheme_le (hb : b ≤ 32) (hn : n < 2 ^ 32) (m : ℕ) [NeZero n]
    {adv : HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray} {Qpre Qon qEnc : ℕ}
    (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) (henc : adv.MakesAtMostQueries qEnc) :
    hidingAdvantage (byteScheme b n m) (byteEnvelope b n m) plaintextLength adv ≤
      2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * (solvePoints n m + 2 * qEnc) +
            ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 +
        prfAdvantage (hmacPRF.multiKey (Fin (2 * qEnc)))
          (byteHidingDistinguisher hb hn m qEnc adv)) := by
  rw [hidingAdvantage_byteScheme_eq hb hn m adv]
  exact hidingAdvantage_sealScheme_le_paper hmacPRF (FixedCodec.bytes 16) (encode m)
    hmacPRF_uniformKey (ctx b n m) id (ctx_injective b n m) (card_bytes 32) (card_bytes b)
    (card_bytes 16) (card_bytes 16)
    ((sealEncoding hb hn).isQueryBound_adaptTwoPhase hadv)
    ((sealEncoding hb hn).makesAtMostQueries_adaptHidingAdversary henc)

/-- **Hiding security of leanSeal at the paper's constants**, for every PRF bound `ε` that holds
for the distinguishers `byteHidingDistinguisher` of all byte-level adversaries.

Scope: the PRF premise quantifies over *all* byte-level adversaries, including those outside the
budgets, and running time is not modelled; the PRF term is the advantage of the named
distinguisher `byteHidingDistinguisher`. `hidingSecure_byteScheme_of_budget` assumes the PRF
bound only for adversaries within the budgets. -/
theorem hidingSecure_byteScheme (hb : b ≤ 32) (hn : n < 2 ^ 32) (m : ℕ) [NeZero n]
    (Qpre Qon qEnc : ℕ) {ε : ℝ≥0∞}
    (hε : ∀ adv : HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray,
      prfAdvantage (hmacPRF.multiKey (Fin (2 * qEnc))) (byteHidingDistinguisher hb hn m qEnc adv)
        ≤ ε) :
    HidingSecure (byteScheme b n m) (byteEnvelope b n m) plaintextLength Qpre
      (keyRound n m - 1, Qon) qEnc
      (2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * (solvePoints n m + 2 * qEnc) +
            ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 + ε)) :=
  fun adv hadv henc =>
    (hidingAdvantage_byteScheme_le hb hn m hadv henc).trans (by gcongr; exact hε adv)

/-- **Hiding security of leanSeal at the paper's constants, for budgeted adversaries**, for every
PRF bound `ε` that holds for the distinguishers `byteHidingDistinguisher` of the byte-level
adversaries within the budgets.

Scope: the PRF premise quantifies only over byte-level adversaries within the budgets, unlike
`hidingSecure_byteScheme`, whose premise covers all of them. Running time is still not modelled,
and the PRF term is the advantage of the named distinguisher `byteHidingDistinguisher`. -/
theorem hidingSecure_byteScheme_of_budget (hb : b ≤ 32) (hn : n < 2 ^ 32) (m : ℕ) [NeZero n]
    (Qpre Qon qEnc : ℕ) {ε : ℝ≥0∞}
    (hε : ∀ adv : HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray,
      adv.IsQueryBound Qpre (keyRound n m - 1, Qon) → adv.MakesAtMostQueries qEnc →
      prfAdvantage (hmacPRF.multiKey (Fin (2 * qEnc))) (byteHidingDistinguisher hb hn m qEnc adv)
        ≤ ε) :
    HidingSecure (byteScheme b n m) (byteEnvelope b n m) plaintextLength Qpre
      (keyRound n m - 1, Qon) qEnc
      (2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * (solvePoints n m + 2 * qEnc) +
            ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 + ε)) :=
  fun adv hadv henc =>
    (hidingAdvantage_byteScheme_le hb hn m hadv henc).trans (by gcongr; exact hε adv hadv henc)

/-! ## The paper's capped challenger -/

/-- **The hiding theorem for leanSeal in the paper's game.** With the paper's capped challenger
(`TimeLockPuzzle.cappedHidingAdvantage`), which answers every request beyond the `qEnc`-th
accepted one with `none`, no encryption budget is assumed: the bound of
`hidingAdvantage_byteScheme_le` holds, with the distinguisher built from the adapter
`adv.capChallenges plaintextLength qEnc`, which makes at most `qEnc` challenge queries and keeps
the round budgets (`TimeLockPuzzle.cappedHidingAdvantage_eq_hidingAdvantage_capChallenges`). -/
theorem cappedHidingAdvantage_byteScheme_le (hb : b ≤ 32) (hn : n < 2 ^ 32) (m : ℕ) [NeZero n]
    {adv : HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray} {Qpre Qon : ℕ} (qEnc : ℕ)
    (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) :
    (byteScheme b n m).cappedHidingAdvantage (byteEnvelope b n m) plaintextLength qEnc adv ≤
      2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * (solvePoints n m + 2 * qEnc) +
            ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 +
        prfAdvantage (hmacPRF.multiKey (Fin (2 * qEnc)))
          (byteHidingDistinguisher hb hn m qEnc (adv.capChallenges plaintextLength qEnc))) := by
  rw [cappedHidingAdvantage_eq_hidingAdvantage_capChallenges]
  exact hidingAdvantage_byteScheme_le hb hn m
    (HidingAdversary.isQueryBound_capChallenges hadv plaintextLength qEnc)
    (HidingAdversary.makesAtMostQueries_capChallenges adv plaintextLength qEnc)

/-! ## Every parameter set leanSeal accepts -/

/-- **The hiding theorem for leanSeal at every parameter set it accepts**: the bound of
`hidingAdvantage_byteScheme_le`, through `Valid.le_32` and `Valid.lt_two_pow_32`. -/
theorem hidingAdvantage_byteScheme_le_of_valid {m : ℕ} [NeZero n] (hv : Valid b n m)
    {adv : HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray} {Qpre Qon qEnc : ℕ}
    (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) (henc : adv.MakesAtMostQueries qEnc) :
    hidingAdvantage (byteScheme b n m) (byteEnvelope b n m) plaintextLength adv ≤
      2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * (solvePoints n m + 2 * qEnc) +
            ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 +
        prfAdvantage (hmacPRF.multiKey (Fin (2 * qEnc)))
          (byteHidingDistinguisher hv.le_32 hv.lt_two_pow_32 m qEnc adv)) :=
  hidingAdvantage_byteScheme_le hv.le_32 hv.lt_two_pow_32 m hadv henc

/-- **Hiding security of leanSeal at every parameter set it accepts**: `hidingSecure_byteScheme`
under `Valid b n m`, with the same scope. -/
theorem hidingSecure_byteScheme_of_valid {m : ℕ} [NeZero n] (hv : Valid b n m)
    (Qpre Qon qEnc : ℕ) {ε : ℝ≥0∞}
    (hε : ∀ adv : HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray,
      prfAdvantage (hmacPRF.multiKey (Fin (2 * qEnc)))
        (byteHidingDistinguisher hv.le_32 hv.lt_two_pow_32 m qEnc adv) ≤ ε) :
    HidingSecure (byteScheme b n m) (byteEnvelope b n m) plaintextLength Qpre
      (keyRound n m - 1, Qon) qEnc
      (2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * (solvePoints n m + 2 * qEnc) +
            ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 + ε)) :=
  hidingSecure_byteScheme hv.le_32 hv.lt_two_pow_32 m Qpre Qon qEnc hε

/-- **The hiding theorem for leanSeal in the paper's game, at every parameter set it accepts**:
`cappedHidingAdvantage_byteScheme_le` under `Valid b n m`, with no encryption budget. -/
theorem cappedHidingAdvantage_byteScheme_le_of_valid {m : ℕ} [NeZero n] (hv : Valid b n m)
    {adv : HidingAdversary byteSpec (Puzzle b n) Plaintext ByteArray} {Qpre Qon : ℕ} (qEnc : ℕ)
    (hadv : adv.IsQueryBound Qpre (keyRound n m - 1, Qon)) :
    (byteScheme b n m).cappedHidingAdvantage (byteEnvelope b n m) plaintextLength qEnc adv ≤
      2 * ((if 2 ≤ n then (Qon : ℝ≥0∞) / 2 ^ (8 * b) else 0) + Qpre / 2 ^ (128 + 8 * b) +
        ((Qpre + Qon) * (solvePoints n m + 2 * qEnc) +
            ((solvePoints n m + 2 * qEnc : ℕ) : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 +
        prfAdvantage (hmacPRF.multiKey (Fin (2 * qEnc)))
          (byteHidingDistinguisher hv.le_32 hv.lt_two_pow_32 m qEnc
            (adv.capChallenges plaintextLength qEnc))) :=
  cappedHidingAdvantage_byteScheme_le hv.le_32 hv.lt_two_pow_32 m qEnc hadv

end PointerChainPuzzle.LeanSeal
