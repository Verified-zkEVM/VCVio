/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSealHiding

/-!
# The hiding theorem for leanSeal: checks

Checks of the byte-level hiding theorem through its public API:

* every theorem of the byte-level hiding development depends on the standard axioms only;
* the corollary under `Valid` at the parameters of the round table of leanSeal's security notes
  (`n = 3` chains of `m = 2` steps) with leanSeal's default link width `b = 24`, the parameter
  check discharged by `decide`: an adversary within `12` online rounds has hiding advantage at most
  `2 (Q_on / 2^192 + Q_pre / 2^320 + ((Q_pre + Q_on) (16 + 2 Q_enc) + (16 + 2 Q_enc)²) / 2^256
  + Q_enc² / 2^129 + Adv^PRF)`.

No declaration of this module enumerates a type when the module is loaded.
-/

public section

open OracleComp OracleSpec TimeLockPuzzle PRFScheme PointerChainPuzzle PointerChainPuzzle.LeanSeal
  PointerChainPuzzle.LeanSeal.Envelope
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.LeanSealHiding

/-! ## Axioms -/

-- `#print axioms` of the byte-level hiding theorems: the standard axioms only.

/--
info: 'PointerChainPuzzle.LeanSeal.hidingAdvantage_byteScheme_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingAdvantage_byteScheme_eq

/--
info: 'PointerChainPuzzle.LeanSeal.hidingAdvantage_byteScheme_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingAdvantage_byteScheme_le

/--
info: 'PointerChainPuzzle.LeanSeal.hidingSecure_byteScheme' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingSecure_byteScheme

/--
info: 'PointerChainPuzzle.LeanSeal.hidingSecure_byteScheme_of_budget' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingSecure_byteScheme_of_budget

/--
info: 'PointerChainPuzzle.LeanSeal.cappedHidingAdvantage_byteScheme_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cappedHidingAdvantage_byteScheme_le

/--
info: 'PointerChainPuzzle.LeanSeal.hidingAdvantage_byteScheme_le_of_valid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingAdvantage_byteScheme_le_of_valid

/--
info: 'PointerChainPuzzle.LeanSeal.hidingSecure_byteScheme_of_valid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingSecure_byteScheme_of_valid

/--
info: 'PointerChainPuzzle.LeanSeal.cappedHidingAdvantage_byteScheme_le_of_valid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cappedHidingAdvantage_byteScheme_le_of_valid

/-! ## The round table of leanSeal's security notes, with 24-byte links -/

/-- Three chains of two steps with 24-byte links pass leanSeal's parameter check. -/
theorem valid_24_3_2 : Valid 24 3 2 := by decide

/-- **The hiding theorem at `n = 3`, `m = 2`, `b = 24`**, through the corollary under `Valid`:
the key is derived in round `13` and the solver uses `16` answers, so an adversary within `12`
online rounds has hiding advantage at most
`2 (Q_on / 2^192 + Q_pre / 2^320 + ((Q_pre + Q_on) (16 + 2 Q_enc) + (16 + 2 Q_enc)²) / 2^256
+ Q_enc² / 2^129 + Adv^PRF)`. -/
theorem hidingAdvantage_byteScheme_24_3_2_le
    {adv : HidingAdversary byteSpec (Puzzle 24 3) Plaintext ByteArray} {Qpre Qon qEnc : ℕ}
    (hadv : adv.IsQueryBound Qpre (12, Qon)) (henc : adv.MakesAtMostQueries qEnc) :
    hidingAdvantage (byteScheme 24 3 2) (byteEnvelope 24 3 2) plaintextLength adv ≤
      2 * ((Qon : ℝ≥0∞) / 2 ^ 192 + Qpre / 2 ^ 320 +
        ((Qpre + Qon) * (16 + 2 * qEnc) + (16 + 2 * qEnc : ℝ≥0∞) ^ 2) / 2 ^ 256 +
        (qEnc : ℝ≥0∞) ^ 2 / 2 ^ 129 +
        prfAdvantage (hmacPRF.multiKey (Fin (2 * qEnc)))
          (byteHidingDistinguisher valid_24_3_2.le_32 valid_24_3_2.lt_two_pow_32 2 qEnc adv)) := by
  have hP : solvePoints 3 2 = 16 := rfl
  have hK : keyRound 3 2 - 1 = 12 := rfl
  have h := hidingAdvantage_byteScheme_le_of_valid valid_24_3_2 (hK ▸ hadv) henc
  simpa [hP] using h

/--
info: 'VCVioTest.PointerChainPuzzle.LeanSealHiding.hidingAdvantage_byteScheme_24_3_2_le' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingAdvantage_byteScheme_24_3_2_le

end VCVioTest.PointerChainPuzzle.LeanSealHiding
