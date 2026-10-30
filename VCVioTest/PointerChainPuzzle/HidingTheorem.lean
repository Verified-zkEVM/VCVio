/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingTheorem

/-!
# Time-lock encryption with the pointer-chain puzzle: checks of the hiding theorem

Checks through the public API:

* the four hiding theorems depend on the standard axioms only;
* the hiding theorem with the paper's constants, for two chains of one step (`n = 2`, `m = 1`,
  so `P = 9`) with one-byte links (`b = 1`), over `S = Fin (2^256)`, `L = Fin (2^8)`,
  `Salt = Ctx = N = Fin (2^128)`, PRF keys `K = Fin 7` and a toy PRF, at a concrete adversary with
  no preprocessing, no round and one challenge query: its hiding advantage is at most
  `2 (11² / 2^256 + 1 / 2^129 + ε)`, with `ε` the PRF advantage of its distinguisher.

The answer types are sampled through `SampleableType.Fin`, so loading this module enumerates no
type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle PointerChainPuzzle.LeanSeal
  PointerChainPuzzle.LeanSeal.Envelope PRFScheme
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.HidingTheorem

/-! ## Axioms -/

-- `#print axioms` of the four theorems: the standard axioms only.

/--
info: 'PointerChainPuzzle.hidingAdvantage_sealScheme_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingAdvantage_sealScheme_le

/--
info: 'PointerChainPuzzle.hidingAdvantage_sealScheme_le_paper' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingAdvantage_sealScheme_le_paper

/--
info: 'PointerChainPuzzle.hidingSecure_sealScheme' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hidingSecure_sealScheme

/--
info: 'PointerChainPuzzle.cappedHidingAdvantage_sealScheme_le_paper' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cappedHidingAdvantage_sealScheme_le_paper

/-! ## The paper's constants at a concrete adversary -/

/-- States are `Fin (2^256)`. -/
abbrev S := Fin (2 ^ 256)

/-- Links are one byte, `Fin (2^8)`. -/
abbrev L := Fin (2 ^ (8 * 1))

/-- Salts and contexts are `Fin (2^128)`. -/
abbrev Salt := Fin (2 ^ 128)

/-- Nonces are `Fin (2^128)`. -/
abbrev N := Fin (2 ^ 128)

/-- PRF keys are `Fin 7`. -/
abbrev K := Fin 7

/-- The oracles with subkeys at these parameters. -/
abbrev spec := sealSpec 2 S L Salt Salt N K

/-- A toy PRF: byte `i` of `eval k x` is `k + |x| + i`. -/
@[expose]
def toyPRF : PRFScheme K ByteArray (Bytes 32) where
  keygen := $ᵗ K
  eval k x := ⟨Vector.ofFn fun i => (k.val + x.size + i.val).toUInt8⟩

/-- The toy PRF draws its key uniformly. -/
theorem toyPRF_uniformKey : toyPRF.UniformKey :=
  rfl

/-- The initial accumulator of a context: the context itself, as a state. -/
def initAcc (ctx : Salt) : S := Fin.castLE (Nat.pow_le_pow_right (by decide) (by decide)) ctx

/-- The one-byte message `[1]`. -/
@[expose]
def msgA : Plaintext := ⟨⟨#[1]⟩, by decide⟩

/-- The one-byte message `[2]`. -/
@[expose]
def msgB : Plaintext := ⟨⟨#[2]⟩, by decide⟩

/-- No preprocessing; the online phase asks one challenge on `msgA` and `msgB`, submits no round,
and guesses whether the first byte of the ciphertext is even. -/
def hidingAdv : TimeLockPuzzle.HidingAdversary spec (Puzzle 2 S L Salt) Plaintext ByteArray where
  State := Unit
  preprocess := pure ()
  online _ _ := do
    let c ← liftM (((unifSpec + LeftOrRight.spec Plaintext ByteArray) + spec.batch).query
      (.inl (.inr (msgA, msgB))))
    return ((c.getD ByteArray.empty).data.toList.headD 0).toNat % 2 == 0

/-- The adversary makes no preprocessing query and no round; the challenge is free. -/
lemma hidingAdv_isQueryBound : hidingAdv.IsQueryBound 0 (keyRound 2 1 - 1, 0) :=
  ⟨trivial, fun _ _ => (isOnlineQueryBound_query_bind_inl_iff _ _ _).2 fun _ =>
    isOnlineQueryBound_pure _ _⟩

/-- The adversary makes one challenge query. -/
lemma hidingAdv_makesAtMostQueries : hidingAdv.MakesAtMostQueries 1 := by
  intro σ puzzle
  simp [hidingAdv]

variable {w : ℕ} (codec : FixedCodec N w) (encodePuzzle : Puzzle 2 S L Salt → ByteArray)

/-- **The hiding theorem with the paper's constants at small parameters.** With `P = 9`, `b = 1`,
no preprocessing query, no online point and one challenge query, `P' = 11` and the hiding
advantage of `hidingAdv` is at most `2 (11² / 2^256 + 1 / 2^129 + ε)`. -/
theorem hidingAdvantage_hidingAdv_le :
    TimeLockPuzzle.hidingAdvantage (sealScheme 2 1 id initAcc N K)
        (sealDEM toyPRF codec encodePuzzle) plaintextLength hidingAdv ≤
      2 * (11 ^ 2 / 2 ^ 256 + 1 / 2 ^ 129 +
        prfAdvantage (toyPRF.multiKey (Fin (2 * 1)))
          (hidingDistinguisher 1 codec encodePuzzle 1 id initAcc hidingAdv)) := by
  have h := hidingAdvantage_sealScheme_le_paper (m := 1) toyPRF codec encodePuzzle
    toyPRF_uniformKey id initAcc Function.injective_id (b := 1) (Fintype.card_fin _)
    (Fintype.card_fin _) (Fintype.card_fin _) (Fintype.card_fin _) hidingAdv_isQueryBound
    hidingAdv_makesAtMostQueries
  have hP : solvePoints 2 1 + 2 * 1 = 11 := rfl
  simpa [hP] using h

end VCVioTest.PointerChainPuzzle.HidingTheorem
