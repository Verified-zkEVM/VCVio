/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingIdeal
public import VCVioTest.PointerChainPuzzle.HidingPRF

/-!
# Time-lock encryption with the pointer-chain puzzle: checks of the ideal PRF world

Checks through the public API, at the parameters, toy PRF and concrete hiding adversary of
`VCVioTest.PointerChainPuzzle.HidingPRF`:

* the keystream block counters of a 70-byte message, three blocks, are the distinct points
  `be 8 0`, `be 8 1` and `be 8 2` of the stream instance;
* independence of the hidden bit in the ideal world and the PRF step, at budgets `1` and `2`,
  for `hidingAdv` and for test-local adversaries that read the first ciphertext byte of their
  answers, at offset `8 + pz.size + 1 + 4` of the envelope: one request at budget `1`, two
  accepted requests at budget `2`;
* under fixed keys that byte is the message byte XORed with the first keystream byte, so its
  parity differs between `msgA` and `msgB`;
* a trace of two accepted requests at budget `2`: the second encryption queries its own stream
  and tag instances `(0, 1)` and `(1, 1)`, again from the stream point `be 8 0`, and is sealed
  under their keys.

Loading this module enumerates no type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle PointerChainPuzzle.LeanSeal
  PointerChainPuzzle.LeanSeal.Envelope PRFScheme
open VCVioTest.PointerChainPuzzle.HidingPRF
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.HidingIdeal

/-! ## The stream points of a multi-block message -/

/-- A message of 70 zero bytes: three keystream blocks. -/
@[expose]
def msg70 : Plaintext := ⟨⟨Array.replicate 70 0⟩, by decide⟩

/-- The 70-byte message has three keystream blocks. -/
theorem numBlocks_msg70 : (msg70.1.size + 31) / 32 = 3 := rfl

/-- The stream instance of an encryption of the 70-byte message is queried at three distinct
points. -/
theorem nodup_streamPoints_msg70 : [be 8 0, be 8 1, be 8 2].Nodup :=
  nodup_map_be_range msg70

/-! ## The ideal world and the PRF step at budgets `1` and `2` -/

variable (encodePuzzle : Puzzle 2 S L Salt → ByteArray)

/-- In the ideal world, `hidingAdv` against the indexed run at budget `1` outputs `true` with the
same probability at both hidden bits. -/
theorem prfIdealExperiment_indexedRun_one :
    Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv true))}[g = true] =
      Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv false))}[g = true] :=
  prfIdealExperiment_indexedRun_true_eq_false codec encodePuzzle 1 mkCtx initAcc hidingAdv

/-- In the ideal world, `hidingAdv` against the indexed run at budget `2` outputs `true` with the
same probability at both hidden bits. -/
theorem prfIdealExperiment_indexedRun_two :
    Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv true))}[g = true] =
      Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv false))}[g = true] :=
  prfIdealExperiment_indexedRun_true_eq_false codec encodePuzzle 2 mkCtx initAcc hidingAdv

/-- The PRF step for `hidingAdv` at budget `1`, against independent toy PRF keys. -/
theorem absDiff_indexed_le_prfAdvantage_one :
    ENNReal.absDiff
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv true))}[g = true])
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv false))}[g = true]) ≤
      2 * (toyPRF.multiKey (Fin (2 * 1))).prfAdvantage
        (hidingDistinguisher 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv) :=
  absDiff_indexed_le_prfAdvantage codec encodePuzzle 1 mkCtx initAcc hidingAdv toyPRF

/-- The PRF step for `hidingAdv` at budget `2`, against independent toy PRF keys. -/
theorem absDiff_indexed_le_prfAdvantage_two :
    ENNReal.absDiff
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 2))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv true))}[g = true])
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 2))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv false))}[g = true]) ≤
      2 * (toyPRF.multiKey (Fin (2 * 2))).prfAdvantage
        (hidingDistinguisher 1 codec encodePuzzle 2 mkCtx initAcc hidingAdv) :=
  absDiff_indexed_le_prfAdvantage codec encodePuzzle 2 mkCtx initAcc hidingAdv toyPRF

/-! ## Adversaries that read the ciphertext -/

/-- The byte of the envelope `c` at offset `8 + pz.size + 1 + 4`: past the header, the puzzle bytes
`pz`, the one-byte nonce and the length field, the first ciphertext byte. -/
@[expose]
def payloadByte (pz c : ByteArray) : UInt8 :=
  c.data.toList.getD (8 + pz.size + 1 + 4) 0

/-- Under fixed keys, the first ciphertext byte of the envelope of `msgB` is `2` XORed with the
first keystream byte. -/
theorem payloadByte_sealWith_msgB :
    payloadByte pz (sealWith toyPRF codec pz 0 (instKey 2, instKey 3) msgB) =
      2 ^^^ (toyPRF.eval (instKey 2) (be 8 0)).toList.headD 0 := by
  decide

/-- Under fixed keys, the parity of the first ciphertext byte tells `msgA` from `msgB`. -/
theorem payloadByte_sealWith_parity_ne :
    (payloadByte pz (sealWith toyPRF codec pz 0 (instKey 2, instKey 3) msgA)).toNat % 2 ≠
      (payloadByte pz (sealWith toyPRF codec pz 0 (instKey 2, instKey 3) msgB)).toNat % 2 := by
  decide

/-- One challenge on `msgA` and `msgB`. -/
@[expose]
def challengeAB :
    OracleComp ((unifSpec + LeftOrRight.spec Plaintext ByteArray) + spec.batch)
      (Option ByteArray) :=
  liftM (((unifSpec + LeftOrRight.spec Plaintext ByteArray) + spec.batch).query
    (.inl (.inr (msgA, msgB))))

/-- No preprocessing; the online phase asks one challenge on `msgA` and `msgB` and guesses
whether the first ciphertext byte of the answer, under the puzzle's bytes, is even. -/
@[expose]
def payloadAdv₁ :
    TimeLockPuzzle.HidingAdversary spec (Puzzle 2 S L Salt) Plaintext ByteArray where
  State := Unit
  preprocess := pure ()
  online _ puzzle := do
    let c ← challengeAB
    return (payloadByte (encodePuzzle puzzle) (c.getD ByteArray.empty)).toNat % 2 == 0

/-- No preprocessing; the online phase asks two challenges on `msgA` and `msgB` and guesses
whether the first ciphertext bytes of the two answers, under the puzzle's bytes, have even XOR. -/
@[expose]
def payloadAdv₂ :
    TimeLockPuzzle.HidingAdversary spec (Puzzle 2 S L Salt) Plaintext ByteArray where
  State := Unit
  preprocess := pure ()
  online _ puzzle := do
    let c₁ ← challengeAB
    let c₂ ← challengeAB
    return (payloadByte (encodePuzzle puzzle) (c₁.getD ByteArray.empty) ^^^
      payloadByte (encodePuzzle puzzle) (c₂.getD ByteArray.empty)).toNat % 2 == 0

/-- In the ideal world, `payloadAdv₁` at budget `1` outputs `true` with the same probability at
both hidden bits. -/
theorem prfIdealExperiment_indexedRun_payloadAdv₁ :
    Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc (payloadAdv₁ encodePuzzle) true))}[
          g = true] =
      Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc (payloadAdv₁ encodePuzzle) false))}[
          g = true] :=
  prfIdealExperiment_indexedRun_true_eq_false codec encodePuzzle 1 mkCtx initAcc _

/-- In the ideal world, `payloadAdv₂`, with its two accepted requests at budget `2`, outputs
`true` with the same probability at both hidden bits. -/
theorem prfIdealExperiment_indexedRun_payloadAdv₂ :
    Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc (payloadAdv₂ encodePuzzle) true))}[
          g = true] =
      Pr{let g ← (prfIdealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc (payloadAdv₂ encodePuzzle) false))}[
          g = true] :=
  prfIdealExperiment_indexedRun_true_eq_false codec encodePuzzle 2 mkCtx initAcc _

/-- The PRF step for `payloadAdv₁` at budget `1`, against independent toy PRF keys. -/
theorem absDiff_indexed_le_prfAdvantage_payloadAdv₁ :
    ENNReal.absDiff
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc (payloadAdv₁ encodePuzzle) true))}[
          g = true])
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc (payloadAdv₁ encodePuzzle) false))}[
          g = true]) ≤
      2 * (toyPRF.multiKey (Fin (2 * 1))).prfAdvantage
        (hidingDistinguisher 1 codec encodePuzzle 1 mkCtx initAcc (payloadAdv₁ encodePuzzle)) :=
  absDiff_indexed_le_prfAdvantage codec encodePuzzle 1 mkCtx initAcc _ toyPRF

/-- The PRF step for `payloadAdv₂` at budget `2`, against independent toy PRF keys. -/
theorem absDiff_indexed_le_prfAdvantage_payloadAdv₂ :
    ENNReal.absDiff
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 2))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc (payloadAdv₂ encodePuzzle) true))}[
          g = true])
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 2))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 2 mkCtx initAcc (payloadAdv₂ encodePuzzle) false))}[
          g = true]) ≤
      2 * (toyPRF.multiKey (Fin (2 * 2))).prfAdvantage
        (hidingDistinguisher 1 codec encodePuzzle 2 mkCtx initAcc (payloadAdv₂ encodePuzzle)) :=
  absDiff_indexed_le_prfAdvantage codec encodePuzzle 2 mkCtx initAcc _ toyPRF

/-! ## Two accepted requests -/

/-- Two challenges of the indexed hybrid at hidden bit `b`, on the pairs `mm₁` and `mm₂`, from the
counter `0`, against `traceImpl`: the two answers, the new counter and the log of instance
queries. -/
@[expose]
def twoChallengeTrace (qEnc : ℕ) (g : QueryImpl spec Id) (b : Bool)
    (mm₁ mm₂ : Plaintext × Plaintext) :
    ((Option ByteArray × Option ByteArray) × ℕ) × List (Fin (2 * qEnc) × ByteArray) :=
  let O := LeftOrRight.oracle (indexedEncrypt (n := 2) (S := S) (L := L) (Salt := Salt)
    (Ctx := Salt) (K := K) codec qEnc pz) plaintextLength b
  (simulateQ (traceImpl qEnc g) ((do
    let c₁ ← O mm₁
    let c₂ ← O mm₂
    return (c₁, c₂)).run 0)).run []

/-- With budget `2`, two accepted pairs advance the counter to `2`. The first is sealed under the
keys of instances `(0, 0)` and `(1, 0)`, and the second under the keys of its own instances
`(0, 1)` and `(1, 1)`; the four instances are queried in this order, they are distinct, and the
second stream instance is again first queried at `be 8 0`. -/
theorem twoChallengeTrace_accepted (g : QueryImpl spec Id) :
    let r := twoChallengeTrace 2 g true (msgA, msgB) (msgA, msgB)
    r.1 = ((some (sealWith toyPRF codec pz 0
          (instKey (instanceIndex (qEnc := 2) 0 0), instKey (instanceIndex (qEnc := 2) 1 0)) msgB),
        some (sealWith toyPRF codec pz 0
          (instKey (instanceIndex (qEnc := 2) 0 1), instKey (instanceIndex (qEnc := 2) 1 1)) msgB)),
        2) ∧
      r.2.map Prod.fst = [instanceIndex 0 0, instanceIndex 1 0, instanceIndex 0 1,
        instanceIndex 1 1] ∧
      (r.2.map Prod.fst).Nodup ∧
      (r.2.map Prod.snd)[2]? = some (be 8 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact (by decide : [instanceIndex (qEnc := 2) 0 0, instanceIndex 1 0, instanceIndex 0 1,
      instanceIndex 1 1].Nodup)
  · rfl

end VCVioTest.PointerChainPuzzle.HidingIdeal
