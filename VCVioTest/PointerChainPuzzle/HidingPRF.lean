/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingPRF

/-!
# Time-lock encryption with the pointer-chain puzzle: checks of the indexed hybrid

Checks through the public API, for two chains of one step (`n = 2`, `m = 1`) over `S = Fin 11`,
`L = Fin 5`, `Salt = Ctx = Fin 3`, nonces `N = Fin 4` with a one-byte codec, PRF keys `K = Fin 7`
and a toy PRF:

* `sealWith_eq_sealBy` at a message of 33 bytes, two keystream blocks: `sealBy` with logging PRF
  evaluations gives the envelope of `sealWith`, evaluates the keystream at `be 8 0` and `be 8 1`
  only, and then the tag once;
* traces of the indexed challenger against a logging table of instances: a pair of messages of
  unequal length is answered with `none`, leaves the counter unchanged and queries no instance; an
  accepted pair below the budget advances the counter, queries instance `(0, j)` at `be 8 0` and
  then instance `(1, j)`, and is answered by the envelope of `sealWith` under the keys of these
  instances; an accepted pair beyond the budget advances the counter, is answered by the empty
  byte string and queries no instance;
* the two normalization theorems at a concrete hiding adversary.

The answer types are sampled through `SampleableType.Fin`, so loading this module enumerates no
type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle PointerChainPuzzle.LeanSeal
  PointerChainPuzzle.LeanSeal.Envelope PRFScheme
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.HidingPRF

/-- States are `Fin 11`. -/
abbrev S := Fin 11

/-- Links are `Fin 5`. -/
abbrev L := Fin 5

/-- Salts and contexts are `Fin 3`. -/
abbrev Salt := Fin 3

/-- Nonces are `Fin 4`. -/
abbrev N := Fin 4

/-- PRF keys are `Fin 7`. -/
abbrev K := Fin 7

/-- The oracles with subkeys at these parameters. -/
abbrev spec := sealSpec 2 S L Salt Salt N K

/-- Nonces are encoded as one byte. -/
@[expose]
def codec : FixedCodec N 1 where
  encode x := ⟨#v[x.val.toUInt8]⟩
  decode y := if h : y.toVector[0].toNat < 4 then some ⟨_, h⟩ else none
  decode_encode x := by fin_cases x <;> rfl

/-- A toy PRF: byte `i` of `eval k x` is `k + |x| + x₀ + i`, with `x₀` the first byte of `x`. -/
@[expose]
def toyPRF : PRFScheme K ByteArray (Bytes 32) where
  keygen := $ᵗ K
  eval k x :=
    ⟨Vector.ofFn fun i => (k.val + x.size + (x.data.toList.headD 0).toNat + i.val).toUInt8⟩

/-- The puzzle bytes `[7, 7]`. -/
@[expose]
def pz : ByteArray := ⟨#[7, 7]⟩

/-! ## `sealBy` at two keystream blocks -/

/-- A message of 33 bytes, `0, 1, …, 32`: two keystream blocks. -/
@[expose]
def msg33 : Plaintext := ⟨⟨((List.range 33).map Nat.toUInt8).toArray⟩, by decide⟩

/-- The toy PRF under the key `k`, logging every input. -/
@[expose]
def logPRF (k : K) (x : ByteArray) : StateM (List ByteArray) (Bytes 32) := do
  modify (· ++ [x])
  pure (toyPRF.eval k x)

/-- `sealWith_eq_sealBy` at the 33-byte message. -/
example : sealWith toyPRF codec pz 3 (2, 5) msg33 =
    (sealBy codec (fun x => pure (toyPRF.eval 2 x)) (fun x => pure (toyPRF.eval 5 x)) pz 3 msg33 :
      Id ByteArray).run :=
  sealWith_eq_sealBy toyPRF codec pz 3 (2, 5) msg33

/-- With logging evaluations, `sealBy` at the 33-byte message gives the envelope of `sealWith`,
evaluates the keystream exactly at `be 8 0` and `be 8 1`, then the tag once, at the signed bytes. -/
theorem sealBy_logPRF_msg33 :
    (sealBy codec (logPRF 2) (logPRF 5) pz 3 msg33).run [] =
      (sealWith toyPRF codec pz 3 (2, 5) msg33,
        [be 8 0, be 8 1, ⟨(signedBytes codec pz 3
          (xorBytes msg33.1.data.toList (keystream toyPRF 2 33))).toArray⟩]) :=
  rfl

/-- The envelope of the 33-byte message has `8 + 2 + 1 + 4 + 33 + 32 = 80` bytes. -/
example : (sealWith toyPRF codec pz 3 (2, 5) msg33).size = 80 := by
  decide

/-! ## Traces of the indexed challenger -/

/-- The key of instance `i` in the traces: `i + 2` modulo `7`. -/
@[expose]
def instKey (i : ℕ) : K := ⟨(i + 2) % 7, Nat.mod_lt _ (by decide)⟩

/-- Answers local coins with `0`, the oracles with subkeys from the table `g`, and instance `i` at
`x` with `toyPRF.eval (instKey i) x`, logging every instance query. -/
@[expose]
def traceImpl (qEnc : ℕ) (g : QueryImpl spec Id) :
    QueryImpl (indexedSpec 2 S L Salt Salt N K qEnc)
      (StateM (List (Fin (2 * qEnc) × ByteArray)))
  | .inl n => pure (0 : Fin (n + 1))
  | .inr (.inl t) => pure (g t)
  | .inr (.inr (i, x)) => do
      modify (· ++ [(i, x)])
      pure (toyPRF.eval (instKey i) x)

/-- The challenge oracle of the indexed hybrid at hidden bit `b` on the pair `mm`, from the counter
`j`, against `traceImpl`: the answer, the new counter and the log of instance queries. -/
@[expose]
def challengeTrace (qEnc : ℕ) (g : QueryImpl spec Id) (b : Bool)
    (mm : Plaintext × Plaintext) (j : ℕ) :
    (Option ByteArray × ℕ) × List (Fin (2 * qEnc) × ByteArray) :=
  (simulateQ (traceImpl qEnc g)
    ((LeftOrRight.oracle (indexedEncrypt (n := 2) (S := S) (L := L) (Salt := Salt) (Ctx := Salt)
      (K := K) codec qEnc pz) plaintextLength b mm).run j)).run []

/-- The one-byte message `[1]`. -/
@[expose]
def msgA : Plaintext := ⟨⟨#[1]⟩, by decide⟩

/-- The one-byte message `[2]`. -/
@[expose]
def msgB : Plaintext := ⟨⟨#[2]⟩, by decide⟩

/-- The two-byte message `[1, 2]`. -/
@[expose]
def msgC : Plaintext := ⟨⟨#[1, 2]⟩, by decide⟩

/-- A pair of messages of unequal length is answered with `none`, leaves the counter unchanged and
queries no instance, at every budget, hidden bit and counter. -/
theorem challengeTrace_unequal (qEnc : ℕ) (g : QueryImpl spec Id) (b : Bool) (j : ℕ) :
    challengeTrace qEnc g b (msgA, msgC) j = ((none, j), []) :=
  rfl

/-- With budget `1`, the first accepted pair advances the counter to `1`, queries instance `(0, 0)`
at `be 8 0` and then instance `(1, 0)`, and is answered by the envelope of `sealWith` under the
keys `instKey 0` and `instKey 1` of these instances, with the nonce `0` the coins give: of `msgB`
at hidden bit `true`. -/
theorem challengeTrace_accepted (g : QueryImpl spec Id) :
    let r := challengeTrace 1 g true (msgA, msgB) 0
    r.1 = (some (sealWith toyPRF codec pz 0 (instKey 0, instKey 1) msgB), 1) ∧
      r.2.map Prod.fst = [instanceIndex 0 0, instanceIndex 1 0] ∧
      (r.2.head?.map Prod.snd) = some (be 8 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- The same pair at hidden bit `false` is answered by the envelope of `msgA`. -/
theorem challengeTrace_accepted_false (g : QueryImpl spec Id) :
    (challengeTrace 1 g false (msgA, msgB) 0).1 =
      (some (sealWith toyPRF codec pz 0 (instKey 0, instKey 1) msgA), 1) :=
  rfl

/-- With budget `1`, an accepted pair after the first advances the counter, is answered by the empty
byte string and queries no instance. -/
theorem challengeTrace_overBudget (g : QueryImpl spec Id) (b : Bool) :
    challengeTrace 1 g b (msgA, msgB) 1 = ((some ByteArray.empty, 2), []) := by
  cases b <;> rfl

/-- The keystream and tag instances of the single encryption at budget `1` are `0` and `1`. -/
example : (instanceIndex 0 (0 : Fin 1), instanceIndex 1 (0 : Fin 1)) = (0, 1) := by
  decide

/-! ## Normalization at a concrete adversary -/

/-- The context of a salt. -/
def mkCtx (salt : Salt) : Salt := salt + 1

/-- The initial accumulator of a context. -/
def initAcc (ctx : Salt) : S := ⟨ctx.val + 6, by omega⟩

/-- No preprocessing; the online phase asks one challenge on `msgA` and `msgB` and guesses whether
the first byte of the ciphertext is even. -/
def hidingAdv : TimeLockPuzzle.HidingAdversary spec (Puzzle 2 S L Salt) Plaintext ByteArray where
  State := Unit
  preprocess := pure ()
  online _ _ := do
    let c ← liftM (((unifSpec + LeftOrRight.spec Plaintext ByteArray) + spec.batch).query
      (.inl (.inr (msgA, msgB))))
    return ((c.getD ByteArray.empty).data.toList.headD 0).toNat % 2 == 0

variable (encodePuzzle : Puzzle 2 S L Salt → ByteArray)

/-- Real-world normalization for `hidingAdv` at budget `1`, against independent toy PRF keys. -/
example :
    Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
        (hidingDistinguisher 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv))}[g = true] =
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
          (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv true))}[g = true] +
        (1 - Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
          (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv false))}[g = true])) / 2 :=
  prfRealExperiment_hidingDistinguisher codec encodePuzzle 1 mkCtx initAcc hidingAdv toyPRF

/-- Ideal-world normalization for `hidingAdv` at budget `1`. -/
example :
    Pr{let g ← (prfIdealExperiment
        (hidingDistinguisher 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv))}[g = true] =
      (Pr{let g ← (prfIdealExperiment
          (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv true))}[g = true] +
        (1 - Pr{let g ← (prfIdealExperiment
          (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv false))}[g = true])) / 2 :=
  prfIdealExperiment_hidingDistinguisher codec encodePuzzle 1 mkCtx initAcc hidingAdv

end VCVioTest.PointerChainPuzzle.HidingPRF
