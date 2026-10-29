/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Envelope
public import VCVio.Schemes.PointerChainPuzzle.LeanSealBridge

/-!
# The leanSeal envelope over bytes

leanSeal's envelope (SPEC §6.2 and §7) is the envelope of
`VCVio/Schemes/PointerChainPuzzle/Envelope.lean` with its three primitives instantiated over
bytes:

* the subkeys `k_enc = TH("leanseal/v1/enc", K ‖ nonce)` and `k_mac = TH("leanseal/v1/mac",
  K ‖ nonce)`, two queries to the single oracle `byteSpec` (`subkeysQuery`), or the labelled
  hashes at a byte-answer function `h` (`subkeys`);
* HMAC-SHA256 as the PRF (`hmacPRF`), computed outside the oracle;
* the puzzle encoding of SPEC §6.1 (`encode`);
* 16-byte nonces, encoded as themselves (`FixedCodec.bytes 16`).

Opening trusts the puzzle bytes and the key it is given. SPEC-conforming use opens under an
already validated puzzle encoding (`decode`) and a key accepted against the puzzle's commitment
(`solveBytes` checks it), and rejection checks the envelope relative to those values; opening
decodes no puzzle and checks no commitment.

`hmacPRF` lives here rather than beside `Sha2.hmacSha256` because its key and output type
`Bytes` is the fixed-width byte type of leanSeal's encoding (`LeanSeal.lean`); the security
statement assumes it is a PRF (`prfAdvantage (hmacPRF.multiKey U)`), not derived from the random
oracle.

## Main definitions

* `PointerChainPuzzle.LeanSeal.hmacPRF`: HMAC-SHA256 as a `PRFScheme` with uniform 32-byte keys.
* `PointerChainPuzzle.LeanSeal.sealBytes`, `openBytes`: sealing and opening at a byte-answer
  function `h`, the executable envelope at `h = sha256`.
* `PointerChainPuzzle.LeanSeal.byteEnvelope`: the envelope as a DEM over `byteSpec`, keyed by a
  puzzle with its key, the `dem` argument of `TimeLockPuzzle.hidingExperiment` for `byteScheme`.

## Main statements

* `openBytes_sealBytes`: opening a sealed envelope under the same puzzle bytes and key returns the
  message, for every nonce and every byte-answer function.
* `simulateQ_byteEnvelope_encrypt`, `simulateQ_byteEnvelope_decrypt`: with the oracle answered by
  `h`, the DEM seals with `sealBytes` at `h` under a uniform nonce and opens with `openBytes`.
* `byteEnvelope_perfectlyCorrect`, `byteEnvelope_perfectlyCorrect_rom`: the DEM is perfectly
  correct with the oracle answered by any byte-answer function, and in the random oracle model.
-/

public section

open OracleSpec OracleComp VCVio.Algorithms

namespace PointerChainPuzzle.LeanSeal

open Envelope

/-! ## HMAC-SHA256 as a PRF -/

/-- HMAC-SHA256 under a 32-byte key. -/
@[expose]
def hmac (k : Bytes 32) (x : ByteArray) : Bytes 32 :=
  ⟨⟨(Sha2.hmacSha256 k.toByteArray x).data, by
    change (Sha2.hmacSha256 k.toByteArray x).size = 32
    unfold Sha2.hmacSha256
    exact Sha2.sha256_size _⟩⟩

/-- HMAC-SHA256 as a PRF with uniform 32-byte keys, inputs of any length and 32-byte outputs. -/
@[expose]
def hmacPRF : PRFScheme (Bytes 32) ByteArray (Bytes 32) where
  keygen := $ᵗ Bytes 32
  eval := hmac

/-- `hmacPRF` draws its keys uniformly. -/
lemma hmacPRF_uniformKey : hmacPRF.UniformKey := rfl

@[simp] lemma hmacPRF_eval : hmacPRF.eval = hmac := rfl

/-! ## Subkeys -/

/-- The subkeys of the key `key` and the nonce at the byte-answer function `h`:
`TH("leanseal/v1/enc", K ‖ nonce)` for encryption and `TH("leanseal/v1/mac", K ‖ nonce)` for
authentication. -/
@[expose]
def subkeys (h : ByteArray → Bytes 32) (key : Bytes 32) (nonce : Bytes 16) :
    Bytes 32 × Bytes 32 :=
  (TH h "leanseal/v1/enc" (key.toByteArray ++ nonce.toByteArray),
    TH h "leanseal/v1/mac" (key.toByteArray ++ nonce.toByteArray))

/-- The subkeys of the key `key` and the nonce as two queries to the single oracle, at the inputs
of `TH("leanseal/v1/enc", K ‖ nonce)` and `TH("leanseal/v1/mac", K ‖ nonce)`. -/
@[expose]
def subkeysQuery (key : Bytes 32) (nonce : Bytes 16) : OracleComp byteSpec (Bytes 32 × Bytes 32) :=
  do
    let kEnc ← byteSpec.query (labelled "leanseal/v1/enc" (key.toByteArray ++ nonce.toByteArray))
    let kMac ← byteSpec.query (labelled "leanseal/v1/mac" (key.toByteArray ++ nonce.toByteArray))
    return (kEnc, kMac)

/-- With the oracle answered by `h`, the subkey queries give the subkeys at `h`. -/
lemma subkeysAt_subkeysQuery (h : ByteArray → Bytes 32) (key : Bytes 32) :
    subkeysAt (spec := byteSpec) (fun x => (h x : Id (Bytes 32))) (subkeysQuery key) =
      subkeys h key := by
  funext nonce
  simp only [subkeysAt, subkeysQuery, bind_pure_comp, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_map, Id.run_bind, Id.run_map,
    subkeys, TH_eq]
  rfl

/-! ## The executable envelope -/

/-- The envelope of `msg` under the puzzle bytes `pz`, the key and the nonce, at the byte-answer
function `h` (SPEC §6.2 and §7). At `h = sha256` it is leanSeal's envelope. -/
@[expose]
def sealBytes (h : ByteArray → Bytes 32) (pz : ByteArray) (key : Bytes 32) (nonce : Bytes 16)
    (msg : Plaintext) : ByteArray :=
  sealUnder hmacPRF (FixedCodec.bytes 16) (subkeys h key) pz nonce msg

/-- Open an envelope under the puzzle bytes `pz` and the key, at the byte-answer function `h`:
`none` on malformed input, on puzzle bytes other than `pz`, or on a tag mismatch. Opening trusts
`pz` and the key: SPEC-conforming use passes an already validated puzzle encoding and a key
accepted against its commitment, and rejection checks the envelope relative to those values. -/
@[expose]
def openBytes (h : ByteArray → Bytes 32) (pz : ByteArray) (key : Bytes 32) (env : ByteArray) :
    Option Plaintext :=
  openUnder hmacPRF (FixedCodec.bytes 16) (subkeys h key) pz env

/-- Opening a sealed envelope under the same puzzle bytes and key returns the message, for every
nonce and every byte-answer function. -/
theorem openBytes_sealBytes (h : ByteArray → Bytes 32) (pz : ByteArray) (key : Bytes 32)
    (nonce : Bytes 16) (msg : Plaintext) :
    openBytes h pz key (sealBytes h pz key nonce msg) = some msg :=
  openUnder_sealUnder hmacPRF (FixedCodec.bytes 16) (subkeys h key) pz nonce msg

/-! ## The envelope as a DEM over the single oracle -/

/-- leanSeal's envelope as a DEM over the single oracle `byteSpec` with local coins, keyed by a
puzzle with link width `b` and `n` chains together with its key: the 16-byte nonce is drawn
uniformly and carried as itself, the subkeys are two queries to the oracle (`subkeysQuery`), the
PRF is HMAC-SHA256 and the envelope carries the puzzle encoding with `m` steps per chain. -/
@[expose]
def byteEnvelope (b n m : ℕ) :
    DEMScheme (OracleComp (unifSpec + byteSpec)) (Puzzle b n × Bytes 32) Plaintext ByteArray :=
  dem hmacPRF (FixedCodec.bytes 16) subkeysQuery (encode m)

variable {b n : ℕ} (h : ByteArray → Bytes 32) (m : ℕ)

/-- With local coins kept and the oracle answered by `h`, the DEM's encryption is the executable
envelope at `h` under a uniform nonce. -/
theorem simulateQ_byteEnvelope_encrypt (key : Puzzle b n × Bytes 32) (msg : Plaintext) :
    simulateQ (unifFwdAnswerImpl (spec := byteSpec) fun x => (h x : Id (Bytes 32)))
        ((byteEnvelope b n m).encrypt key msg) =
      (fun nonce => sealBytes h (encode m key.1) key.2 nonce msg) <$> ($ᵗ Bytes 16) := by
  rw [byteEnvelope, simulateQ_dem_encrypt, subkeysAt_subkeysQuery]
  rfl

/-- With local coins kept and the oracle answered by `h`, the DEM's decryption is the executable
opening at `h`, a rejection read as the empty message. -/
theorem simulateQ_byteEnvelope_decrypt (key : Puzzle b n × Bytes 32) (env : ByteArray) :
    simulateQ (unifFwdAnswerImpl (spec := byteSpec) fun x => (h x : Id (Bytes 32)))
        ((byteEnvelope b n m).decrypt key env) =
      pure ((openBytes h (encode m key.1) key.2 env).getD default) := by
  rw [byteEnvelope, simulateQ_dem_decrypt, subkeysAt_subkeysQuery]
  rfl

/-- The byte-level envelope is perfectly correct with the oracle answered by any byte-answer
function `h`. -/
theorem byteEnvelope_perfectlyCorrect :
    (byteEnvelope b n m).PerfectlyCorrect
      (ProbCompRuntime.withStateOracle
        (fun x => (pure (h x) : StateT Unit ProbComp (Bytes 32))) ()) :=
  dem_perfectlyCorrect_answerTable hmacPRF (FixedCodec.bytes 16)
    (spec := byteSpec) (fun x => (h x : Id (Bytes 32))) subkeysQuery (encode m)

/-- The byte-level envelope is perfectly correct in the random oracle model, from every initial
cache. -/
theorem byteEnvelope_perfectlyCorrect_rom (cache : byteSpec.QueryCache) :
    (byteEnvelope b n m).PerfectlyCorrect (ProbCompRuntime.rom byteSpec cache) :=
  dem_perfectlyCorrect_rom hmacPRF (FixedCodec.bytes 16) subkeysQuery (encode m) cache

end PointerChainPuzzle.LeanSeal
