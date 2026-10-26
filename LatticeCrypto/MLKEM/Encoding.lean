/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.MLKEM.Arithmetic

/-!
# ML-KEM Encoding Interfaces

This file records the compression and byte-encoding operations referenced by the FIPS 203
pseudocode. In this first phase they are kept abstract, but their types match the semantic objects
consumed by the spec-level `K-PKE` and `ML-KEM` algorithms.
-/

@[expose] public section


namespace MLKEM

/-- Encoding and compression operations used by the ML-KEM pseudocode. -/
structure Encoding (params : Params) where
  /-- The type of serialized vectors of `k` NTT-domain polynomials, the outputs of
  `byteEncode12Vec`. It carries `ByteEncode_12(t̂)` in the encapsulation key and
  `ByteEncode_12(ŝ)` in the K-PKE decryption key (FIPS 203 Algorithm 13). -/
  EncodedTHat : Type
  /-- The type of serialized first ciphertext components
  `c₁ = ByteEncode_du(Compress_du(u))` (FIPS 203 Algorithm 14). -/
  EncodedU : Type
  /-- The type of serialized second ciphertext components
  `c₂ = ByteEncode_dv(Compress_dv(v))` (FIPS 203 Algorithm 14). -/
  EncodedV : Type
  /-- `ByteEncode_12` (FIPS 203 Algorithm 5 with `d = 12`) applied to each polynomial of an
  NTT-domain vector and concatenated; `K-PKE.KeyGen` (Algorithm 13) serializes `t̂` and `ŝ`
  with it. -/
  byteEncode12Vec : TqVec params.k → EncodedTHat
  /-- `ByteDecode_12` (FIPS 203 Algorithm 6 with `d = 12`) applied to each 384-byte block of a
  serialized vector; it recovers `t̂` in `K-PKE.Encrypt` (Algorithm 14) and `ŝ` in
  `K-PKE.Decrypt` (Algorithm 15). -/
  byteDecode12Vec : EncodedTHat → TqVec params.k
  /-- Freshly serialized public-key vectors decode back to the original semantic value. This is
  the canonicality invariant relied on by the top-level checked ML-KEM API. -/
  byteDecode12Vec_byteEncode12Vec :
    ∀ tHat : TqVec params.k, byteDecode12Vec (byteEncode12Vec tHat) = tHat
  /-- `Compress_du` (FIPS 203 Section 4.2.1) applied to every coefficient of a vector;
  `K-PKE.Encrypt` (Algorithm 14) applies it to `u`. -/
  compressDU : RqVec params.k → RqVec params.k
  /-- `Decompress_du` (FIPS 203 Section 4.2.1) applied to every coefficient of a vector;
  `K-PKE.Decrypt` (Algorithm 15) applies it to recover `u'`. -/
  decompressDU : RqVec params.k → RqVec params.k
  /-- `ByteEncode_du` (FIPS 203 Algorithm 5 with `d = du`) applied to each polynomial of a
  compressed vector and concatenated, producing `c₁`. -/
  byteEncodeDUVec : RqVec params.k → EncodedU
  /-- `ByteDecode_du` (FIPS 203 Algorithm 6 with `d = du`) applied to each block of `c₁`. -/
  byteDecodeDUVec : EncodedU → RqVec params.k
  /-- `Compress_dv` (FIPS 203 Section 4.2.1) applied to every coefficient of a polynomial;
  `K-PKE.Encrypt` (Algorithm 14) applies it to `v`. -/
  compressDV : Rq → Rq
  /-- `Decompress_dv` (FIPS 203 Section 4.2.1) applied to every coefficient of a polynomial;
  `K-PKE.Decrypt` (Algorithm 15) applies it to recover `v'`. -/
  decompressDV : Rq → Rq
  /-- `ByteEncode_dv` (FIPS 203 Algorithm 5 with `d = dv`), producing `c₂` from the compressed
  `v`. -/
  byteEncodeDV : Rq → EncodedV
  /-- `ByteDecode_dv` (FIPS 203 Algorithm 6 with `d = dv`), decoding `c₂`. -/
  byteDecodeDV : EncodedV → Rq
  /-- `Compress_1` (FIPS 203 Section 4.2.1) applied to every coefficient, rounding each to one
  bit; `K-PKE.Decrypt` (Algorithm 15) applies it to `w` to recover the message bits. -/
  compress1 : Rq → Rq
  /-- `Decompress_1` (FIPS 203 Section 4.2.1) applied to every coefficient, sending the bit `1`
  to `⌈q/2⌋`; `K-PKE.Encrypt` (Algorithm 14) applies it to embed the message as `μ`. -/
  decompress1 : Rq → Rq
  /-- `ByteEncode_1` (FIPS 203 Algorithm 5 with `d = 1`), packing one-bit coefficients into a
  32-byte message; `K-PKE.Decrypt` (Algorithm 15) outputs the plaintext through it. -/
  byteEncode1 : Rq → Message
  /-- `ByteDecode_1` (FIPS 203 Algorithm 6 with `d = 1`), unpacking a 32-byte message into one
  bit per coefficient; `K-PKE.Encrypt` (Algorithm 14) reads the plaintext through it. -/
  byteDecode1 : Message → Rq

namespace Encoding

variable {params : Params} (encoding : Encoding params)

/-- Roundtrip laws needed to reason about ciphertext and message encoding at the semantic layer.
These are kept separate from the executable encoding bundle so concrete implementations can expose
their proofs incrementally without blocking computation. -/
structure Laws : Prop where
  byteDecodeDUVec_byteEncodeDUVec_compressDU :
    ∀ u : RqVec params.k,
      encoding.byteDecodeDUVec (encoding.byteEncodeDUVec (encoding.compressDU u)) =
        encoding.compressDU u
  byteDecodeDV_byteEncodeDV_compressDV :
    ∀ v : Rq,
      encoding.byteDecodeDV (encoding.byteEncodeDV (encoding.compressDV v)) =
        encoding.compressDV v
  byteEncode1_byteDecode1 :
    ∀ msg : Message, encoding.byteEncode1 (encoding.byteDecode1 msg) = msg
  byteDecode1_byteEncode1_compress1 :
    ∀ v : Rq,
      encoding.byteDecode1 (encoding.byteEncode1 (encoding.compress1 v)) =
        encoding.compress1 v

/-- Canonicality check mirroring the FIPS 203 public-key modulus check. -/
def publicKeyCanonical [DecidableEq encoding.EncodedTHat]
    (tHatEncoded : encoding.EncodedTHat) : Bool :=
  encoding.byteEncode12Vec (encoding.byteDecode12Vec tHatEncoded) == tHatEncoded

@[simp] theorem publicKeyCanonical_byteEncode12Vec_eq_true
    [DecidableEq encoding.EncodedTHat] (tHat : TqVec params.k) :
    encoding.publicKeyCanonical (encoding.byteEncode12Vec tHat) = true := by
  unfold Encoding.publicKeyCanonical
  simp [encoding.byteDecode12Vec_byteEncode12Vec tHat]

/-- Ciphertext decoding into the semantic `(u, v)` pair used by decryption. -/
def decodeCiphertext (uEncoded : encoding.EncodedU) (vEncoded : encoding.EncodedV) :
    RqVec params.k × Rq :=
  (encoding.decompressDU (encoding.byteDecodeDUVec uEncoded),
    encoding.decompressDV (encoding.byteDecodeDV vEncoded))

end Encoding

end MLKEM
