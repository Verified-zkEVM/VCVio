/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Representation
public import HashSig.SLHDSA.Concrete.Codec

/-!
# Complete SLH-DSA-SHAKE-128s data and wire correspondences

The bit-vector and byte-vector carriers are in bijection on every field. Whole signatures
use the existing canonical codec, with exact width, field order and complete consumption.
The full oracle-answer equivalence also transports its actual uniform law.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Bridge

open SLHDSA

/-- The FIPS 205 structured signature at SLH-DSA-SHAKE-128s. -/
abbrev CoreSignature : Type := SignatureCore FIPS205.params.params FIPS205.core

/-- The atomic wire codec of the SHAKE context. -/
abbrev wireCodec : CoreWireCodec FIPS205.params.params FIPS205.core :=
  Concrete.shakeWireCodec FIPS205.params.params

/-- FORS tree signatures are equal when their fields are. -/
theorem forsTreeSigCore_ext {x y : ForsTreeSigCore FIPS205.params.params FIPS205.core}
    (hsk : x.sk = y.sk) (hauth : x.auth = y.auth) : x = y := by
  cases x
  cases y
  simp_all

/-- XMSS signatures are equal when their fields are. -/
theorem xmssSigCore_ext {x y : XmssSigCore FIPS205.params.params FIPS205.core}
    (hwots : x.wots = y.wots) (hauth : x.auth = y.auth) : x = y := by
  cases x
  cases y
  simp_all

/-- The paper's FORS tree signature of a FIPS 205 one. -/
@[expose] def forsTreeOfCore (t : ForsTreeSigCore FIPS205.params.params FIPS205.core) :
    ForsTreeSignature where
  secret := digestEquiv.symm t.sk
  authentication j := digestEquiv.symm (t.auth[j.val]'j.isLt)

/-- FIPS 205's FORS tree signature of a paper one. -/
@[expose] def forsTreeToCore (t : ForsTreeSignature) :
    ForsTreeSigCore FIPS205.params.params FIPS205.core where
  sk := digestEquiv t.secret
  auth := Vector.ofFn fun j => digestEquiv (t.authentication j)

/-- The paper's XMSS signature of a FIPS 205 one. -/
@[expose] def xmssOfCore (t : XmssSigCore FIPS205.params.params FIPS205.core) : XmssSignature where
  wots j := digestEquiv.symm (t.wots[j.val]'j.isLt)
  authentication j := digestEquiv.symm (t.auth[j.val]'j.isLt)

/-- FIPS 205's XMSS signature of a paper one. -/
@[expose] def xmssToCore (t : XmssSignature) : XmssSigCore FIPS205.params.params FIPS205.core where
  wots := Vector.ofFn fun j => digestEquiv (t.wots j)
  auth := Vector.ofFn fun j => digestEquiv (t.authentication j)

/-- **The paper's signature of a FIPS 205 structured signature**: every node read as a digest,
FORS trees and hypertree layers in the same order. -/
@[expose] def sigOfCore (σ : CoreSignature) : Signature where
  randomizer := digestEquiv.symm σ.randomness
  fors i := forsTreeOfCore (σ.fors[i.val]'i.isLt)
  hypertree i := xmssOfCore (σ.hypertree[i.val]'i.isLt)

/-- FIPS 205's structured signature of a paper signature. -/
@[expose] def sigToCore (s : Signature) : CoreSignature where
  randomness := digestEquiv s.randomizer
  fors := Vector.ofFn fun i => forsTreeToCore (s.fors i)
  hypertree := Vector.ofFn fun i => xmssToCore (s.hypertree i)

/-- **Signatures of the two schemes are in bijection** (`sigOfCore`, `sigToCore`). -/
@[expose] def signatureEquiv : CoreSignature ≃ Signature where
  toFun := sigOfCore
  invFun := sigToCore
  left_inv σ := by
    rcases σ with ⟨r, f, ht⟩
    simp only [sigToCore, sigOfCore, Equiv.apply_symm_apply]
    congr 1
    · apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      apply forsTreeSigCore_ext
      · simp [forsTreeToCore, forsTreeOfCore]
        rfl
      · apply Vector.ext
        intro j hj
        simp [forsTreeToCore, forsTreeOfCore]
        rfl
    · apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      apply xmssSigCore_ext
      · apply Vector.ext
        intro j hj
        simp [xmssToCore, xmssOfCore]
        rfl
      · apply Vector.ext
        intro j hj
        simp [xmssToCore, xmssOfCore]
        rfl
  right_inv s := by
    rcases s with ⟨r, f, ht⟩
    simp only [sigToCore, sigOfCore, Equiv.symm_apply_apply]
    congr 1
    · funext i
      simp only [forsTreeToCore, forsTreeOfCore, Equiv.symm_apply_apply, Vector.getElem_ofFn]
      rfl
    · funext i
      simp only [xmssToCore, xmssOfCore, Equiv.symm_apply_apply, Vector.getElem_ofFn]
      rfl

/-- `signatureEquiv` is `sigOfCore`. -/
@[simp] theorem signatureEquiv_apply (σ : CoreSignature) : signatureEquiv σ = sigOfCore σ := rfl

/-- The inverse of `signatureEquiv` is `sigToCore`. -/
@[simp] theorem signatureEquiv_symm_apply (s : Signature) :
    signatureEquiv.symm s = sigToCore s := rfl

/-- The atomic SHAKE codec writes a node as its own bytes. -/
theorem wireCodec_y_encode (v : FIPS205.core.Y) :
    wireCodec.y.encode v = Vector.toList (v : Node) := rfl

/-- The native WOTS+ signature has thirty-five chains. -/
theorem params_len : FIPS205.params.params.len = 35 := by decide

/-- The complete native signature width agrees with the paper's fixed width. -/
theorem params_signatureBytes : FIPS205.params.params.signatureBytes = signatureBytes := by decide


end SLHDSA.SHAKE128s.Bridge

namespace SLHDSA.SHAKE128s

/-- Encode every structured signature using the canonical full-signature codec. -/
@[expose] def Signature.toBytes (signature : Signature) : Bytes :=
  encodeSignature FIPS205.params Bridge.wireCodec (Bridge.sigToCore signature)

/-- Decode exactly one complete canonical signature. -/
@[expose] def Signature.fromBytes? (wire : Bytes) : Option Signature :=
  Bridge.sigOfCore <$> (decodeSignature FIPS205.params Bridge.wireCodec wire).toOption

/-- Every non-exact signature width is rejected. -/
theorem Signature.fromBytes?_eq_none_of_length_ne (wire : Bytes)
    (hlen : wire.length ≠ signatureBytes) : Signature.fromBytes? wire = none := by
  have hnative : wire.length ≠ FIPS205.params.params.signatureBytes := by
    simpa only [Bridge.params_signatureBytes] using hlen
  rw [Signature.fromBytes?, decodeSignature,
    WireCodec.decode_eq_error_of_length_ne _ _ hnative]
  rfl

end SLHDSA.SHAKE128s

namespace SLHDSA.SHAKE128s.Bridge

/-- Encoding a native signature through its paper representation writes the canonical bytes. -/
theorem toBytes_sigOfCore (signature : CoreSignature) :
    (sigOfCore signature).toBytes = encodeSignature FIPS205.params wireCodec signature := by
  simp only [Signature.toBytes, ← signatureEquiv_apply, ← signatureEquiv_symm_apply,
    Equiv.symm_apply_apply]

/-- Parsing canonical signature bytes returns the corresponding complete paper signature. -/
theorem fromBytes?_encodeSignature (signature : CoreSignature) :
    Signature.fromBytes? (encodeSignature FIPS205.params wireCodec signature) =
      some (sigOfCore signature) := by
  change Option.map sigOfCore
    ((decodeSignature FIPS205.params wireCodec
      (encodeSignature FIPS205.params wireCodec signature)).toOption) = _
  rw [decodeSignature_encode]
  rfl

/-- Paper parsing is canonical full decoding followed by the structured representation map. -/
theorem fromBytes?_eq (wire : Bytes) :
    Signature.fromBytes? wire =
      sigOfCore <$> (decodeSignature FIPS205.params wireCodec wire).toOption := rfl

end SLHDSA.SHAKE128s.Bridge
