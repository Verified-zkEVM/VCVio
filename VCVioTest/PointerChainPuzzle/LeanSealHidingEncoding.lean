/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSealHidingEncoding
public meta import VCVio.Schemes.PointerChainPuzzle.LeanSealHidingEncoding

/-!
# leanSeal's encryption oracles over one random oracle: checks

The subkey rows of the extended encoding are the two queries of `subkeysQuery`, in the order of
`sealDerive` (encryption subkey, then MAC subkey), by `rfl`. Subkey inputs are 64 bytes long, are
routed back to their subkey point, and are no hash input of a typed point. Two byte strings with
the label `leanseal/v1/enc` and a payload of the wrong length, an overlong one of 80 bytes (a
64-byte payload) and a short one of 56 bytes (a 40-byte payload, which `Bytes.read` pads), are
read as subkey points by `parseSubkey` but route to `none`: they fail the re-encoding check.
-/

public section

open OracleSpec OracleComp PointerChainPuzzle PointerChainPuzzle.LeanSeal

namespace VCVioTest.LeanSealHidingEncoding

/-- The byte string of length `k` with every byte `c`. -/
def fill (k : ℕ) (c : UInt8) : Bytes k := ⟨Vector.replicate k c⟩

/-! ## The subkey rows -/

example {b n : ℕ} (k : Bytes 32) (η : Bytes 16) :
    sealInput (b := b) (n := n) (.inr (.inl (k, η))) =
      labelled "leanseal/v1/enc" (k.toByteArray ++ η.toByteArray) := rfl

example {b n : ℕ} (k : Bytes 32) (η : Bytes 16) :
    sealInput (b := b) (n := n) (.inr (.inr (k, η))) =
      labelled "leanseal/v1/mac" (k.toByteArray ++ η.toByteArray) := rfl

/-- `sealDerive` queries the encryption subkey, then the MAC subkey. -/
example {b n : ℕ} (k : Bytes 32) (η : Bytes 16) :
    sealDerive (n := n) (L := Bytes b) (Salt := Bytes 16) (Ctx := Bytes 32) (K := Bytes 32) k η =
      (do
        let e ← (sealTypedSpec b n).query (.inr (.inl (k, η)))
        let t ← (sealTypedSpec b n).query (.inr (.inr (k, η)))
        return (e, t)) := rfl

/-- The subkey rows, in `sealDerive`'s order, are exactly the queries of `subkeysQuery`. -/
example {b n : ℕ} (k : Bytes 32) (η : Bytes 16) :
    subkeysQuery k η = (do
      let e ← byteSpec.query (sealInput (b := b) (n := n) (.inr (.inl (k, η))))
      let t ← byteSpec.query (sealInput (b := b) (n := n) (.inr (.inr (k, η))))
      return (e, t)) := rfl

/-! ## Routing subkey inputs -/

/-- An encryption-subkey point. -/
def encPoint : SubkeyPoint := .inl (fill 32 1, fill 16 2)

/-- A MAC-subkey point. -/
def macPoint : SubkeyPoint := .inr (fill 32 3, fill 16 4)

-- Subkey inputs are 64 bytes long: `u8(15)`, the 15-byte label, the key and the nonce.
/-- info: [64, 64] -/
#guard_msgs in
#eval [(subkeyInput encPoint).size, (subkeyInput macPoint).size]

example (q : SubkeyPoint) : (subkeyInput q).size = 64 := size_subkeyInput q

-- Subkey inputs route back to their subkey point, and `route` reads no typed point from them.
/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [sealRoute (b := 7) (n := 4) (subkeyInput encPoint) == some (.inr encPoint),
  sealRoute (b := 7) (n := 4) (subkeyInput macPoint) == some (.inr macPoint),
  (route (b := 7) (n := 4) (subkeyInput encPoint)).isNone,
  (route (b := 7) (n := 4) (subkeyInput macPoint)).isNone]

example : sealRoute (b := 7) (n := 4) (subkeyInput encPoint) = some (.inr encPoint) :=
  sealRoute_sealInput (by norm_num) (.inr encPoint)

example : route (b := 7) (n := 4) (subkeyInput encPoint) = none := route_subkeyInput encPoint

/-! ## Wrong-length payloads -/

/-- An overlong input with the encryption label: a 64-byte payload, 80 bytes in all. -/
def overlong : ByteArray :=
  labelled "leanseal/v1/enc" ((fill 32 1).toByteArray ++ (fill 32 2).toByteArray)

/-- A short input with the encryption label: a 40-byte payload, 56 bytes in all, which
`Bytes.read` pads with zeros. -/
def short : ByteArray :=
  labelled "leanseal/v1/enc" ((fill 32 1).toByteArray ++ (fill 8 2).toByteArray)

/-- info: [80, 56] -/
#guard_msgs in
#eval [overlong.size, short.size]

-- Both are read as encryption-subkey points, but neither is the input of the point read, so both
-- route to `none`.
/-- info: [true, true, true, true] -/
#guard_msgs in
#eval [(parseSubkey overlong.data.toList).isSome, (parseSubkey short.data.toList).isSome,
  (sealRoute (b := 7) (n := 4) overlong).isNone, (sealRoute (b := 7) (n := 4) short).isNone]

/-- Every byte string that is no input of a point of `sealTypedSpec` routes to `none`, from the
general theorem. -/
example (x : ByteArray) (h : ∀ t : (sealTypedSpec 7 4).Domain, sealInput t ≠ x) :
    sealRoute (b := 7) (n := 4) x = none :=
  (sealRoute_eq_none_iff (by norm_num) x).2 h

/-! ## The refinements at a concrete size -/

example (m : ℕ) : (byteScheme 7 4 m).gen =
    simulateQ (sealEncoding (b := 7) (n := 4) (by norm_num) (by norm_num)).roundImpl
      (typedSealScheme 7 4 m).gen :=
  byteScheme_gen_eq (by norm_num) (by norm_num) m

example (m : ℕ) (key : Puzzle 7 4 × Bytes 32) (msg : Envelope.Plaintext) :
    (byteEnvelope 7 4 m).encrypt key msg =
      simulateQ ((sealEncoding (b := 7) (n := 4) (by norm_num) (by norm_num)).encodeImpl ∘ₛ
        RandomOracleEncoding.typedLift) ((typedSealDEM 7 4 m).encrypt key msg) :=
  byteEnvelope_encrypt_eq (by norm_num) (by norm_num) m key msg

end VCVioTest.LeanSealHidingEncoding
