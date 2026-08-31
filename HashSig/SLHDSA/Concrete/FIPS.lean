/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Primitives
public import HashSig.SLHDSA.Concrete.Sha2
public import HashSig.SLHDSA.Concrete.Keccak

/-!
# FIPS 205 SHA2 and SHAKE primitive instantiations

This module implements the six functions `F`, `H`, `T_l`, `PRF`, `PRF_msg`, and `H_msg` for
all twelve approved SLH-DSA parameter sets. SHA2 category 1 uses SHA-256 throughout; SHA2
categories 3 and 5 retain SHA-256 for `F` and `PRF`, and use SHA-512 for `H`, `T_l`, `H_msg`,
and `PRF_msg`. Every SHAKE-family function uses the distinct FIPS SHAKE256 XOF.

SHA2 address compression is exposed through `Sha2Address`, a proof-carrying result of the
rejecting `Adrs.compressSha2Checked` boundary. The checked primitive entry points return errors for
noncanonical or too-wide addresses. The total `Primitives` bundle maps that out-of-domain case to
the all-zero node because the pre-existing generic construction interface is total; on the stated
FIPS address domain it is definitionally the checked grammar.

## References

- NIST FIPS 205, Sections 11.1, 11.2.1, and 11.2.2
- NIST FIPS 180-4 (SHA-256 and SHA-512)
- NIST FIPS 202 (SHAKE256)
- FIPS 198-1 (HMAC) and RFC 8017 Appendix B.2.1 (MGF1)
-/

@[expose] public section


namespace SLHDSA.Concrete

open SLHDSA
open Sha2
open Keccak

/-! ## Fixed-width byte helpers -/

/-- Convert a fixed-width byte vector without padding or truncation. -/
def bytesToByteArray {n : ℕ} (bytes : Bytes n) : ByteArray := ByteArray.mk bytes.toArray

/-- Take the first `n` bytes and reject a source that is too short. -/
def byteArrayPrefixChecked (bytes : ByteArray) (n : ℕ) : Except CodecError (Bytes n) :=
  decodeExact n (bytes.extract 0 n).toList

/-- The all-zero fixed-width byte vector. -/
def zeroBytes (n : ℕ) : Bytes n := Vector.replicate n 0

/-- Total, fail-closed projection used only where the pre-existing abstract interface requires a
total result. Unlike the former helper, this never pads a partial digest with source bytes. -/
def byteArrayPrefixOrZero (bytes : ByteArray) (n : ℕ) : Bytes n :=
  match byteArrayPrefixChecked bytes n with
  | .ok value => value
  | .error _ => zeroBytes n

/-- Concatenate fixed-width nodes in list order. -/
def concatBytes {n : ℕ} (values : List (Bytes n)) : ByteArray :=
  values.foldl (fun out value => out ++ bytesToByteArray value) ByteArray.empty

/-- Exactly `n` zero bytes. -/
def zeroByteArray (n : ℕ) : ByteArray := ByteArray.mk (Array.replicate n 0)

/-! ## Checked SHA2 address compression -/

/-- A SHA2 address together with the exact successful result of canonical, narrow 22-byte
compression. A value of this type cannot be constructed for an address rejected by the checked
adapter. -/
structure Sha2Address where
  value : Adrs
  canonical : value.isCanonical = true
  layerFits : Adrs.Fits 1 value.layer = true
  treeFits : Adrs.Fits 8 value.tree = true

namespace Sha2Address

/-- Enforce canonicality and the one-byte layer/eight-byte tree bounds before SHA2 hashing. -/
def ofAdrs (address : Adrs) : Except CodecError Sha2Address :=
  if hcanonical : address.isCanonical = true then
    if hlayer : Adrs.Fits 1 address.layer = true then
      if htree : Adrs.Fits 8 address.tree = true then
        .ok ⟨address, hcanonical, hlayer, htree⟩
      else
        .error (.outOfRange 8 address.tree)
    else
      .error (.outOfRange 1 address.layer)
  else
    .error .noncanonicalAddress

/-- The exact 22-byte compressed representation carried by a checked address. -/
def bytes (address : Sha2Address) : Bytes 22 :=
  ⟨address.value.compressSha2.toArray, by simp⟩

/-- The proof-carrying adapter agrees exactly with the checked compression operation. -/
theorem compressSha2Checked_eq (address : Sha2Address) :
    address.value.compressSha2Checked = .ok address.bytes := by
  simp [Adrs.compressSha2Checked, address.canonical, address.layerFits, address.treeFits, bytes]

/-- The proof-carrying adapter's bytes are the existing compressed serialization. -/
@[simp] theorem bytes_toList (address : Sha2Address) :
    address.bytes.toList = address.value.compressSha2 := by
  simp [bytes]

end Sha2Address

/-! ## SHA2 family -/

/-- FIPS's SHA2 prefix for `F` and `PRF`, which always use the SHA-256 block width. -/
def sha2Prefix256Key {n : ℕ} (pkSeed : Bytes n) (address : Bytes 22) : ByteArray :=
  bytesToByteArray pkSeed ++ zeroByteArray (64 - n) ++ bytesToByteArray address

/-- SHA-256 prefix from a proof-carrying structural address. -/
def sha2Prefix256 {n : ℕ} (pkSeed : Bytes n) (address : Sha2Address) : ByteArray :=
  sha2Prefix256Key pkSeed address.bytes

/-- FIPS's SHA2 prefix for category-3/5 `H` and `T_l`, using the SHA-512 block width. -/
def sha2Prefix512Key {n : ℕ} (pkSeed : Bytes n) (address : Bytes 22) : ByteArray :=
  bytesToByteArray pkSeed ++ zeroByteArray (128 - n) ++ bytesToByteArray address

/-- SHA-512 prefix from a proof-carrying structural address. -/
def sha2Prefix512 {n : ℕ} (pkSeed : Bytes n) (address : Sha2Address) : ByteArray :=
  sha2Prefix512Key pkSeed address.bytes

/-- Exact checked SHA2 `F` grammar. -/
def sha2FChecked {n : ℕ} (pkSeed : Bytes n) (address : Adrs) (message : Bytes n) :
    Except CodecError (Bytes n) := do
  let checked ← Sha2Address.ofAdrs address
  byteArrayPrefixChecked
    (sha256 (sha2Prefix256 pkSeed checked ++ bytesToByteArray message)) n

/-- Exact checked SHA2 `PRF` grammar. -/
def sha2PRFChecked {n : ℕ} (pkSeed skSeed : Bytes n) (address : Adrs) :
    Except CodecError (Bytes n) := do
  let checked ← Sha2Address.ofAdrs address
  byteArrayPrefixChecked
    (sha256 (sha2Prefix256 pkSeed checked ++ bytesToByteArray skSeed)) n

/-- Exact checked SHA2 `H` grammar, selecting SHA-256 only for `n = 16`. -/
def sha2HChecked {n : ℕ} (pkSeed : Bytes n) (address : Adrs) (left right : Bytes n) :
    Except CodecError (Bytes n) := do
  let checked ← Sha2Address.ofAdrs address
  let message := bytesToByteArray left ++ bytesToByteArray right
  if n = 16 then
    byteArrayPrefixChecked (sha256 (sha2Prefix256 pkSeed checked ++ message)) n
  else
    byteArrayPrefixChecked (sha512 (sha2Prefix512 pkSeed checked ++ message)) n

/-- Exact checked SHA2 `T_l` grammar, selecting SHA-256 only for `n = 16`. -/
def sha2TlChecked {n : ℕ} (pkSeed : Bytes n) (address : Adrs) (message : List (Bytes n)) :
    Except CodecError (Bytes n) := do
  let checked ← Sha2Address.ofAdrs address
  if n = 16 then
    byteArrayPrefixChecked (sha256 (sha2Prefix256 pkSeed checked ++ concatBytes message)) n
  else
    byteArrayPrefixChecked (sha512 (sha2Prefix512 pkSeed checked ++ concatBytes message)) n

/-- SHA2 `PRF_msg`: HMAC-SHA-256 at `n = 16`, HMAC-SHA-512 otherwise. -/
def sha2PRFmsg {n : ℕ} (skPrf optRand : Bytes n) (message : List Byte) : Bytes n :=
  let input := bytesToByteArray optRand ++ ByteArray.mk message.toArray
  if n = 16 then
    byteArrayPrefixOrZero (hmacSha256 (bytesToByteArray skPrf) input) n
  else
    byteArrayPrefixOrZero (hmacSha512 (bytesToByteArray skPrf) input) n

/-- SHA2 `H_msg`: MGF1-SHA-256 at `n = 16`, MGF1-SHA-512 otherwise. -/
def sha2Hmsg (p : Params) (randomizer pkSeed pkRoot : Bytes p.n)
    (message : List Byte) : Bytes p.m :=
  let input := bytesToByteArray randomizer ++ bytesToByteArray pkSeed ++
    bytesToByteArray pkRoot ++ ByteArray.mk message.toArray
  if p.n = 16 then
    let inner := sha256 input
    byteArrayPrefixOrZero (mgf1Sha256 (bytesToByteArray randomizer ++
      bytesToByteArray pkSeed ++ inner) p.m) p.m
  else
    let inner := sha512 input
    byteArrayPrefixOrZero (mgf1Sha512 (bytesToByteArray randomizer ++
      bytesToByteArray pkSeed ++ inner) p.m) p.m

/-- Convert the checked SHA2 operation to the pre-existing total primitive interface. Invalid
addresses cannot be FIPS inputs and map to the all-zero node rather than being silently
truncated. -/
def checkedNodeOrZero {n : ℕ} (result : Except CodecError (Bytes n)) : Bytes n :=
  match result with
  | .ok value => value
  | .error _ => zeroBytes n

/-- Canonical SHA2 address key for the total abstract interface. Checked public entry points
retain the rejection result; this projection maps out-of-domain structural addresses to zero. -/
def sha2AdrsKey (address : Adrs) : Bytes 22 :=
  match address.compressSha2Checked with
  | .ok value => value
  | .error _ => zeroBytes 22

/-- On the checked SHA-2 address domain, the total primitive key is exactly `ADRSc`; the zero-key
fallback is unreachable. -/
theorem sha2AdrsKey_eq_compressed (address : Adrs)
    (hcanonical : address.isCanonical = true)
    (hlayer : Adrs.Fits 1 address.layer = true)
    (htree : Adrs.Fits 8 address.tree = true) :
    sha2AdrsKey address = ⟨address.compressSha2.toArray, by simp⟩ := by
  simp [sha2AdrsKey, Adrs.compressSha2Checked, hcanonical, hlayer, htree]

/-- The total SHA-2 primitive address key is injective between two checked-domain addresses.
The one-byte type hypothesis is explicit because `ADRSc` compresses the full four-byte ADRS type
field; canonicality supplies the three four-byte word bounds. -/
theorem sha2AdrsKey_injective_of_domain {a b : Adrs}
    (haCanonical : a.isCanonical = true) (haLayer : Adrs.Fits 1 a.layer = true)
    (haTree : Adrs.Fits 8 a.tree = true) (haType : Adrs.Fits 1 a.type = true)
    (hbCanonical : b.isCanonical = true) (hbLayer : Adrs.Fits 1 b.layer = true)
    (hbTree : Adrs.Fits 8 b.tree = true) (hbType : Adrs.Fits 1 b.type = true)
    (hkey : sha2AdrsKey a = sha2AdrsKey b) : a = b := by
  rcases Adrs.fits_of_isCanonical a haCanonical with
    ⟨_, _, _, haWord1, haWord2, haWord3⟩
  rcases Adrs.fits_of_isCanonical b hbCanonical with
    ⟨_, _, _, hbWord1, hbWord2, hbWord3⟩
  rw [sha2AdrsKey_eq_compressed a haCanonical haLayer haTree,
    sha2AdrsKey_eq_compressed b hbCanonical hbLayer hbTree] at hkey
  apply Adrs.compressSha2_injective_of_fits haLayer haTree haType haWord1 haWord2 haWord3
    hbLayer hbTree hbType hbWord1 hbWord2 hbWord3
  exact congrArg Vector.toList hkey

/-- The single variable-arity SHA2 tweakable-hash collection. FIPS 205 uses SHA-256 for the
singleton `F` view in every category; larger arities use SHA-256 at `n = 16` and SHA-512 at
`n = 24, 32`. -/
def sha2Thash (p : Params) (pkSeed : Bytes p.n) (address : Bytes 22)
    (messages : List (Bytes p.n)) : Bytes p.n :=
  let payload := concatBytes messages
  if messages.length = 1 then
    byteArrayPrefixOrZero (sha256 (sha2Prefix256Key pkSeed address ++ payload)) p.n
  else if p.n = 16 then
    byteArrayPrefixOrZero (sha256 (sha2Prefix256Key pkSeed address ++ payload)) p.n
  else
    byteArrayPrefixOrZero (sha512 (sha2Prefix512Key pkSeed address ++ payload)) p.n

/-- The SHA2 primitive bundle at byte width `p.n`. FIPS-approved callers use this only through
`approvedPrimitives`, and construction address-range proofs are successor-session obligations. -/
def sha2Primitives (p : Params) : Primitives p where
  PkSeed := Bytes p.n
  SkSeed := Bytes p.n
  SkPrf := Bytes p.n
  Y := Bytes p.n
  AdrsKey := Bytes 22
  adrsToKey := sha2AdrsKey
  Thash := sha2Thash p
  PRF := fun pkSeed skSeed address => checkedNodeOrZero (sha2PRFChecked pkSeed skSeed address)
  PRFmsg := sha2PRFmsg
  Hmsg := sha2Hmsg p
  yToBytes := id

/-! ## SHAKE family -/

/-- Full 32-byte ADRS serialization used by every SHAKE primitive. -/
def shakeAddress (address : Adrs) : ByteArray := ByteArray.mk address.toBytes.toArray

/-- SHAKE address payload from the canonical fixed-width key. -/
def shakeAddressKey (address : Bytes 32) : ByteArray := bytesToByteArray address

/-- SHAKE-family `F`. -/
def shakeF {n : ℕ} (pkSeed : Bytes n) (address : Adrs) (message : Bytes n) : Bytes n :=
  byteArrayPrefixOrZero (shake256 (bytesToByteArray pkSeed ++ shakeAddress address ++
    bytesToByteArray message) n) n

/-- SHAKE-family `H`. -/
def shakeH {n : ℕ} (pkSeed : Bytes n) (address : Adrs) (left right : Bytes n) : Bytes n :=
  byteArrayPrefixOrZero (shake256 (bytesToByteArray pkSeed ++ shakeAddress address ++
    bytesToByteArray left ++ bytesToByteArray right) n) n

/-- SHAKE-family `T_l`. -/
def shakeTl {n : ℕ} (pkSeed : Bytes n) (address : Adrs) (message : List (Bytes n)) : Bytes n :=
  byteArrayPrefixOrZero (shake256 (bytesToByteArray pkSeed ++ shakeAddress address ++
    concatBytes message) n) n

/-- SHAKE-family `PRF`. -/
def shakePRF {n : ℕ} (pkSeed skSeed : Bytes n) (address : Adrs) : Bytes n :=
  byteArrayPrefixOrZero (shake256 (bytesToByteArray pkSeed ++ shakeAddress address ++
    bytesToByteArray skSeed) n) n

/-- SHAKE-family `PRF_msg`. -/
def shakePRFmsg {n : ℕ} (skPrf optRand : Bytes n) (message : List Byte) : Bytes n :=
  byteArrayPrefixOrZero (shake256 (bytesToByteArray skPrf ++ bytesToByteArray optRand ++
    ByteArray.mk message.toArray) n) n

/-- SHAKE-family `H_msg`. -/
def shakeHmsg (p : Params) (randomizer pkSeed pkRoot : Bytes p.n)
    (message : List Byte) : Bytes p.m :=
  byteArrayPrefixOrZero (shake256 (bytesToByteArray randomizer ++ bytesToByteArray pkSeed ++
    bytesToByteArray pkRoot ++ ByteArray.mk message.toArray) p.m) p.m

/-- The single variable-arity SHAKE256 tweakable-hash collection. -/
def shakeThash (p : Params) (pkSeed : Bytes p.n) (address : Bytes 32)
    (messages : List (Bytes p.n)) : Bytes p.n :=
  byteArrayPrefixOrZero (shake256 (bytesToByteArray pkSeed ++ shakeAddressKey address ++
    concatBytes messages) p.n) p.n

/-- The SHAKE256 primitive bundle at byte width `p.n`. -/
def shakePrimitives (p : Params) : Primitives p where
  PkSeed := Bytes p.n
  SkSeed := Bytes p.n
  SkPrf := Bytes p.n
  Y := Bytes p.n
  AdrsKey := Bytes 32
  adrsToKey := Adrs.toVector
  Thash := shakeThash p
  PRF := shakePRF
  PRFmsg := shakePRFmsg
  Hmsg := shakeHmsg p
  yToBytes := id

/-! ## All approved profiles and byte coherence -/

/-- Select the exact FIPS primitive family for one of the twelve approved parameter names. -/
def approvedPrimitives (set : FipsParameterSet) : Primitives set.params :=
  match set.hashFamily with
  | .sha2 => sha2Primitives set.params
  | .shake => shakePrimitives set.params

/-- Fixed-width byte nodes satisfy the abstract representation-coherence boundary. -/
theorem sha2Primitives_byteLaws (p : Params) : (sha2Primitives p).core.ByteLaws :=
  ⟨fun _ _ h => h⟩

/-- Fixed-width byte nodes satisfy the abstract representation-coherence boundary. -/
theorem shakePrimitives_byteLaws (p : Params) : (shakePrimitives p).core.ByteLaws :=
  ⟨fun _ _ h => h⟩

/-- Every approved SHA2/SHAKE bundle satisfies byte coherence. -/
theorem approvedPrimitives_byteLaws (set : FipsParameterSet) :
    (approvedPrimitives set).core.ByteLaws := by
  cases set <;> exact ⟨fun _ _ h => h⟩

end SLHDSA.Concrete
