/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Requests
public import HashSig.SLHDSA.SHAKE128s.Statement.RandomOracleModel
public import Mathlib.Data.BitVec

/-!
# Pure SLH-DSA-SHAKE-128s data

The fixed parameters, keys, addresses and structured signatures carry their full native
domains. Pure input formatting and digest-array payloads do not execute any oracle query.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s

/-! ## Parameters (Table 2) -/

/-- `n`: the byte length of seeds, tree nodes, chain values and the randomizer. -/
@[expose] def n : Nat := 16

/-- `h`: the total height of the hypertree. -/
@[expose] def totalHeight : Nat := 63

/-- `d`: the number of layers of the hypertree. -/
@[expose] def layers : Nat := 7

/-- `h'`: the height of each XMSS tree of the hypertree. -/
@[expose] def subtreeHeight : Nat := 9

/-- `a`: the height of each FORS tree. -/
@[expose] def forsHeight : Nat := 12

/-- `k`: the number of FORS trees. -/
@[expose] def forsTrees : Nat := 14

/-- `lg_w`: the number of bits of a WOTS+ digit. -/
@[expose] def winternitzBits : Nat := 4

/-- `w = 2 ^ lg_w`: the number of values of a WOTS+ digit. -/
@[expose] def w : Nat := 2 ^ winternitzBits

/-- `len₁`: the number of base-`w` digits of an `n`-byte message. -/
@[expose] def messageDigits : Nat := 8 * n / winternitzBits

/-- `len₂`: the number of base-`w` digits of the WOTS+ checksum. -/
@[expose] def checksumDigits : Nat := 3

/-- `len = len₁ + len₂`: the number of WOTS+ chains. -/
@[expose] def chains : Nat := messageDigits + checksumDigits

/-- Output length of `H_msg`, in bytes. -/
@[expose] def messageDigestBytes : Nat := 30

/-- The byte length of an encoded signature: the randomizer, a secret value and `a` authentication
nodes for each of the `k` FORS trees, then `d` WOTS+ signatures of `len` values and `h`
authentication nodes in total over the hypertree, all in units of `n` bytes. -/
@[expose]
def signatureBytes : Nat := (1 + forsTrees * (1 + forsHeight) + totalHeight + layers * chains) * n

/-! ## Data -/

/-- An `n`-byte value, as a bit vector: a seed, a tree node, a chain value or a randomizer. -/
abbrev Digest := BitVec (8 * n)

/-- An answer of the random oracle: `messageDigestBytes` bytes, as a bit vector. -/
abbrev HashOutput := BitVec (8 * messageDigestBytes)

/-- An SLH-DSA public key `(PK.seed, PK.root)`. -/
structure PublicKey where
  /-- `PK.seed`: the public seed that keys every tweakable hash. -/
  seed : Digest
  /-- `PK.root`: the root of the top XMSS tree of the hypertree. -/
  root : Digest
deriving DecidableEq

/-- An SLH-DSA secret key: `SK.seed`, `SK.prf` and the public key. -/
structure SecretKey where
  /-- `SK.seed`: the seed from which the WOTS+ and FORS secret values are derived. -/
  seed : Digest
  /-- `SK.prf`: the key of `PRF_msg`. -/
  prf : Digest
  /-- The public key `(PK.seed, PK.root)` of the key pair. -/
  publicKey : PublicKey
deriving DecidableEq

/-- Big-endian encoding (Algorithm 3). -/
@[expose] def bytesBE (byteCount : Nat) (value : BitVec (8 * byteCount)) : Bytes :=
  (List.ofFn fun i : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * i.val) 8)).reverse

/-! ## Addresses (Section 4.2, 32-byte form) -/

/-- The address types of FIPS 205 Section 4.2. -/
inductive AddressType where
  /-- `WOTS_HASH`: a step of a WOTS+ hash chain. -/
  | wotsHash
  /-- `WOTS_PK`: the compression of the WOTS+ chain ends into a WOTS+ public key. -/
  | wotsPk
  /-- `TREE`: a node of an XMSS tree. -/
  | tree
  /-- `FORS_TREE`: a node of a FORS tree. -/
  | forsTree
  /-- `FORS_ROOTS`: the compression of the FORS roots into the FORS public key. -/
  | forsRoots
  /-- `WOTS_PRF`: the derivation of a WOTS+ secret value. -/
  | wotsPrf
  /-- `FORS_PRF`: the derivation of a FORS secret value. -/
  | forsPrf
deriving DecidableEq

/-- The 4-byte type code of an address type. -/
@[expose] def AddressType.code : AddressType → BitVec 32
  | .wotsHash => 0
  | .wotsPk => 1
  | .tree => 2
  | .forsTree => 3
  | .forsRoots => 4
  | .wotsPrf => 5
  | .forsPrf => 6

/-- An address `ADRS` (FIPS 205 Section 4.2), with the fields of its 32-byte form. -/
structure Address where
  /-- The layer address: the hypertree layer. -/
  layer : BitVec 32 := 0
  /-- The tree address: the index of the XMSS tree within its layer. -/
  tree : BitVec 96 := 0
  /-- The address type. -/
  kind : AddressType := .wotsHash
  /-- The key pair address: the WOTS+ key or FORS instance within the tree. -/
  keyPair : BitVec 32 := 0
  /-- The chain address of a WOTS+ address, or the tree height of a tree address. -/
  chainOrHeight : BitVec 32 := 0
  /-- The hash address of a WOTS+ address, or the tree index of a tree address. -/
  hashOrIndex : BitVec 32 := 0
deriving DecidableEq

/-- The 32-byte encoding of an address: each field big-endian, in order. -/
@[expose] def Address.toBytes (address : Address) : Bytes :=
  bytesBE 4 address.layer ++ bytesBE 12 address.tree ++ bytesBE 4 address.kind.code ++
    bytesBE 4 address.keyPair ++ bytesBE 4 address.chainOrHeight ++ bytesBE 4 address.hashOrIndex

/-- `ADRS.setTypeAndClear`: set the type and zero the key pair, chain or height, and hash or index
fields. -/
@[expose] def Address.setTypeAndClear (address : Address) (kind : AddressType) : Address :=
  { address with kind, keyPair := 0, chainOrHeight := 0, hashOrIndex := 0 }

/-! ## Hashing (Section 11.1, as one random oracle) -/

/-- The random oracle on byte strings, answering with `HashOutput`. -/
abbrev HashSpec := RandomOracleModel.HashSpec Bytes HashOutput

/-- The world of the scheme: private uniform sampling and the random oracle. -/
abbrev OracleWorld := RandomOracleModel.World Bytes HashOutput

namespace Hashing

/-- The first 16 bytes of an answer. -/
@[expose] def truncate (answer : HashOutput) : Digest :=
  answer.extractLsb' (8 * (messageDigestBytes - n)) (8 * n)

/-- Input of `F`, `H`, `T_l` and `PRF`: `PK.seed ‖ ADRS ‖ payload`. -/
@[expose] def tweakableInput (seed : Digest) (address : Address) (payload : Bytes) : Bytes :=
  bytesBE n seed ++ address.toBytes ++ payload

/-- Input of `PRF_msg`, with `opt_rand = PK.seed`. -/
@[expose] def randomizerInput (prf seed : Digest) (message : Bytes) : Bytes :=
  bytesBE n prf ++ bytesBE n seed ++ message

/-- Input of `H_msg`. -/
@[expose] def messageInput (randomizer : Digest) (pk : PublicKey) (message : Bytes) : Bytes :=
  bytesBE n randomizer ++ bytesBE n pk.seed ++ bytesBE n pk.root ++ message

end Hashing

/-- Pure-mode framing `0 ‖ |ctx| ‖ ctx ‖ M` (Algorithms 22 and 24). -/
@[expose] def Message.frame (request : Message) : Option Bytes :=
  if request.context.length ≤ 255 then
    some ([0, UInt8.ofNat request.context.length] ++ request.context ++ request.message)
  else none

/-! ## Signatures (Figures 10–17) -/

/-- A WOTS+ signature: one chain value per chain. -/
abbrev WotsSignature := Fin chains → Digest

/-- An XMSS signature: a WOTS+ signature and an authentication path. -/
structure XmssSignature where
  /-- The WOTS+ signature under the key of the signing leaf. -/
  wots : WotsSignature
  /-- The authentication path: the sibling at each height, from the leaf up. -/
  authentication : Fin subtreeHeight → Digest
deriving DecidableEq

/-- One FORS tree's part of a FORS signature: the selected leaf's secret value and its
authentication path. -/
structure ForsTreeSignature where
  /-- The secret value of the selected leaf. -/
  secret : Digest
  /-- The authentication path: the sibling at each height, from the leaf up. -/
  authentication : Fin forsHeight → Digest
deriving DecidableEq

/-- A FORS signature: one revealed leaf and path per FORS tree. -/
abbrev ForsSignature := Fin forsTrees → ForsTreeSignature

/-- A hypertree signature: one XMSS signature per layer, bottom layer first. -/
abbrev HypertreeSignature := Fin layers → XmssSignature

/-- An SLH-DSA signature: the randomizer, the FORS signature and the hypertree signature. -/
structure Signature where
  /-- The randomizer `R`. -/
  randomizer : Digest
  /-- The FORS signature of the message digest's indices. -/
  fors : ForsSignature
  /-- The hypertree signature of the FORS public key. -/
  hypertree : HypertreeSignature
deriving DecidableEq

/-- The big-endian encodings of a family of `n`-byte values, concatenated in index order. -/
@[expose] def digestArrayBytes {size : Nat} (values : Fin size → Digest) : Bytes :=
  (List.ofFn fun i => bytesBE n (values i)).flatten


end SLHDSA.SHAKE128s
