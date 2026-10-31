/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Game
public import HashSig.SLHDSA.Wots.Program.Laws
public import HashSig.SLHDSA.Hypertree.Program
public import Mathlib.Data.BitVec
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# SLH-DSA-SHAKE-128s (FIPS 205)

Pure SLH-DSA with deterministic signing, at the 128s parameters and with the SHAKE input formats.
All hash functions are one shared random oracle with 30-byte answers; the 16-byte hashes are
their prefixes, as with SHAKE.
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

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the random oracle. -/
@[expose] def hash (input : Bytes) : m HashOutput := query (spec := HashSpec) input

/-- The first `n` bytes of the random oracle's answer. -/
@[expose] def shortHash (input : Bytes) : m Digest := do
  return truncate (← hash input)

/-- The tweakable hashes `F`, `H` and `T_l`, keyed by the public seed and an address. -/
@[expose] def tweakable (seed : Digest) (address : Address) (payload : Bytes) : m Digest :=
  shortHash (tweakableInput seed address payload)

/-- `PRF(PK.seed, SK.seed, ADRS)`: a secret value derived from the secret seed at an address. -/
@[expose] def derive (publicSeed secretSeed : Digest) (address : Address) : m Digest :=
  tweakable publicSeed address (bytesBE n secretSeed)

/-- `PRF_msg(SK.prf, PK.seed, M)`: the randomizer `R` of a signature. -/
@[expose] def randomizer (prf seed : Digest) (message : Bytes) : m Digest :=
  shortHash (randomizerInput prf seed message)

/-- `H_msg(R, PK.seed, PK.root, M)`: the full message digest. -/
@[expose]
def messageDigest (randomizer : Digest) (pk : PublicKey) (message : Bytes) : m HashOutput :=
  hash (messageInput randomizer pk message)

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

/-- `Fin.cases` by direct matching. Core's goes through `Fin.induction`, which evaluates its
unused argument, so compiled nested uses take exponential time; `@[csimp]` swaps it in. -/
@[expose] def finCases {n : Nat} {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive i.succ) : ∀ i, motive i
  | ⟨0, hi⟩ => by rwa [Fin.mk_zero]
  | ⟨i + 1, hi⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- `Fin.cases` equals `finCases`, which lets the compiler run one as the other. -/
@[csimp] theorem fin_cases_eq_finCases : @Fin.cases = @finCases := by
  funext n motive zero succ i
  rcases i with ⟨_ | i, hi⟩ <;> rfl

/-- Run the indexed computations in increasing order. -/
@[expose] def sequenceFin {m : Type → Type} [Monad m] {α : Type} :
    (size : Nat) → (Fin size → m α) → m (Fin size → α)
  | 0, _ => pure Fin.elim0
  | size + 1, f => do
    let first ← f 0
    let rest ← sequenceFin size (fun i => f i.succ)
    return Fin.cases first rest

/-- The big-endian encodings of a family of `n`-byte values, concatenated in index order. -/
@[expose] def digestArrayBytes {size : Nat} (values : Fin size → Digest) : Bytes :=
  (List.ofFn fun i => bytesBE n (values i)).flatten

/-- The byte encoding of an XMSS signature: the WOTS+ signature, then the authentication path. -/
@[expose] def XmssSignature.toBytes (signature : XmssSignature) : Bytes :=
  digestArrayBytes signature.wots ++ digestArrayBytes signature.authentication

/-- The byte encoding of one FORS tree's part: the secret value, then the authentication path. -/
@[expose] def ForsTreeSignature.toBytes (signature : ForsTreeSignature) : Bytes :=
  bytesBE n signature.secret ++ digestArrayBytes signature.authentication

/-- The byte encoding of a signature: the randomizer, the FORS trees in order, then the hypertree
layers in order. -/
@[expose] def Signature.toBytes (signature : Signature) : Bytes :=
  bytesBE n signature.randomizer ++
    (List.ofFn fun i => (signature.fors i).toBytes).flatten ++
    (List.ofFn fun i => (signature.hypertree i).toBytes).flatten

/-- The 16-byte big-endian field at a byte offset. -/
@[expose] def Signature.readDigest (input : Bytes) (offset : Nat) : Digest :=
  ((input.drop offset).take n).foldl
    (fun value byte => (value <<< 8) ||| BitVec.ofNat (8 * n) byte.toNat) 0

/-- Parse a signature; anything but exactly `signatureBytes` bytes is rejected. -/
@[expose] def Signature.fromBytes? (input : Bytes) : Option Signature :=
  if input.length = signatureBytes then
    some {
      randomizer := readDigest input 0
      fors := fun i => {
        secret := readDigest input (n * (1 + i.val * (1 + forsHeight)))
        authentication := fun j =>
          readDigest input (n * (2 + i.val * (1 + forsHeight) + j.val)) }
      hypertree := fun i => {
        wots := fun j =>
          readDigest input
            (n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) + j.val))
        authentication := fun j =>
          readDigest input
            (n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) +
              chains + j.val)) } }
  else none

/-! ## WOTS+ checksum (Algorithms 7 and 8) -/

/-- A base-`w` digit. -/
abbrev Digit := Fin w

/-- The `len₁` base-`w` digits of a message. -/
abbrev MessageDigits := Fin messageDigits → Digit

/-- The `len` base-`w` digits a WOTS+ signature signs: the message's, then the checksum's. -/
abbrev Encoding := Fin chains → Digit

namespace Checksum

/-- The base-`w` digits of an `n`-byte message, most significant first. -/
@[expose] def messageDigit (message : Digest) (i : Fin messageDigits) : Digit :=
  (message.extractLsb' (winternitzBits * (messageDigits - 1 - i.val)) winternitzBits).toFin

/-- The WOTS+ checksum: the sum of `w - 1 - digit` over the message digits. -/
@[expose] def checksum (digits : MessageDigits) : Nat := ∑ i, (w - 1 - (digits i).val)

/-- The checksum's base-16 digits, most significant first. -/
@[expose] def checksumDigit (csum : Nat) (i : Fin checksumDigits) : Digit :=
  ⟨csum / w ^ (checksumDigits - 1 - i.val) % w, Nat.mod_lt _ (by decide)⟩

/-- The digits a WOTS+ signature signs: the message digits, then the checksum digits. -/
@[expose] def encode (message : Digest) : Encoding := fun i =>
  if h : i.val < messageDigits then messageDigit message ⟨i.val, h⟩
  else checksumDigit (checksum (messageDigit message))
    ⟨i.val - messageDigits, by have := i.isLt; simp only [chains] at *; omega⟩

end Checksum

/-! ## Message digest (Algorithms 19 and 20) -/

namespace MessageDigest

/-- The index of a FORS tree. -/
abbrev ForsTree := Fin forsTrees

/-- The index of a leaf of a FORS tree. -/
abbrev ForsLeaf := Fin (2 ^ forsHeight)

/-- `idx_tree`: the low 54 bits of bytes 21–27. -/
@[expose] def treeIndex (output : HashOutput) : BitVec (totalHeight - subtreeHeight) :=
  output.extractLsb' 16 (totalHeight - subtreeHeight)

/-- `idx_leaf`: the low 9 bits of bytes 28–29. -/
@[expose] def leafIndex (output : HashOutput) : BitVec subtreeHeight :=
  output.extractLsb' 0 subtreeHeight

/-- The FORS indices: fourteen 12-bit digits of bytes 0–20, most significant first. -/
@[expose] def forsIndices (output : HashOutput) (tree : ForsTree) : ForsLeaf :=
  (output.extractLsb' (72 + forsHeight * (forsTrees - 1 - tree.val)) forsHeight).toFin

end MessageDigest

/-! ## WOTS+ (Algorithms 5–8) -/

namespace Wots

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One addressed WOTS hash step over the digest representation. -/
@[expose] def chainStep (publicSeed : Digest) (address : Address)
    (position : Nat) (value : Digest) : m Digest :=
  Hashing.tweakable publicSeed
    { address with hashOrIndex := BitVec.ofNat 32 position } (bytesBE n value)

/-- Algorithm 5 (`chain`): `steps` steps of the hash chain of `address`, starting at position
`start`. -/
@[expose] def chain (publicSeed : Digest) (address : Address)
    (start steps : Nat) (value : Digest) : m Digest :=
  SLHDSA.Wots.Program.chain (chainStep publicSeed address) start steps value

/-- A zero-step WOTS chain returns its input. -/
@[simp] theorem chain_zero (publicSeed : Digest) (address : Address)
    (start : Nat) (value : Digest) :
    chain publicSeed address start 0 value = (pure value : m Digest) := by
  simp only [chain, SLHDSA.Wots.Program.chain_zero]

/-- A nonempty WOTS chain executes its initial addressed hash before the suffix. -/
theorem chain_succ (publicSeed : Digest) (address : Address)
    (start steps : Nat) (value : Digest) :
    chain (m := m) publicSeed address start (steps + 1) value = (do
      let next ← Hashing.tweakable publicSeed
        { address with hashOrIndex := BitVec.ofNat 32 start } (bytesBE n value)
      chain publicSeed address (start + 1) steps next) := by
  simp only [chain, SLHDSA.Wots.Program.chain_head, chainStep]

/-- The `WOTS_PRF` address of a chain's secret value, at the key pair of `address`. -/
@[expose] def secretAddress (address : Address) (chainIndex : Fin chains) : Address :=
  { address.setTypeAndClear .wotsPrf with
    keyPair := address.keyPair, chainOrHeight := BitVec.ofNat 32 chainIndex.val }

/-- The `WOTS_PK` address of the key pair of `address`. -/
@[expose] def publicKeyAddress (address : Address) : Address :=
  { address.setTypeAndClear .wotsPk with keyPair := address.keyPair }

/-- Algorithm 6 (`wots_pkGen`): the WOTS+ public key, the compression of all chain ends. -/
@[expose] def publicKey (secretSeed publicSeed : Digest) (address : Address) : m Digest :=
  SLHDSA.Wots.Program.run (I := Fin chains) (sequenceFin chains)
    (fun i => Hashing.derive publicSeed secretSeed (secretAddress address i))
    (fun i => chainStep publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val })
    (fun endpoints => Hashing.tweakable publicSeed (publicKeyAddress address)
      (digestArrayBytes endpoints)) (w - 1) .publicKey

/-- Public-key generation collects native digest chains, then compresses their endpoints. -/
theorem publicKey_eq (secretSeed publicSeed : Digest) (address : Address) :
    publicKey secretSeed publicSeed address = (do
      let endpoints ← sequenceFin chains fun i => do
        let secret ← Hashing.derive publicSeed secretSeed (secretAddress address i)
        chain publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
          0 (w - 1) secret
      Hashing.tweakable publicSeed (publicKeyAddress address) (digestArrayBytes endpoints) :
        m Digest) := by
  simp only [publicKey, SLHDSA.Wots.Program.run_publicKey,
    SLHDSA.Wots.Program.runTops_publicKey, SLHDSA.Wots.Program.runChains_eq, chain]

/-- Algorithm 7 (`wots_sign`): each chain's secret value advanced by its digit of the encoded
message. -/
@[expose] def sign (message secretSeed publicSeed : Digest) (address : Address) : m WotsSignature :=
  SLHDSA.Wots.Program.runTops (I := Fin chains) (sequenceFin chains)
    (fun i => Hashing.derive publicSeed secretSeed (secretAddress address i))
    (fun i => chainStep publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val })
    (w - 1) (.sign (fun i => (Checksum.encode message i).val))

/-- Signing retains the secret-derivation action before each native digest chain. -/
theorem sign_eq (message secretSeed publicSeed : Digest) (address : Address) :
    sign message secretSeed publicSeed address = (sequenceFin chains fun i => do
      let secret ← Hashing.derive publicSeed secretSeed (secretAddress address i)
      chain publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
        0 (Checksum.encode message i).val secret : m WotsSignature) := by
  simp only [sign, SLHDSA.Wots.Program.runTops_sign,
    SLHDSA.Wots.Program.runChains_eq, chain]

/-- Algorithm 8 (`wots_pkFromSig`): each chain completed from the signature, then the ends
compressed. -/
@[expose] def publicKeyFromSignature (signature : WotsSignature) (message publicSeed : Digest)
    (address : Address) : m Digest :=
  SLHDSA.Wots.Program.run (I := Fin chains) (sequenceFin chains)
    (fun i => pure (signature i))
    (fun i => chainStep publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val })
    (fun endpoints => Hashing.tweakable publicSeed (publicKeyAddress address)
      (digestArrayBytes endpoints)) (w - 1)
    (.recover signature (fun i => (Checksum.encode message i).val))

/-- Recovery collects native signature suffixes and compresses their endpoints. -/
theorem publicKeyFromSignature_eq [LawfulMonad m]
    (signature : WotsSignature) (message publicSeed : Digest) (address : Address) :
    publicKeyFromSignature signature message publicSeed address = (do
      let endpoints ← sequenceFin chains fun i =>
        let digit := (Checksum.encode message i).val
        chain publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
          digit (w - 1 - digit) (signature i)
      Hashing.tweakable publicSeed (publicKeyAddress address) (digestArrayBytes endpoints) :
        m Digest) := by
  simp only [publicKeyFromSignature, SLHDSA.Wots.Program.run_recover,
    SLHDSA.Wots.Program.runTops_recover, chain]

end Wots

/-! ## XMSS (Algorithms 9–11) -/

namespace Merkle

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The `WOTS_HASH` address of the WOTS+ key at leaf `index` of the XMSS tree of `address`. -/
@[expose] def wotsAddress (address : Address) (index : Nat) : Address :=
  { address.setTypeAndClear .wotsHash with keyPair := BitVec.ofNat 32 index }

/-- The `TREE` address of the node at height `height` and index `index`. -/
@[expose] def nodeAddress (address : Address) (height index : Nat) : Address :=
  { address.setTypeAndClear .tree with
    chainOrHeight := BitVec.ofNat 32 height, hashOrIndex := BitVec.ofNat 32 index }

/-- Algorithm 9 (`xmss_node`): the node at height `height` and index `index` of the XMSS tree of
`address`. -/
@[expose] def node (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) : m Digest :=
  PerfectMerkleTree.merkleRootM
    (fun t => Wots.publicKey secretSeed publicSeed (wotsAddress address t))
    (fun z t left right =>
      Hashing.tweakable publicSeed (nodeAddress address z t)
        (bytesBE n left ++ bytesBE n right)) height index

/-- A height-zero XMSS subtree computes the WOTS+ public key at its leaf. -/
theorem node_zero (secretSeed publicSeed : Digest) (address : Address) (index : Nat) :
    node (m := m) secretSeed publicSeed address 0 index =
      (Wots.publicKey secretSeed publicSeed (wotsAddress address index) : m Digest) := rfl

/-- An XMSS parent evaluates its left and right children before its node hash. -/
theorem node_succ (secretSeed publicSeed : Digest) (address : Address) (height index : Nat) :
    node (m := m) secretSeed publicSeed address (height + 1) index = (do
      let left ← node secretSeed publicSeed address height (2 * index)
      let right ← node secretSeed publicSeed address height (2 * index + 1)
      Hashing.tweakable publicSeed (nodeAddress address (height + 1) index)
        (bytesBE n left ++ bytesBE n right) : m Digest) := rfl

/-- The leaf-first sibling path of an XMSS leaf at every natural height and index. -/
@[expose] def authenticationPath (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) : m (Vector Digest height) :=
  PerfectMerkleTree.intrinsicAuthPathM
    (fun t => Wots.publicKey secretSeed publicSeed (wotsAddress address t))
    (fun z t left right =>
      Hashing.tweakable publicSeed (nodeAddress address z t)
        (bytesBE n left ++ bytesBE n right)) index height

/-- Algorithm 10 (`xmss_sign`): a WOTS+ signature of `message` under the key of leaf `index`, with
that leaf's authentication path. The sibling path is evaluated before WOTS+ signing. -/
@[expose] def sign (message secretSeed publicSeed : Digest) (address : Address)
    (index : Fin (2 ^ subtreeHeight)) : m XmssSignature := do
  let authentication ← authenticationPath secretSeed publicSeed address subtreeHeight index.val
  let wots ← Wots.sign message secretSeed publicSeed (wotsAddress address index.val)
  return { wots, authentication := fun j => authentication[j] }

/-- Recover an XMSS subtree root from its leaf value and leaf-first sibling path. -/
@[expose] def climb (publicSeed : Digest) (address : Address) (index : Nat)
    (leaf : Digest) (authentication : List Digest) : m Digest :=
  PerfectMerkleTree.climbM
    (fun height index left right =>
      Hashing.tweakable publicSeed (nodeAddress address height index)
        (bytesBE n left ++ bytesBE n right)) index leaf authentication

/-- Algorithm 11 (`xmss_pkFromSig`): the WOTS+ public key recovered from the signature, hashed up
the authentication path to a root. -/
@[expose] def publicKeyFromSignature (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message publicSeed : Digest) (address : Address) : m Digest := do
  let leaf ← Wots.publicKeyFromSignature signature.wots message publicSeed
    (wotsAddress address index.val)
  climb publicSeed address index.val leaf (List.ofFn signature.authentication)

end Merkle

/-! ## FORS (Algorithms 14–17) -/

namespace Fors

/-- The selected leaf of each FORS tree. -/
abbrev Indices := MessageDigest.ForsTree → MessageDigest.ForsLeaf

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The `FORS_PRF` address of the secret value of global leaf `index`, at the key pair of
`address`. -/
@[expose] def secretAddress (address : Address) (index : Nat) : Address :=
  { address.setTypeAndClear .forsPrf with
    keyPair := address.keyPair, hashOrIndex := BitVec.ofNat 32 index }

/-- The address of the FORS node at height `height` and global index `index`. -/
@[expose] def nodeAddress (address : Address) (height index : Nat) : Address :=
  { address with
    chainOrHeight := BitVec.ofNat 32 height, hashOrIndex := BitVec.ofNat 32 index }

/-- Indices are global across the fourteen trees. -/
@[expose]
def secret (secretSeed publicSeed : Digest) (address : Address) (index : Nat) : m Digest :=
  Hashing.derive publicSeed secretSeed (secretAddress address index)

/-- Algorithm 15 (`fors_node`): the FORS node at height `height` and global index `index`. -/
@[expose] def node (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) : m Digest :=
  PerfectMerkleTree.merkleRootM
    (fun t => do
      let value ← secret secretSeed publicSeed address t
      Hashing.tweakable publicSeed (nodeAddress address 0 t) (bytesBE n value))
    (fun z t left right =>
      Hashing.tweakable publicSeed (nodeAddress address z t)
        (bytesBE n left ++ bytesBE n right)) height index

/-- A height-zero FORS subtree derives its secret and hashes the resulting leaf. -/
theorem node_zero (secretSeed publicSeed : Digest) (address : Address) (index : Nat) :
    node secretSeed publicSeed address 0 index = (do
      let value ← secret secretSeed publicSeed address index
      Hashing.tweakable publicSeed (nodeAddress address 0 index) (bytesBE n value) : m Digest) :=
  rfl

/-- A FORS parent evaluates its left subtree, its right subtree, and then its node hash. -/
theorem node_succ (secretSeed publicSeed : Digest) (address : Address) (height index : Nat) :
    node secretSeed publicSeed address (height + 1) index = (do
      let left ← node secretSeed publicSeed address height (2 * index)
      let right ← node secretSeed publicSeed address height (2 * index + 1)
      Hashing.tweakable publicSeed (nodeAddress address (height + 1) index)
        (bytesBE n left ++ bytesBE n right) : m Digest) := rfl

/-- The leaf-first sibling path of a global FORS leaf, with its height retained in the type. -/
@[expose] def authenticationPath (secretSeed publicSeed : Digest) (address : Address)
    (height index : Nat) : m (Vector Digest height) :=
  PerfectMerkleTree.intrinsicAuthPathM (node secretSeed publicSeed address 0)
    (fun z t left right =>
      Hashing.tweakable publicSeed (nodeAddress address z t)
        (bytesBE n left ++ bytesBE n right)) index height

/-- Algorithm 16 (`fors_sign`): for each tree, the selected leaf's secret value and authentication
path. -/
@[expose] def sign (indices : Indices) (secretSeed publicSeed : Digest) (address : Address) :
    m ForsSignature :=
  sequenceFin forsTrees fun i => do
    let index := i.val * 2 ^ forsHeight + (indices i).val
    let selected ← secret secretSeed publicSeed address index
    let authentication ← authenticationPath secretSeed publicSeed address forsHeight index
    return { secret := selected, authentication := fun j => authentication[j] }

/-- Recover a FORS root from its leaf value and leaf-first sibling path. -/
@[expose] def climb (publicSeed : Digest) (address : Address) (index : Nat)
    (leaf : Digest) (authentication : List Digest) : m Digest :=
  PerfectMerkleTree.climbM
    (fun height index left right =>
      Hashing.tweakable publicSeed (nodeAddress address height index)
        (bytesBE n left ++ bytesBE n right)) index leaf authentication

/-- Algorithm 17 (`fors_pkFromSig`): each tree's root recovered from the signature, then the roots
compressed into the FORS public key. -/
@[expose] def publicKeyFromSignature (signature : ForsSignature) (indices : Indices)
    (publicSeed : Digest) (address : Address) : m Digest := do
  let roots ← sequenceFin forsTrees fun i => do
    let index := i.val * 2 ^ forsHeight + (indices i).val
    let leaf ← Hashing.tweakable publicSeed (nodeAddress address 0 index)
      (bytesBE n (signature i).secret)
    climb publicSeed address index leaf (List.ofFn (signature i).authentication)
  let rootAddress := { address.setTypeAndClear .forsRoots with keyPair := address.keyPair }
  Hashing.tweakable publicSeed rootAddress (digestArrayBytes roots)

end Fors

/-! ## Hypertree (Algorithms 12 and 13) -/

namespace Hypertree

/-- The index of a leaf of an XMSS tree. -/
abbrev LeafIndex := Fin (2 ^ subtreeHeight)

/-- The index of an XMSS tree of the bottom layer. -/
abbrev TreeIndex := BitVec (totalHeight - subtreeHeight)

/-- The address of XMSS tree `tree` of layer `layer`. -/
@[expose] def address (layer tree : Nat) : Address :=
  { layer := BitVec.ofNat 32 layer, tree := BitVec.ofNat 96 tree }

/-- The leaf of the next layer that signs the root of tree `tree`: its low `h'` bits. -/
@[expose] def nextLeaf (tree : Nat) : LeafIndex :=
  ⟨tree % 2 ^ subtreeHeight, Nat.mod_lt _ (by decide)⟩

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- A raw paper position keeps layer and tree indices natural until address encoding. -/
abbrev ProgramPosition (_remaining : Nat) := Nat × Nat × LeafIndex

/-- Advance raw tree coordinates before the next layer's word encoding. -/
@[expose] def nextProgramPosition (remaining : Nat)
    (position : ProgramPosition (remaining + 2)) : ProgramPosition (remaining + 1) :=
  (position.1 + 1, position.2.1 / 2 ^ subtreeHeight, nextLeaf position.2.1)

/-- The layer signatures in increasing order, with recovery only between successive layers. -/
@[expose] def signVector (secretSeed publicSeed : Digest) (remaining layer tree : Nat)
    (leaf : LeafIndex) (message : Digest) : m (Vector XmssSignature remaining) :=
  SLHDSA.Hypertree.Program.signLayers nextProgramPosition
    (fun _ current value => Merkle.sign value secretSeed publicSeed
      (address current.1 current.2.1) current.2.2)
    (fun _ current signature value => Merkle.publicKeyFromSignature current.2.2 signature value
      publicSeed (address current.1 current.2.1)) false remaining (layer, tree, leaf) message

/-- Algorithm 12 (`ht_sign`) over the remaining layers, as a finite family of layer signatures. -/
@[expose] def signLayers (secretSeed publicSeed : Digest) (remaining layer tree : Nat)
    (leaf : LeafIndex) (message : Digest) : m (Fin remaining → XmssSignature) :=
  (fun (values : Vector XmssSignature remaining) (i : Fin remaining) => values[i]) <$>
    signVector secretSeed publicSeed remaining layer tree leaf message

/-- Prepending a component prepends the finite-family reading of a vector. -/
theorem vectorFamily_insertIdx {α : Type*} {remaining : Nat}
    (values : Vector α remaining) (value : α) :
    (fun i : Fin (remaining + 1) => (values.insertIdx 0 value)[i]) =
      Fin.cases value (fun i : Fin remaining => values[i]) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Vector.insertIdx_zero]
  · simp [Vector.insertIdx_zero, Vector.getElem_append_right]

/-- A singleton vector reads as its canonical singleton finite family. -/
theorem vectorFamily_singleton {α : Type*} (value : α) :
    (fun i : Fin 1 => (#v[value])[i]) = Fin.cases value Fin.elim0 := by
  funext i
  refine Fin.cases ?_ (fun i => i.elim0) i
  simp

/-- No layer signs or recovers when the remaining count is zero. -/
theorem signLayers_zero [LawfulMonad m] (secretSeed publicSeed : Digest)
    (layer tree : Nat) (leaf : LeafIndex) (message : Digest) :
    signLayers secretSeed publicSeed 0 layer tree leaf message = (pure Fin.elim0 : m _) := by
  simp only [signLayers, signVector, SLHDSA.Hypertree.Program.signLayers_zero, map_pure]
  congr 1
  funext i
  exact i.elim0

/-- A singleton paper entry signs without executing public-key recovery. -/
theorem signLayers_one [LawfulMonad m] (secretSeed publicSeed : Digest)
    (layer tree : Nat) (leaf : LeafIndex) (message : Digest) :
    signLayers secretSeed publicSeed 1 layer tree leaf message = (do
      let signature ← Merkle.sign message secretSeed publicSeed (address layer tree) leaf
      return Fin.cases signature Fin.elim0 : m _) := by
  simp only [signLayers, signVector, SLHDSA.Hypertree.Program.signLayers_one_false,
    map_bind, map_pure]
  apply bind_congr
  intro signature
  exact congrArg (fun family : Fin 1 → XmssSignature => (pure family : m _))
    (vectorFamily_singleton signature)

/-- Nonfinal paper entries recover their component before signing the next layer. -/
theorem signLayers_add_two [LawfulMonad m] (secretSeed publicSeed : Digest)
    (remaining layer tree : Nat) (leaf : LeafIndex) (message : Digest) :
    signLayers secretSeed publicSeed (remaining + 2) layer tree leaf message = (do
      let signature ← Merkle.sign message secretSeed publicSeed (address layer tree) leaf
      let root ← Merkle.publicKeyFromSignature leaf signature message publicSeed
        (address layer tree)
      let rest ← signLayers secretSeed publicSeed (remaining + 1) (layer + 1)
        (tree / 2 ^ subtreeHeight) (nextLeaf tree) root
      return Fin.cases signature rest : m _) := by
  simp only [signLayers, signVector, SLHDSA.Hypertree.Program.signLayers_add_two,
    nextProgramPosition, map_bind, map_pure]
  apply bind_congr
  intro signature
  apply bind_congr
  intro root
  change (do
    let rest ← signVector secretSeed publicSeed (remaining + 1) (layer + 1)
      (tree / 2 ^ subtreeHeight) (nextLeaf tree) root
    return fun i : Fin (remaining + 2) => (rest.insertIdx 0 signature)[i]) = (do
    let rest ← signLayers secretSeed publicSeed (remaining + 1) (layer + 1)
      (tree / 2 ^ subtreeHeight) (nextLeaf tree) root
    return Fin.cases signature rest)
  rw [signLayers, bind_map_left]
  apply bind_congr
  intro rest
  exact congrArg (fun family : Fin (remaining + 2) → XmssSignature => (pure family : m _))
    (vectorFamily_insertIdx rest signature)

/-- A nonempty layer family signs its head, then recovers exactly when another layer remains. -/
theorem signLayers_succ [LawfulMonad m] (secretSeed publicSeed : Digest)
    (remaining layer tree : Nat) (leaf : LeafIndex) (message : Digest) :
    signLayers secretSeed publicSeed (remaining + 1) layer tree leaf message =
      ((Merkle.sign message secretSeed publicSeed (address layer tree) leaf : m XmssSignature) >>=
        fun signature => Nat.casesOn (motive := fun count => m (Fin (count + 1) → XmssSignature))
          remaining (pure (Fin.cases signature Fin.elim0)) (fun remaining => do
            let root ← Merkle.publicKeyFromSignature leaf signature message publicSeed
              (address layer tree)
            let rest ← signLayers secretSeed publicSeed (remaining + 1) (layer + 1)
              (tree / 2 ^ subtreeHeight) (nextLeaf tree) root
            return Fin.cases signature rest)) := by
  cases remaining with
  | zero => exact signLayers_one secretSeed publicSeed layer tree leaf message
  | succ remaining =>
      exact signLayers_add_two secretSeed publicSeed remaining layer tree leaf message

/-- Algorithm 12 (`ht_sign`) at the bottom tree and leaf selected by the message digest. -/
@[expose] def sign (message secretSeed publicSeed : Digest) (tree : TreeIndex) (leaf : LeafIndex) :
    m HypertreeSignature :=
  signLayers secretSeed publicSeed layers 0 tree.toNat leaf message

/-- Recover a root at every supplied layer, retaining the raw position trajectory. -/
@[expose] def rootFromSignature (publicSeed : Digest) (remaining : Nat)
    (signatures : Fin remaining → XmssSignature) (layer tree : Nat) (leaf : LeafIndex)
    (message : Digest) : m Digest :=
  SLHDSA.Hypertree.Program.recoverLayers nextProgramPosition
    (fun _ current signature value => Merkle.publicKeyFromSignature current.2.2 signature value
      publicSeed (address current.1 current.2.1))
    remaining (layer, tree, leaf) message (Vector.ofFn signatures)

/-- An empty supplied signature returns its message without any recovery action. -/
theorem rootFromSignature_zero (publicSeed : Digest) (signatures : Fin 0 → XmssSignature)
    (layer tree : Nat) (leaf : LeafIndex) (message : Digest) :
    rootFromSignature publicSeed 0 signatures layer tree leaf message = (pure message : m _) := rfl

/-- The head of a vector built from a family is the family's zero coordinate. -/
theorem vectorOfFn_head {α : Type*} {remaining : Nat} (values : Fin (remaining + 1) → α) :
    (Vector.ofFn values).head = values 0 := by
  simp [Vector.head]

/-- The tail of a vector built from a family reads the successor coordinates. -/
theorem vectorOfFn_tail {α : Type*} {remaining : Nat} (values : Fin (remaining + 1) → α) :
    (Vector.ofFn values).tail = Vector.ofFn (fun i : Fin remaining => values i.succ) := by
  apply Vector.ext
  intro i hi
  simp [Vector.tail, Nat.add_comm]

/-- Each recovered root becomes the next layer's input, including the final returned root. -/
theorem rootFromSignature_succ [LawfulMonad m] (publicSeed : Digest) (remaining : Nat)
    (signatures : Fin (remaining + 1) → XmssSignature) (layer tree : Nat) (leaf : LeafIndex)
    (message : Digest) :
    rootFromSignature publicSeed (remaining + 1) signatures layer tree leaf message = (do
      let root ← Merkle.publicKeyFromSignature leaf (signatures 0) message publicSeed
        (address layer tree)
      rootFromSignature publicSeed remaining (fun i => signatures i.succ) (layer + 1)
        (tree / 2 ^ subtreeHeight) (nextLeaf tree) root : m Digest) := by
  cases remaining with
  | zero =>
      change (Merkle.publicKeyFromSignature leaf (Vector.ofFn signatures).head message publicSeed
        (address layer tree) : m Digest) =
        ((Merkle.publicKeyFromSignature leaf (signatures 0) message publicSeed
          (address layer tree) : m Digest) >>= fun root => pure root)
      simp only [vectorOfFn_head, bind_pure]
  | succ remaining =>
      simp only [rootFromSignature, SLHDSA.Hypertree.Program.recoverLayers_add_two,
        nextProgramPosition, vectorOfFn_head, vectorOfFn_tail]

/-- Algorithm 13 (`ht_verify`): whether the recovered top root is `PK.root`. -/
@[expose] def verify (message : Digest) (signature : HypertreeSignature) (pk : PublicKey)
    (tree : TreeIndex) (leaf : LeafIndex) : m Bool := do
  let root ← rootFromSignature pk.seed layers signature 0 tree.toNat leaf message
  return root == pk.root

end Hypertree

/-! ## SLH-DSA (Algorithms 18–22 and 24) -/

namespace Scheme

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Algorithm 18: the root of the top XMSS tree. -/
@[expose]
def keygenInternal (secretSeed prfSeed publicSeed : Digest) : m (SecretKey × PublicKey) := do
  let root ← Merkle.node secretSeed publicSeed (Hypertree.address (layers - 1) 0)
    subtreeHeight 0
  let pk : PublicKey := { seed := publicSeed, root }
  return ({ seed := secretSeed, prf := prfSeed, publicKey := pk }, pk)

/-- Algorithm 21: three uniform seeds. -/
@[expose] noncomputable def keygen [HasQuery unifSpec m] : m (SecretKey × PublicKey) := do
  let secretSeed ← simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest)
  let prfSeed ← simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest)
  let publicSeed ← simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest)
  keygenInternal secretSeed prfSeed publicSeed

/-- The `FORS_TREE` address of the FORS instance a message digest selects. -/
@[expose] def forsAddress (digest : HashOutput) : Address :=
  { (Hypertree.address 0 (MessageDigest.treeIndex digest).toNat).setTypeAndClear .forsTree with
    keyPair := BitVec.ofNat 32 (MessageDigest.leafIndex digest).toNat }

/-- Algorithm 19, deterministic. -/
@[expose] def signInternal (sk : SecretKey) (message : Bytes) : m Signature := do
  let randomizer ← Hashing.randomizer sk.prf sk.publicKey.seed message
  let digest ← Hashing.messageDigest randomizer sk.publicKey message
  let indices := MessageDigest.forsIndices digest
  let address := forsAddress digest
  let fors ← Fors.sign indices sk.seed sk.publicKey.seed address
  let forsKey ← Fors.publicKeyFromSignature fors indices sk.publicKey.seed address
  let hypertree ← Hypertree.sign forsKey sk.seed sk.publicKey.seed
    (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin
  return { randomizer, fors, hypertree }

/-- Algorithm 20. -/
@[expose]
def verifyInternal (pk : PublicKey) (message : Bytes) (signature : Signature) : m Bool := do
  let digest ← Hashing.messageDigest signature.randomizer pk message
  let forsKey ← Fors.publicKeyFromSignature signature.fors (MessageDigest.forsIndices digest)
    pk.seed (forsAddress digest)
  Hypertree.verify forsKey signature.hypertree pk
    (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin

/-- Algorithm 22; `none` for a context longer than 255 bytes. -/
@[expose] def sign (sk : SecretKey) (request : Message) : m (Option Bytes) := do
  match request.frame with
  | none => return none
  | some message => return some (← signInternal sk message).toBytes

/-- Algorithm 24. -/
@[expose] def verify (pk : PublicKey) (request : Message) (signature : Bytes) : m Bool := do
  match request.frame with
  | none => return false
  | some message =>
    match Signature.fromBytes? signature with
    | none => return false
    | some parsed => verifyInternal pk message parsed

end Scheme

end SLHDSA.SHAKE128s
