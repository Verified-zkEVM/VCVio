/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.RandomOracleModel
public import Mathlib.Data.BitVec
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# SLH-DSA-SHAKE-128s (FIPS 205)

Pure SLH-DSA with deterministic signing, at the 128s parameters and with the SHAKE input formats.
All hash functions are one shared random oracle with 30-byte answers; the 16-byte hashes are
their prefixes, as with SHAKE.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity

/-! ## Parameters (Table 2) -/

def n : Nat := 16
def totalHeight : Nat := 63
def layers : Nat := 7
def subtreeHeight : Nat := 9
def forsHeight : Nat := 12
def forsTrees : Nat := 14
def winternitzBits : Nat := 4
def w : Nat := 2 ^ winternitzBits
def messageDigits : Nat := 8 * n / winternitzBits
def checksumDigits : Nat := 3
def chains : Nat := messageDigits + checksumDigits
/-- Output length of `H_msg`, in bytes. -/
def messageDigestBytes : Nat := 30
/-- At most `2 ^ 64` signatures per key. -/
def signingLimit : Nat := 2 ^ 64
def signatureBytes : Nat := (1 + forsTrees * (1 + forsHeight) + totalHeight + layers * chains) * n

/-! ## Data -/

abbrev Bytes := List UInt8
abbrev Digest := BitVec (8 * n)
abbrev HashOutput := BitVec (8 * messageDigestBytes)

structure PublicKey where
  seed : Digest
  root : Digest
deriving DecidableEq

structure SecretKey where
  seed : Digest
  prf : Digest
  publicKey : PublicKey
deriving DecidableEq

/-- A signing request: message and context. -/
structure Message where
  message : Bytes
  context : Bytes
deriving DecidableEq

/-- Big-endian encoding (Algorithm 3). -/
def bytesBE (byteCount : Nat) (value : BitVec (8 * byteCount)) : Bytes :=
  (List.ofFn fun i : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * i.val) 8)).reverse

/-! ## Addresses (Section 4.2, 32-byte form) -/

inductive AddressType where
  | wotsHash | wotsPk | tree | forsTree | forsRoots | wotsPrf | forsPrf
deriving DecidableEq

def AddressType.code : AddressType → BitVec 32
  | .wotsHash => 0
  | .wotsPk => 1
  | .tree => 2
  | .forsTree => 3
  | .forsRoots => 4
  | .wotsPrf => 5
  | .forsPrf => 6

structure Address where
  layer : BitVec 32 := 0
  tree : BitVec 96 := 0
  kind : AddressType := .wotsHash
  keyPair : BitVec 32 := 0
  chainOrHeight : BitVec 32 := 0
  hashOrIndex : BitVec 32 := 0
deriving DecidableEq

def Address.toBytes (address : Address) : Bytes :=
  bytesBE 4 address.layer ++ bytesBE 12 address.tree ++ bytesBE 4 address.kind.code ++
    bytesBE 4 address.keyPair ++ bytesBE 4 address.chainOrHeight ++ bytesBE 4 address.hashOrIndex

def Address.setTypeAndClear (address : Address) (kind : AddressType) : Address :=
  { address with kind, keyPair := 0, chainOrHeight := 0, hashOrIndex := 0 }

/-! ## Hashing (Section 11.1, as one random oracle) -/

abbrev HashSpec := Xmss.RandomOracleModel.HashSpec Bytes HashOutput
abbrev OracleWorld := Xmss.RandomOracleModel.World Bytes HashOutput

namespace Hashing

/-- The first 16 bytes of an answer. -/
def truncate (answer : HashOutput) : Digest :=
  answer.extractLsb' (8 * (messageDigestBytes - n)) (8 * n)

/-- Input of `F`, `H`, `T_l` and `PRF`: `PK.seed ‖ ADRS ‖ payload`. -/
def tweakableInput (seed : Digest) (address : Address) (payload : Bytes) : Bytes :=
  bytesBE n seed ++ address.toBytes ++ payload

/-- Input of `PRF_msg`, with `opt_rand = PK.seed`. -/
def randomizerInput (prf seed : Digest) (message : Bytes) : Bytes :=
  bytesBE n prf ++ bytesBE n seed ++ message

/-- Input of `H_msg`. -/
def messageInput (randomizer : Digest) (pk : PublicKey) (message : Bytes) : Bytes :=
  bytesBE n randomizer ++ bytesBE n pk.seed ++ bytesBE n pk.root ++ message

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def hash (input : Bytes) : m HashOutput := query (spec := HashSpec) input

def shortHash (input : Bytes) : m Digest := do
  return truncate (← hash input)

def tweakable (seed : Digest) (address : Address) (payload : Bytes) : m Digest :=
  shortHash (tweakableInput seed address payload)

def derive (publicSeed secretSeed : Digest) (address : Address) : m Digest :=
  tweakable publicSeed address (bytesBE n secretSeed)

def randomizer (prf seed : Digest) (message : Bytes) : m Digest :=
  shortHash (randomizerInput prf seed message)

def messageDigest (randomizer : Digest) (pk : PublicKey) (message : Bytes) : m HashOutput :=
  hash (messageInput randomizer pk message)

end Hashing

/-- Pure-mode framing `0 ‖ |ctx| ‖ ctx ‖ M` (Algorithms 22 and 24). -/
def Message.frame (request : Message) : Option Bytes :=
  if request.context.length ≤ 255 then
    some ([0, UInt8.ofNat request.context.length] ++ request.context ++ request.message)
  else none

/-! ## Signatures (Figures 10–17) -/

abbrev WotsSignature := Fin chains → Digest

structure XmssSignature where
  wots : WotsSignature
  authentication : Fin subtreeHeight → Digest
deriving DecidableEq

structure ForsTreeSignature where
  secret : Digest
  authentication : Fin forsHeight → Digest
deriving DecidableEq

abbrev ForsSignature := Fin forsTrees → ForsTreeSignature
abbrev HypertreeSignature := Fin layers → XmssSignature

structure Signature where
  randomizer : Digest
  fors : ForsSignature
  hypertree : HypertreeSignature
deriving DecidableEq

/-- `Fin.cases` by direct matching. Core's goes through `Fin.induction`, which evaluates its
unused argument, so compiled nested uses take exponential time; `@[csimp]` swaps it in. -/
def finCases {n : Nat} {motive : Fin (n + 1) → Sort _} (zero : motive 0)
    (succ : ∀ i : Fin n, motive i.succ) : ∀ i, motive i
  | ⟨0, hi⟩ => by rwa [Fin.mk_zero]
  | ⟨i + 1, hi⟩ => succ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

@[csimp] theorem fin_cases_eq_finCases : @Fin.cases = @finCases := by
  funext n motive zero succ i
  rcases i with ⟨_ | i, hi⟩ <;> rfl

/-- Run the indexed computations in increasing order. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} :
    (size : Nat) → (Fin size → m α) → m (Fin size → α)
  | 0, _ => pure Fin.elim0
  | size + 1, f => do
    let first ← f 0
    let rest ← sequenceFin size (fun i => f i.succ)
    return Fin.cases first rest

def digestArrayBytes {size : Nat} (values : Fin size → Digest) : Bytes :=
  (List.ofFn fun i => bytesBE n (values i)).flatten

def XmssSignature.toBytes (signature : XmssSignature) : Bytes :=
  digestArrayBytes signature.wots ++ digestArrayBytes signature.authentication

def ForsTreeSignature.toBytes (signature : ForsTreeSignature) : Bytes :=
  bytesBE n signature.secret ++ digestArrayBytes signature.authentication

def Signature.toBytes (signature : Signature) : Bytes :=
  bytesBE n signature.randomizer ++
    (List.ofFn fun i => (signature.fors i).toBytes).flatten ++
    (List.ofFn fun i => (signature.hypertree i).toBytes).flatten

/-- The 16-byte big-endian field at a byte offset. -/
def Signature.readDigest (input : Bytes) (offset : Nat) : Digest :=
  ((input.drop offset).take n).foldl
    (fun value byte => (value <<< 8) ||| BitVec.ofNat (8 * n) byte.toNat) 0

/-- Parse a signature; anything but exactly `signatureBytes` bytes is rejected. -/
def Signature.fromBytes? (input : Bytes) : Option Signature :=
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

abbrev Digit := Fin w
abbrev MessageDigits := Fin messageDigits → Digit
abbrev Encoding := Fin chains → Digit

namespace Checksum

def messageDigit (message : Digest) (i : Fin messageDigits) : Digit :=
  (message.extractLsb' (winternitzBits * (messageDigits - 1 - i.val)) winternitzBits).toFin

def checksum (digits : MessageDigits) : Nat := ∑ i, (w - 1 - (digits i).val)

/-- The checksum's base-16 digits, most significant first. -/
def checksumDigit (csum : Nat) (i : Fin checksumDigits) : Digit :=
  ⟨csum / w ^ (checksumDigits - 1 - i.val) % w, Nat.mod_lt _ (by decide)⟩

def encode (message : Digest) : Encoding := fun i =>
  if h : i.val < messageDigits then messageDigit message ⟨i.val, h⟩
  else checksumDigit (checksum (messageDigit message))
    ⟨i.val - messageDigits, by have := i.isLt; simp only [chains] at *; omega⟩

end Checksum

/-! ## Message digest (Algorithms 19 and 20) -/

namespace MessageDigest

abbrev ForsTree := Fin forsTrees
abbrev ForsLeaf := Fin (2 ^ forsHeight)

/-- `idx_tree`: the low 54 bits of bytes 21–27. -/
def treeIndex (output : HashOutput) : BitVec (totalHeight - subtreeHeight) :=
  output.extractLsb' 16 (totalHeight - subtreeHeight)

/-- `idx_leaf`: the low 9 bits of bytes 28–29. -/
def leafIndex (output : HashOutput) : BitVec subtreeHeight :=
  output.extractLsb' 0 subtreeHeight

/-- The FORS indices: fourteen 12-bit digits of bytes 0–20, most significant first. -/
def forsIndices (output : HashOutput) (tree : ForsTree) : ForsLeaf :=
  (output.extractLsb' (72 + forsHeight * (forsTrees - 1 - tree.val)) forsHeight).toFin

end MessageDigest

/-! ## WOTS+ (Algorithms 5–8) -/

namespace Wots

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def chain (publicSeed : Digest) (address : Address) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
    let next ← Hashing.tweakable publicSeed
      { address with hashOrIndex := BitVec.ofNat 32 start } (bytesBE n value)
    chain publicSeed address (start + 1) steps next

def secretAddress (address : Address) (chainIndex : Fin chains) : Address :=
  { address.setTypeAndClear .wotsPrf with
    keyPair := address.keyPair, chainOrHeight := BitVec.ofNat 32 chainIndex.val }

def publicKeyAddress (address : Address) : Address :=
  { address.setTypeAndClear .wotsPk with keyPair := address.keyPair }

def publicKey (secretSeed publicSeed : Digest) (address : Address) : m Digest := do
  let endpoints ← sequenceFin chains fun i => do
    let secret ← Hashing.derive publicSeed secretSeed (secretAddress address i)
    chain publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
      0 (w - 1) secret
  Hashing.tweakable publicSeed (publicKeyAddress address) (digestArrayBytes endpoints)

def sign (message secretSeed publicSeed : Digest) (address : Address) : m WotsSignature :=
  sequenceFin chains fun i => do
    let secret ← Hashing.derive publicSeed secretSeed (secretAddress address i)
    chain publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
      0 (Checksum.encode message i).val secret

def publicKeyFromSignature (signature : WotsSignature) (message publicSeed : Digest)
    (address : Address) : m Digest := do
  let endpoints ← sequenceFin chains fun i =>
    let digit := (Checksum.encode message i).val
    chain publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
      digit (w - 1 - digit) (signature i)
  Hashing.tweakable publicSeed (publicKeyAddress address) (digestArrayBytes endpoints)

end Wots

/-! ## XMSS (Algorithms 9–11) -/

namespace Merkle

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def wotsAddress (address : Address) (index : Nat) : Address :=
  { address.setTypeAndClear .wotsHash with keyPair := BitVec.ofNat 32 index }

def nodeAddress (address : Address) (height index : Nat) : Address :=
  { address.setTypeAndClear .tree with
    chainOrHeight := BitVec.ofNat 32 height, hashOrIndex := BitVec.ofNat 32 index }

def node (secretSeed publicSeed : Digest) (address : Address) :
    Nat → Nat → m Digest
  | 0, index => Wots.publicKey secretSeed publicSeed (wotsAddress address index)
  | height + 1, index => do
    let left ← node secretSeed publicSeed address height (2 * index)
    let right ← node secretSeed publicSeed address height (2 * index + 1)
    Hashing.tweakable publicSeed (nodeAddress address (height + 1) index)
      (bytesBE n left ++ bytesBE n right)

def sign (message secretSeed publicSeed : Digest) (address : Address)
    (index : Fin (2 ^ subtreeHeight)) : m XmssSignature := do
  let authentication ← sequenceFin subtreeHeight fun j =>
    node secretSeed publicSeed address j.val (Nat.xor (index.val / 2 ^ j.val) 1)
  let wots ← Wots.sign message secretSeed publicSeed (wotsAddress address index.val)
  return { wots, authentication }

def publicKeyFromSignature (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature)
    (message publicSeed : Digest) (address : Address) : m Digest := do
  let leaf ← Wots.publicKeyFromSignature signature.wots message publicSeed
    (wotsAddress address index.val)
  (List.finRange subtreeHeight).foldlM (fun value j => do
    let payload := if index.val / 2 ^ j.val % 2 = 0 then
      bytesBE n value ++ bytesBE n (signature.authentication j)
      else bytesBE n (signature.authentication j) ++ bytesBE n value
    Hashing.tweakable publicSeed
      (nodeAddress address (j.val + 1) (index.val / 2 ^ (j.val + 1))) payload) leaf

end Merkle

/-! ## FORS (Algorithms 14–17) -/

namespace Fors

abbrev Indices := MessageDigest.ForsTree → MessageDigest.ForsLeaf

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def secretAddress (address : Address) (index : Nat) : Address :=
  { address.setTypeAndClear .forsPrf with
    keyPair := address.keyPair, hashOrIndex := BitVec.ofNat 32 index }

def nodeAddress (address : Address) (height index : Nat) : Address :=
  { address with
    chainOrHeight := BitVec.ofNat 32 height, hashOrIndex := BitVec.ofNat 32 index }

/-- Indices are global across the fourteen trees. -/
def secret (secretSeed publicSeed : Digest) (address : Address) (index : Nat) : m Digest :=
  Hashing.derive publicSeed secretSeed (secretAddress address index)

def node (secretSeed publicSeed : Digest) (address : Address) :
    Nat → Nat → m Digest
  | 0, index => do
    let value ← secret secretSeed publicSeed address index
    Hashing.tweakable publicSeed (nodeAddress address 0 index) (bytesBE n value)
  | height + 1, index => do
    let left ← node secretSeed publicSeed address height (2 * index)
    let right ← node secretSeed publicSeed address height (2 * index + 1)
    Hashing.tweakable publicSeed (nodeAddress address (height + 1) index)
      (bytesBE n left ++ bytesBE n right)

def sign (indices : Indices) (secretSeed publicSeed : Digest) (address : Address) :
    m ForsSignature :=
  sequenceFin forsTrees fun i => do
    let selected ← secret secretSeed publicSeed address
      (i.val * 2 ^ forsHeight + (indices i).val)
    let authentication ← sequenceFin forsHeight fun j =>
      node secretSeed publicSeed address j.val
        (i.val * 2 ^ (forsHeight - j.val) + Nat.xor ((indices i).val / 2 ^ j.val) 1)
    return { secret := selected, authentication }

def publicKeyFromSignature (signature : ForsSignature) (indices : Indices)
    (publicSeed : Digest) (address : Address) : m Digest := do
  let roots ← sequenceFin forsTrees fun i => do
    let index := i.val * 2 ^ forsHeight + (indices i).val
    let leaf ← Hashing.tweakable publicSeed (nodeAddress address 0 index)
      (bytesBE n (signature i).secret)
    (List.finRange forsHeight).foldlM (fun value j => do
      let payload := if (indices i).val / 2 ^ j.val % 2 = 0 then
        bytesBE n value ++ bytesBE n ((signature i).authentication j)
        else bytesBE n ((signature i).authentication j) ++ bytesBE n value
      Hashing.tweakable publicSeed
        (nodeAddress address (j.val + 1) (index / 2 ^ (j.val + 1))) payload) leaf
  let rootAddress := { address.setTypeAndClear .forsRoots with keyPair := address.keyPair }
  Hashing.tweakable publicSeed rootAddress (digestArrayBytes roots)

end Fors

/-! ## Hypertree (Algorithms 12 and 13) -/

namespace Hypertree

abbrev LeafIndex := Fin (2 ^ subtreeHeight)
abbrev TreeIndex := BitVec (totalHeight - subtreeHeight)

def address (layer tree : Nat) : Address :=
  { layer := BitVec.ofNat 32 layer, tree := BitVec.ofNat 96 tree }

def nextLeaf (tree : Nat) : LeafIndex :=
  ⟨tree % 2 ^ subtreeHeight, Nat.mod_lt _ (by decide)⟩

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def signLayers (secretSeed publicSeed : Digest) :
    (remaining : Nat) → Nat → Nat → LeafIndex → Digest →
      m (Fin remaining → XmssSignature)
  | 0, _, _, _, _ => pure Fin.elim0
  | remaining + 1, layer, tree, leaf, message => do
    let signature ← Merkle.sign message secretSeed publicSeed (address layer tree) leaf
    match remaining with
    | 0 => return Fin.cases signature Fin.elim0
    | remaining + 1 =>
      let root ← Merkle.publicKeyFromSignature leaf signature message publicSeed
        (address layer tree)
      let rest ← signLayers secretSeed publicSeed (remaining + 1) (layer + 1)
        (tree / 2 ^ subtreeHeight) (nextLeaf tree) root
      return Fin.cases signature rest

def sign (message secretSeed publicSeed : Digest) (tree : TreeIndex) (leaf : LeafIndex) :
    m HypertreeSignature :=
  signLayers secretSeed publicSeed layers 0 tree.toNat leaf message

def rootFromSignature (publicSeed : Digest) :
    (remaining : Nat) → (Fin remaining → XmssSignature) → Nat → Nat → LeafIndex → Digest →
      m Digest
  | 0, _, _, _, _, message => pure message
  | remaining + 1, signatures, layer, tree, leaf, message => do
    let root ← Merkle.publicKeyFromSignature leaf (signatures 0) message publicSeed
      (address layer tree)
    rootFromSignature publicSeed remaining (fun i => signatures i.succ) (layer + 1)
      (tree / 2 ^ subtreeHeight) (nextLeaf tree) root

def verify (message : Digest) (signature : HypertreeSignature) (pk : PublicKey)
    (tree : TreeIndex) (leaf : LeafIndex) : m Bool := do
  let root ← rootFromSignature pk.seed layers signature 0 tree.toNat leaf message
  return root == pk.root

end Hypertree

/-! ## SLH-DSA (Algorithms 18–22 and 24) -/

namespace Scheme

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Algorithm 18: the root of the top XMSS tree. -/
def keygenInternal (secretSeed prfSeed publicSeed : Digest) : m (SecretKey × PublicKey) := do
  let root ← Merkle.node secretSeed publicSeed (Hypertree.address (layers - 1) 0)
    subtreeHeight 0
  let pk : PublicKey := { seed := publicSeed, root }
  return ({ seed := secretSeed, prf := prfSeed, publicKey := pk }, pk)

/-- Algorithm 21: three uniform seeds. -/
noncomputable def keygen [HasQuery unifSpec m] : m (SecretKey × PublicKey) := do
  let secretSeed ← simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest)
  let prfSeed ← simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest)
  let publicSeed ← simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest)
  keygenInternal secretSeed prfSeed publicSeed

def forsAddress (digest : HashOutput) : Address :=
  { (Hypertree.address 0 (MessageDigest.treeIndex digest).toNat).setTypeAndClear .forsTree with
    keyPair := BitVec.ofNat 32 (MessageDigest.leafIndex digest).toNat }

/-- Algorithm 19, deterministic. -/
def signInternal (sk : SecretKey) (message : Bytes) : m Signature := do
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
def verifyInternal (pk : PublicKey) (message : Bytes) (signature : Signature) : m Bool := do
  let digest ← Hashing.messageDigest signature.randomizer pk message
  let forsKey ← Fors.publicKeyFromSignature signature.fors (MessageDigest.forsIndices digest)
    pk.seed (forsAddress digest)
  Hypertree.verify forsKey signature.hypertree pk
    (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin

/-- Algorithm 22; `none` for a context longer than 255 bytes. -/
def sign (sk : SecretKey) (request : Message) : m (Option Bytes) := do
  match request.frame with
  | none => return none
  | some message => return some (← signInternal sk message).toBytes

/-- Algorithm 24. -/
def verify (pk : PublicKey) (request : Message) (signature : Bytes) : m Bool := do
  match request.frame with
  | none => return false
  | some message =>
    match Signature.fromBytes? signature with
    | none => return false
    | some parsed => verifyInternal pk message parsed

end Scheme

end SlhDsaSecurity
