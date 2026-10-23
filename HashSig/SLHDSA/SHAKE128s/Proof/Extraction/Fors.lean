/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.BinaryPath
public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Fors
public import HashSig.SLHDSA.SHAKE128s.Proof.Extraction.Wots

/-! Extraction from the actual FORS verifier, one tree at a time.

Recovering the genuine root of a single FORS tree with changed authentication data
contains a collision at one of that tree's own hash calls. Otherwise the recovered
secret leaf and all twelve siblings are exactly the genuine canonical values. This
mirrors `Extraction.Merkle.root_eq_canonical_or_collision` for the FORS trees. The
collision witness keeps the path position, so it names a concrete queried input. -/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Extraction.Fors

set_option backward.isDefEq.respectTransparency false

variable [HasQuery HashSpec Id]

/-- The global node index of the selected leaf in FORS tree `i`. -/
def leafIndex (indices : SlhDsaSecurity.Fors.Indices) (i : Fin forsTrees) : Nat :=
  i.val * 2 ^ forsHeight + (indices i).val

/-- The twelve authentication siblings of FORS tree `i`, padded past the tree height. -/
def siblings (signature : ForsSignature) (i : Fin forsTrees) (height : Nat) : Digest :=
  if h : height < forsHeight then (signature i).authentication ⟨height, h⟩ else 0

/-- The recovered leaf of FORS tree `i`: the compression of the revealed secret. -/
def recoveredLeaf (signature : ForsSignature) (indices : SlhDsaSecurity.Fors.Indices)
    (publicSeed : Digest) (address : Address) (i : Fin forsTrees) : Digest :=
  Hashing.tweakable (m := Id) publicSeed
    (SlhDsaSecurity.Fors.nodeAddress address 0 (leafIndex indices i))
    (bytesBE n (signature i).secret)

/-- The recovered root of FORS tree `i`, exactly as computed inside Algorithm 17
before the fourteen roots are compressed. -/
def recoveredRoot (signature : ForsSignature) (indices : SlhDsaSecurity.Fors.Indices)
    (publicSeed : Digest) (address : Address) (i : Fin forsTrees) : Digest :=
  (List.finRange forsHeight).foldl (fun value j =>
    let payload := if (indices i).val / 2 ^ j.val % 2 = 0 then
      bytesBE n value ++ bytesBE n ((signature i).authentication j)
      else bytesBE n ((signature i).authentication j) ++ bytesBE n value
    Hashing.tweakable (m := Id) publicSeed
      (SlhDsaSecurity.Fors.nodeAddress address (j.val + 1)
        (leafIndex indices i / 2 ^ (j.val + 1))) payload)
    (recoveredLeaf signature indices publicSeed address i)

set_option maxRecDepth 10000 in
/-- Reaching the genuine FORS tree root with changed authentication data gives a
collision on this verifier path. Otherwise its recovered secret leaf and all twelve
siblings are exactly the genuine values. -/
theorem root_eq_canonical_or_collision (secretSeed publicSeed : Digest)
    (address : Address) (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature)
    (i : Fin forsTrees)
    (hroot : recoveredRoot signature indices publicSeed address i =
      SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address forsHeight i.val) :
    let nodes : Nat → Nat → Digest :=
      SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address
    let combine : Nat → Nat → Digest → Digest → Digest := fun height nodeIndex left right =>
      Hashing.tweakable (m := Id) publicSeed
        (SlhDsaSecurity.Fors.nodeAddress address height nodeIndex)
        (BinaryPath.pairBytes (left, right))
    let leaf : Digest := recoveredLeaf signature indices publicSeed address i
    (leaf = nodes 0 (leafIndex indices i) ∧ ∀ j, (signature i).authentication j =
      nodes j.val (Nat.xor (leafIndex indices i / 2 ^ j.val) 1)) ∨
    ∃ j < forsHeight,
      BinaryPath.Collision nodes combine (leafIndex indices i) leaf (siblings signature i) j := by
  dsimp only
  set index := leafIndex indices i with hindex
  let nodes : Nat → Nat → Digest :=
    SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address
  let combine : Nat → Nat → Digest → Digest → Digest := fun height nodeIndex left right =>
    Hashing.tweakable (m := Id) publicSeed
      (SlhDsaSecurity.Fors.nodeAddress address height nodeIndex)
      (BinaryPath.pairBytes (left, right))
  let leaf : Digest := recoveredLeaf signature indices publicSeed address i
  -- The verifier fold equals the generic binary-path value function.
  have hfold : BinaryPath.value combine index leaf (siblings signature i) forsHeight =
      recoveredRoot signature indices publicSeed address i := by
    rw [BinaryPath.value_eq_fold]
    simp only [recoveredRoot, ← hindex]
    congr 1
    funext current j
    have hj := j.isLt
    have hparity : index / 2 ^ j.val % 2 = (indices i).val / 2 ^ j.val % 2 := by
      have heven := SlhDsaSecurity.Correctness.offset_even i.val forsHeight j.val hj
      rw [hindex, leafIndex,
        SlhDsaSecurity.Correctness.offset_div_pow _ _ _ _ (Nat.le_of_lt hj)]
      simp [Nat.add_mod, heven]
    simp only [siblings, dif_pos hj, BinaryPath.ordered, hparity]
    split <;> rfl
  -- The canonical FORS node recurrence matches the `combine` operation.
  have hpath := BinaryPath.canonical_or_collision nodes combine (fun _ _ => rfl)
    index leaf (siblings signature i) forsHeight (by
      rw [hfold, hroot]
      congr 1
      rw [hindex, leafIndex,
        SlhDsaSecurity.Correctness.offset_div_pow _ _ _ _ (Nat.le_refl _),
        Nat.sub_self, pow_zero, Nat.mul_one, Nat.div_eq_of_lt (indices i).isLt, Nat.add_zero])
  rcases hpath with ⟨hleaf, hsiblings⟩ | hcollision
  · refine Or.inl ⟨hleaf, fun j => ?_⟩
    simpa only [siblings, dif_pos j.isLt] using hsiblings j.val j.isLt
  · exact Or.inr hcollision

/-- The address of the final FORS root-compression call. -/
def rootAddress (address : Address) : Address :=
  { address.setTypeAndClear .forsRoots with keyPair := address.keyPair }

/-- The canonical root of each of the fourteen FORS trees under the genuine seeds. -/
def canonicalRoots (secretSeed publicSeed : Digest) (address : Address) :
    Fin forsTrees → Digest := fun i =>
  SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address forsHeight i.val

/-- Algorithm 17 compresses the fourteen per-tree recovered roots. -/
theorem publicKeyFromSignature_eq (signature : ForsSignature)
    (indices : SlhDsaSecurity.Fors.Indices) (publicSeed : Digest) (address : Address) :
    SlhDsaSecurity.Fors.publicKeyFromSignature (m := Id) signature indices publicSeed address =
      Hashing.tweakable (m := Id) publicSeed (rootAddress address)
        (digestArrayBytes (recoveredRoot signature indices publicSeed address)) := by
  simp only [SlhDsaSecurity.Fors.publicKeyFromSignature, Correctness.sequenceFin_id, bind,
    Correctness.foldlM_id, rootAddress]
  rfl

/-- A collision at the final FORS root-compression call: two different root
tuples whose full oracle inputs are distinct but compress identically. -/
def CompressionCollision (actualRoots canonicalRoots : Fin forsTrees → Digest)
    (publicSeed : Digest) (address : Address) : Prop :=
  let actualInput := Hashing.tweakableInput publicSeed (rootAddress address)
    (digestArrayBytes actualRoots)
  let canonicalInput := Hashing.tweakableInput publicSeed (rootAddress address)
    (digestArrayBytes canonicalRoots)
  actualInput ≠ canonicalInput ∧
    Hashing.shortHash (m := Id) actualInput = Hashing.shortHash (m := Id) canonicalInput

/-- A FORS signature recovering the genuine FORS public key either reproduces every
canonical tree root, or has a collision at its root-compression call. No collision
resistance is assumed. -/
theorem publicKey_eq_canonical_roots_or_collision (secretSeed publicSeed : Digest)
    (address : Address) (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature)
    (hpk : SlhDsaSecurity.Fors.publicKeyFromSignature (m := Id) signature indices publicSeed address =
      Hashing.tweakable (m := Id) publicSeed (rootAddress address)
        (digestArrayBytes (canonicalRoots secretSeed publicSeed address))) :
    recoveredRoot signature indices publicSeed address =
        canonicalRoots secretSeed publicSeed address ∨
      CompressionCollision (recoveredRoot signature indices publicSeed address)
        (canonicalRoots secretSeed publicSeed address) publicSeed address := by
  rw [publicKeyFromSignature_eq] at hpk
  by_cases hroots : recoveredRoot signature indices publicSeed address =
      canonicalRoots secretSeed publicSeed address
  · exact Or.inl hroots
  · refine Or.inr ⟨fun hinput => hroots ?_, hpk⟩
    exact SlhDsaSecurity.Extraction.Wots.digestArrayBytes_injective forsTrees
      (Hashing.tweakableInput_injective hinput).2.2

set_option maxRecDepth 10000 in
/-- Full FORS structural decomposition: a FORS signature recovering the genuine FORS public
key either collides at the root compression, or for every one of the fourteen trees it
collides on that tree's authentication path or reproduces the canonical secret leaf and all
twelve siblings. This composes the compression and per-tree extractions; no collision
resistance is assumed. -/
theorem publicKey_canonical_decomposition (secretSeed publicSeed : Digest) (address : Address)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature)
    (hpk : SlhDsaSecurity.Fors.publicKeyFromSignature (m := Id) signature indices publicSeed address =
      Hashing.tweakable (m := Id) publicSeed (rootAddress address)
        (digestArrayBytes (canonicalRoots secretSeed publicSeed address))) :
    CompressionCollision (recoveredRoot signature indices publicSeed address)
        (canonicalRoots secretSeed publicSeed address) publicSeed address ∨
    ∀ i : Fin forsTrees,
      let nodes : Nat → Nat → Digest :=
        SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address
      let combine : Nat → Nat → Digest → Digest → Digest := fun height nodeIndex left right =>
        Hashing.tweakable (m := Id) publicSeed
          (SlhDsaSecurity.Fors.nodeAddress address height nodeIndex)
          (BinaryPath.pairBytes (left, right))
      let leaf : Digest := recoveredLeaf signature indices publicSeed address i
      (leaf = nodes 0 (leafIndex indices i) ∧ ∀ j, (signature i).authentication j =
        nodes j.val (Nat.xor (leafIndex indices i / 2 ^ j.val) 1)) ∨
      ∃ j < forsHeight,
        BinaryPath.Collision nodes combine (leafIndex indices i) leaf (siblings signature i) j := by
  rcases publicKey_eq_canonical_roots_or_collision secretSeed publicSeed address indices
      signature hpk with hroots | hcomp
  · refine Or.inr (fun i => ?_)
    exact root_eq_canonical_or_collision secretSeed publicSeed address indices signature i
      (congrFun hroots i)
  · exact Or.inl hcomp

/-- A collision at a FORS leaf compression: the forged secret and the honest secret are
distinct but hash to the same leaf under the same leaf address. -/
def LeafCollision (secretSeed publicSeed : Digest) (address : Address) (index : Nat)
    (forgedSecret : Digest) : Prop :=
  let honestSecret := SlhDsaSecurity.Fors.secret (m := Id) secretSeed publicSeed address index
  forgedSecret ≠ honestSecret ∧
    Hashing.tweakable (m := Id) publicSeed (SlhDsaSecurity.Fors.nodeAddress address 0 index)
        (bytesBE n forgedSecret) =
      Hashing.tweakable (m := Id) publicSeed (SlhDsaSecurity.Fors.nodeAddress address 0 index)
        (bytesBE n honestSecret)

/-- If a FORS tree's recovered leaf equals the canonical leaf, then either the revealed
secret equals the honest secret — so the selected FORS position was disclosed, the FORS
coverage event — or there is a concrete collision at that leaf's compression call. No
collision resistance is assumed. -/
theorem recoveredLeaf_canonical_secret_or_collision (secretSeed publicSeed : Digest)
    (address : Address) (indices : SlhDsaSecurity.Fors.Indices) (signature : ForsSignature)
    (i : Fin forsTrees)
    (hleaf : recoveredLeaf signature indices publicSeed address i =
      SlhDsaSecurity.Fors.node (m := Id) secretSeed publicSeed address 0 (leafIndex indices i)) :
    (signature i).secret =
        SlhDsaSecurity.Fors.secret (m := Id) secretSeed publicSeed address (leafIndex indices i) ∨
      LeafCollision secretSeed publicSeed address (leafIndex indices i) (signature i).secret := by
  by_cases hsecret : (signature i).secret =
      SlhDsaSecurity.Fors.secret (m := Id) secretSeed publicSeed address (leafIndex indices i)
  · exact Or.inl hsecret
  · exact Or.inr ⟨hsecret, hleaf⟩

end SlhDsaSecurity.Extraction.Fors
