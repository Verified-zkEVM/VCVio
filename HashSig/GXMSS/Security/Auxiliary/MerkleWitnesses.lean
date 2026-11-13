/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Merkle
public import HashSig.GXMSS.Security.Auxiliary.HashWitnesses
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Uniqueness
import all HashSig.GXMSS.Merkle

/-!
# Computable raw Merkle opening collisions
-/

public section

namespace GXMSS.HashInstance

open GXMSS.Security BinaryTree AddressedMerkleTree

variable {PP T X H M R : Type} {h w v : ℕ}

private def openingProof (e : Fin (2 ^ h)) (p : Fin h → H) :
    List.Vector H (SkeletonLeafIndex.ofNat h e).depth :=
  ⟨(List.ofFn p).reverse, by simp⟩

private theorem openingProof_injective (e : Fin (2 ^ h)) :
    Function.Injective (openingProof (H := H) e) := by
  intro p q hpq
  apply List.ofFn_injective
  apply List.reverse_injective
  exact congrArg Subtype.val hpq

private def engineAddress (a : SkeletonInternalIndex (Skeleton.perfect h)) :
    Fin (h + 1) × Fin (2 ^ h) :=
  let hb := PerfectMerkleTree.internalAddress_reachable h h 0 le_rfl (by simp) a
  let bounds := hb.2
  let hr := PerfectMerkleTree.subtree_legal bounds.1 bounds.2
  (⟨(a.natAddr 0).height, hr.1⟩, ⟨(a.natAddr 0).index, hr.2⟩)

private def engineHash (P : HashInstance PP T X H h w v) (pp : PP)
    (a : SkeletonInternalIndex (Skeleton.perfect h)) (l r : H) : H :=
  P.nodeHash pp (engineAddress a).1 (engineAddress a).2 l r

private theorem engineHash_eq (P : HashInstance PP T X H h w v) (pp : PP) :
    engineHash P pp = PerfectMerkleTree.nodeHashAt (P.nodeExtension pp) h 0 := by
  funext a l r
  have hb := PerfectMerkleTree.internalAddress_reachable h h 0 le_rfl (by simp) a
  have bounds := hb.2
  have hr := PerfectMerkleTree.subtree_legal bounds.1 bounds.2
  simp [engineHash, engineAddress, PerfectMerkleTree.nodeHashAt, nodeExtension,
    bounds.1, hr.2]

private theorem recoverRoot_engine (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (xs : Fin v → H) (p : Fin h → H) :
    P.recoverRoot pp e xs p = getPutativeRootAddressedWithHash (engineHash P pp)
      (SkeletonLeafIndex.ofNat h e) (P.leafHash pp e xs) (openingProof e p) := by
  rw [recoverRoot, PerfectMerkleTree.climb_eq _ _ _ _ (z := h) (by simp),
    Nat.div_eq_of_lt e.isLt, ← engineHash_eq]
  rfl

private def liftNodeCollision (P : HashInstance PP T X H h w v)
    (c : SkeletonInternalIndex (Skeleton.perfect h) × H × H × H × H) : HashCollision T X :=
  let values := c.2
  let remaining := values.2
  let forged := remaining.2
  ⟨P.treeTweak (engineAddress c.1), P.pairInput (values.1, remaining.1),
    P.pairInput (forged.1, forged.2)⟩

private theorem liftNodeCollision_sound (P : HashInstance PP T X H h w v) (pp : PP)
    (c : SkeletonInternalIndex (Skeleton.perfect h) × H × H × H × H)
    (hc : AddressedCollision (engineHash P pp) c) :
    (liftNodeCollision P c).Sound P.thf pp :=
  collision_embedding P.thf pp _ P.pairInput hc.1 hc.2

/-- Find a common-domain collision from two raw openings, with the first input designated honest.
The finite addressed kernel performs the internal search; no hash-domain enumeration is needed. -/
def findMerkleCollision [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (xs ys : Fin v → H) (p q : Fin h → H) :
    Option (HashCollision T X) :=
  if xs ≠ ys ∧ P.leafHash pp e xs = P.leafHash pp e ys then
    some ⟨P.treeTweak (0, e), P.vectorInput xs, P.vectorInput ys⟩
  else
    (findCollisionAddressed (engineHash P pp) (SkeletonLeafIndex.ofNat h e)
      (openingProof e p) (openingProof e q) (P.leafHash pp e xs) (P.leafHash pp e ys)).map
      (liftNodeCollision P)

/-- Every returned witness is a collision under one common THF seed and tweak. -/
theorem findMerkleCollision_sound [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (xs ys : Fin v → H) (p q : Fin h → H)
    {c : HashCollision T X} (hc : P.findMerkleCollision pp e xs ys p q = some c) :
    c.Sound P.thf pp := by
  unfold findMerkleCollision at hc
  split at hc
  next hleaf =>
    cases Option.some.inj hc
    exact collision_embedding P.thf pp _ P.vectorInput hleaf.1 hleaf.2
  next =>
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact liftNodeCollision_sound P pp d
      (findCollisionAddressed_sound _ _ _ _ _ _ d hd)

/-- Different raw leaf/path openings reaching the same root always return a collision. -/
theorem findMerkleCollision_isSome [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (xs ys : Fin v → H) (p q : Fin h → H)
    (hne : (xs, p) ≠ (ys, q))
    (hroot : P.recoverRoot pp e xs p = P.recoverRoot pp e ys q) :
    (P.findMerkleCollision pp e xs ys p q).isSome := by
  unfold findMerkleCollision
  split
  · rfl
  next hleaf =>
    simp only [Option.isSome_map]
    apply findCollisionAddressed_isSome_of_opening_ne
    · simpa only [recoverRoot_engine] using hroot
    · intro hpair
      have hx := congrArg Prod.fst hpair
      have hp := openingProof_injective e (congrArg Prod.snd hpair)
      apply hne
      apply Prod.ext _ hp
      by_contra hxy
      exact hleaf ⟨hxy, hx⟩

/-- Honest-tree specialization retains the complete opening difference, including path changes. -/
theorem findMerkleCollision_isSome_of_honest [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP)
    (leaves : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h))
    (ys : Fin v → H) (q : Fin h → H)
    (hne : (leaves e, P.authPath pp leaves e) ≠ (ys, q))
    (hroot : P.recoverRoot pp e ys q = P.merkleRoot pp leaves) :
    (P.findMerkleCollision pp e (leaves e) ys (P.authPath pp leaves e) q).isSome :=
  P.findMerkleCollision_isSome pp e _ _ _ _ hne
    ((P.recoverRoot_authPath pp leaves e).trans hroot.symm)

/-- The ordered hash inputs performed by a complete opening, including its raw vector hash. -/
def merkleOpeningQueries (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (xs : Fin v → H) (p : Fin h → H) : List (T × X) :=
  (P.treeTweak (0, e), P.vectorInput xs) ::
    (openingQueries (fun a => P.treeTweak (engineAddress a))
      (fun t l r => P.thf.eval pp t (P.pairInput (l, r)))
      (SkeletonLeafIndex.ofNat h e) (P.leafHash pp e xs) (openingProof e p)).map
      (fun query => (query.address, P.pairInput query.input))

/-- Return-based orientation: each input comes from the corresponding compared opening.
There is no leaf-difference premise, so path-only collisions retain honest input provenance. -/
theorem findMerkleCollision_mem_queries [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP) (e : Fin (2 ^ h))
    (xs ys : Fin v → H) (p q : Fin h → H) {c : HashCollision T X}
    (hc : P.findMerkleCollision pp e xs ys p q = some c) :
    (c.tweak, c.first) ∈ P.merkleOpeningQueries pp e xs p ∧
      (c.tweak, c.second) ∈ P.merkleOpeningQueries pp e ys q := by
  unfold findMerkleCollision at hc
  split at hc
  · cases Option.some.inj hc
    simp [merkleOpeningQueries]
  · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
    obtain ⟨hx, hy⟩ := findCollisionAddressed_mem_openingQueries
      (fun a => P.treeTweak (engineAddress a))
      (fun t l r => P.thf.eval pp t (P.pairInput (l, r)))
      (SkeletonLeafIndex.ofNat h e) (openingProof e p) (openingProof e q)
      (P.leafHash pp e xs) (P.leafHash pp e ys) d hd
    constructor
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hx, rfl⟩)
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hy, rfl⟩)

end GXMSS.HashInstance
