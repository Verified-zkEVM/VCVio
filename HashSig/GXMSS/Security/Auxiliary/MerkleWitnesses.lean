/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.HashWitnesses
public import HashSig.GXMSS.Merkle
import all HashSig.GXMSS.Merkle
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Uniqueness

/-!
# Computable collisions from complete Merkle openings

Raw endpoint vectors are compared before their leaf digests enter the pinned addressed
collision kernel. This preserves leaf compression and path-only disagreements, including
height zero. The two common-domain inputs retain the order of the compared openings.
-/

public section

namespace GXMSS.HashInstance

open Security BinaryTree AddressedMerkleTree

variable {PP T X H : Type} {h w v : ℕ}

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
  let hb := Merkle.internalAddress_legal h h 0 le_rfl (by simp) a
  let bounds := hb.2
  let hr := Merkle.subtree_legal bounds.1 bounds.2
  (⟨(a.natAddr 0).height, hr.1⟩, ⟨(a.natAddr 0).index, hr.2⟩)

private def engineHash (P : HashInstance PP T X H h w v) (pp : PP)
    (a : SkeletonInternalIndex (Skeleton.perfect h)) (l r : H) : H :=
  P.nodeHash pp (engineAddress a).1 (engineAddress a).2 l r

private theorem engineHash_eq (P : HashInstance PP T X H h w v) (pp : PP) :
    engineHash P pp = PerfectMerkleTree.nodeHashAt (P.nodeExtension pp) h 0 := by
  funext a l r
  have hb := Merkle.internalAddress_legal h h 0 le_rfl (by simp) a
  have bounds := hb.2
  have hr := Merkle.subtree_legal bounds.1 bounds.2
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

/-- A returned witness identifies either the raw vector collision or a reachable positive
ancestor and the two ordered child pairs. The ancestor coordinate is the paper quotient. -/
theorem findMerkleCollision_shape [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP) (e : Fin (2 ^ h))
    (xs ys : Fin v → H) (p q : Fin h → H) {c : HashCollision T X}
    (hc : P.findMerkleCollision pp e xs ys p q = some c) :
    (xs ≠ ys ∧ c = ⟨P.treeTweak (0, e), P.vectorInput xs, P.vectorInput ys⟩) ∨
      ∃ (z : Fin h) (u v : H × H),
        c = ⟨P.treeTweak (Merkle.parentAddress e z), P.pairInput u, P.pairInput v⟩ ∧
        u ≠ v := by
  unfold findMerkleCollision at hc
  split at hc
  next hleaf => exact Or.inl ⟨hleaf.1, (Option.some.inj hc).symm⟩
  next =>
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
    have hanc := findCollisionAddressed_isAncestorOf _ _ _ _ _ _ d hd
    have hidx := PerfectMerkleTree.natAddr_index_of_isAncestorOf_ofNat hanc
    have he : e.val / 2 ^ h = 0 := Nat.div_eq_of_lt e.isLt
    rw [he] at hidx
    let address := d.1
    let nodeAddress := address.natAddr 0
    obtain ⟨hpos, hle⟩ := address.natAddr_height_pos_le 0
    have hposNode : 0 < nodeAddress.height := by simpa [nodeAddress] using hpos
    have hleNode : nodeAddress.height ≤ h := by simpa [nodeAddress] using hle
    let z : Fin h := ⟨nodeAddress.height - 1, by omega⟩
    have hz : z.val + 1 = nodeAddress.height := by
      dsimp [z]
      omega
    have ha : engineAddress address = Merkle.parentAddress e z := by
      apply Prod.ext
      · apply Fin.ext
        exact hz.symm
      · apply Fin.ext
        change nodeAddress.index = e.val / 2 ^ (z.val + 1)
        rw [hz]
        exact hidx
    let values := d.2
    let remaining := values.2
    let forged := remaining.2
    refine Or.inr ⟨z, (values.1, remaining.1), (forged.1, forged.2), ?_, ?_⟩
    · simp [liftNodeCollision, address, ha, values, remaining, forged]
    · exact (findCollisionAddressed_sound _ _ _ _ _ _ d hd).1

/-- Height zero permits only the leaf-vector collision alternative. -/
theorem findMerkleCollision_zero [DecidableEq H]
    (P : HashInstance PP T X H 0 w v) (pp : PP) (e : Fin (2 ^ 0))
    (xs ys : Fin v → H) (p q : Fin 0 → H) {c : HashCollision T X}
    (hc : P.findMerkleCollision pp e xs ys p q = some c) :
    xs ≠ ys ∧ c = ⟨P.treeTweak (0, e), P.vectorInput xs, P.vectorInput ys⟩ := by
  rcases P.findMerkleCollision_shape pp e xs ys p q hc with hleaf | ⟨z, _⟩
  · exact hleaf
  · exact Fin.elim0 z

private theorem finder_honest_pair {s : Skeleton} [DecidableEq H]
    (nh : SkeletonInternalIndex s → H → H → H) (ld : LeafData H s)
    (idx : SkeletonLeafIndex s) (y : H) (q : List.Vector H idx.depth)
    (d : SkeletonInternalIndex s × H × H × H × H)
    (hd : findCollisionAddressed nh idx
      (InductiveMerkleTree.generateProof (buildMerkleTreeAddressedWithHash ld nh) idx)
      q (ld.get idx) y = some d) :
    let values := d.2
    let remaining := values.2
    (values.1, remaining.1) = childPairAt (buildMerkleTreeAddressedWithHash ld nh) d.1 := by
  induction idx with
  | ofLeaf => simp [findCollisionAddressed] at hd
  | ofLeft idx ih =>
    cases ld with
    | internal dl dr =>
      have hsub := addressed_functional_completeness idx dl (fun a => nh (.ofLeft a))
      rw [findCollisionAddressed] at hd
      split at hd
      · obtain ⟨d', hd', heq⟩ := Option.map_eq_some_iff.mp hd
        cases heq
        exact ih (fun a => nh (.ofLeft a)) dl q.tail d' hd'
      · split at hd
        · cases Option.some.inj hd
          simpa [buildMerkleTreeAddressedWithHash, populateUpAddressed,
            InductiveMerkleTree.generateProof, childPairAt] using
              congrArg (fun x => (x, (populateUpAddressed
                (fun a => nh (.ofRight a)) dr).getRootValue)) hsub
        · simp at hd
  | ofRight idx ih =>
    cases ld with
    | internal dl dr =>
      have hsub := addressed_functional_completeness idx dr (fun a => nh (.ofRight a))
      rw [findCollisionAddressed] at hd
      split at hd
      · obtain ⟨d', hd', heq⟩ := Option.map_eq_some_iff.mp hd
        cases heq
        exact ih (fun a => nh (.ofRight a)) dr q.tail d' hd'
      · split at hd
        · cases Option.some.inj hd
          simpa [buildMerkleTreeAddressedWithHash, populateUpAddressed,
            InductiveMerkleTree.generateProof, childPairAt] using
              congrArg (fun x => ((populateUpAddressed
                (fun a => nh (.ofLeft a)) dl).getRootValue, x)) hsub
        · simp at hd

/-- The generated tree's ordered child roots at a finite parent on the opened path. -/
def honestMerkleChildren (P : HashInstance PP T X H h w v) (pp : PP)
    (leaves : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) (z : Fin h) : H × H :=
  PerfectMerkleTree.honestChildren (P.leafExtension pp leaves) (P.nodeExtension pp)
    (z.val + 1) (e.val / 2 ^ (z.val + 1))

private theorem openingProof_honest (P : HashInstance PP T X H h w v) (pp : PP)
    (leaves : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) :
    openingProof e (P.authPath pp leaves e) =
      InductiveMerkleTree.generateProof
        (PerfectMerkleTree.tree (P.leafExtension pp leaves) (P.nodeExtension pp) h 0)
        (SkeletonLeafIndex.ofNat h e) := by
  apply Subtype.ext
  simp [openingProof, ofFn_authPath, PerfectMerkleTree.authPath, Nat.div_eq_of_lt e.isLt]

private theorem mem_openingQueries_honestTree {Address : Type} {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (nodeHash : Address → H → H → H) (ld : LeafData H s)
    (idx : SkeletonLeafIndex s) (query : NodeQuery Address H)
    (hquery : query ∈ openingQueries addressKey nodeHash idx (ld.get idx)
      (InductiveMerkleTree.generateProof (buildMerkleTreeAddressedWithHash ld
        (fun a l r => nodeHash (addressKey a) l r)) idx)) :
    ∃ a : SkeletonInternalIndex s, a.IsAncestorOf idx ∧
      query.address = addressKey a ∧
      query.input = childPairAt
        (buildMerkleTreeAddressedWithHash ld (fun a l r => nodeHash (addressKey a) l r)) a := by
  induction idx with
  | ofLeaf => simp [openingQueries] at hquery
  | ofLeft idx ih =>
      cases ld with
      | internal left right =>
          let leftTree := buildMerkleTreeAddressedWithHash left
            (fun a l r => nodeHash (addressKey (.ofLeft a)) l r)
          let rightTree := buildMerkleTreeAddressedWithHash right
            (fun a l r => nodeHash (addressKey (.ofRight a)) l r)
          have hsub := addressed_functional_completeness idx left
            (fun a l r => nodeHash (addressKey (.ofLeft a)) l r)
          change query ∈
            ((⟨addressKey .ofInternal, (getPutativeRootAddressedWithHash
                (fun a => nodeHash (addressKey (.ofLeft a))) idx (left.get idx)
                (InductiveMerkleTree.generateProof leftTree idx), rightTree.getRootValue)⟩ :
              NodeQuery Address H) ::
              openingQueries (fun a => addressKey (.ofLeft a)) nodeHash idx (left.get idx)
                (InductiveMerkleTree.generateProof leftTree idx)) at hquery
          rw [hsub] at hquery
          simp only [List.mem_cons] at hquery
          rcases hquery with hquery | hquery
          · subst query
            exact ⟨.ofInternal, trivial, rfl, rfl⟩
          · obtain ⟨a, hancestor, haddress, hinput⟩ :=
              ih (ld := left) (addressKey := fun a => addressKey (.ofLeft a)) hquery
            exact ⟨.ofLeft a, hancestor, haddress, hinput⟩
  | ofRight idx ih =>
      cases ld with
      | internal left right =>
          let leftTree := buildMerkleTreeAddressedWithHash left
            (fun a l r => nodeHash (addressKey (.ofLeft a)) l r)
          let rightTree := buildMerkleTreeAddressedWithHash right
            (fun a l r => nodeHash (addressKey (.ofRight a)) l r)
          have hsub := addressed_functional_completeness idx right
            (fun a l r => nodeHash (addressKey (.ofRight a)) l r)
          change query ∈
            ((⟨addressKey .ofInternal, (leftTree.getRootValue, getPutativeRootAddressedWithHash
                (fun a => nodeHash (addressKey (.ofRight a))) idx (right.get idx)
                (InductiveMerkleTree.generateProof rightTree idx))⟩ : NodeQuery Address H) ::
              openingQueries (fun a => addressKey (.ofRight a)) nodeHash idx (right.get idx)
                (InductiveMerkleTree.generateProof rightTree idx)) at hquery
          rw [hsub] at hquery
          simp only [List.mem_cons] at hquery
          rcases hquery with hquery | hquery
          · subst query
            exact ⟨.ofInternal, trivial, rfl, rfl⟩
          · obtain ⟨a, hancestor, haddress, hinput⟩ :=
              ih (ld := right) (addressKey := fun a => addressKey (.ofRight a)) hquery
            exact ⟨.ofRight a, hancestor, haddress, hinput⟩

/-- Every query in an honest opening is either its exact raw leaf-vector target or the exact
ordered child pair stored at one of the opened leaf's honest ancestors. -/
theorem mem_merkleOpeningQueries_honest_shape
    (P : HashInstance PP T X H h w v) (pp : PP)
    (leaves : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) (target : T × X)
    (hmem : target ∈
      P.merkleOpeningQueries pp e (leaves e) (P.authPath pp leaves e)) :
    target = (P.treeTweak (0, e), P.vectorInput (leaves e)) ∨
      ∃ z : Fin h, target = (P.treeTweak (Merkle.parentAddress e z),
        P.pairInput (P.honestMerkleChildren pp leaves e z)) := by
  simp only [merkleOpeningQueries, List.mem_cons, List.mem_map] at hmem
  rcases hmem with hleaf | ⟨query, hquery, rfl⟩
  · exact Or.inl hleaf
  · let addressKey := fun a : SkeletonInternalIndex (Skeleton.perfect h) =>
      P.treeTweak (engineAddress a)
    let nodeHash := fun t l r => P.thf.eval pp t (P.pairInput (l, r))
    let ld := PerfectMerkleTree.leafData (P.leafExtension pp leaves) h 0
    let idx := SkeletonLeafIndex.ofNat h e
    have hleafValue : ld.get idx = P.leafHash pp e (leaves e) := by
      simpa [ld, idx, Nat.div_eq_of_lt e.isLt] using
        PerfectMerkleTree.leafData_get_ofNat (P.leafExtension pp leaves) h e
    have hhash : (fun a l r => nodeHash (addressKey a) l r) = engineHash P pp := by
      rfl
    have htree : buildMerkleTreeAddressedWithHash ld
        (fun a l r => nodeHash (addressKey a) l r) =
        PerfectMerkleTree.tree (P.leafExtension pp leaves) (P.nodeExtension pp) h 0 := by
      rw [hhash, engineHash_eq]
      rfl
    rw [openingProof_honest] at hquery
    change query ∈ openingQueries addressKey nodeHash idx (P.leafHash pp e (leaves e))
      (InductiveMerkleTree.generateProof
        (PerfectMerkleTree.tree (P.leafExtension pp leaves) (P.nodeExtension pp) h 0) idx)
      at hquery
    rw [← hleafValue, ← htree] at hquery
    obtain ⟨a, hancestor, haddress, hinput⟩ :=
      mem_openingQueries_honestTree addressKey nodeHash ld idx query hquery
    have hidx := PerfectMerkleTree.natAddr_index_of_isAncestorOf_ofNat hancestor
    have he : e.val / 2 ^ h = 0 := Nat.div_eq_of_lt e.isLt
    rw [he] at hidx
    let nodeAddress := a.natAddr 0
    obtain ⟨hpos, hle⟩ := a.natAddr_height_pos_le 0
    have hposNode : 0 < nodeAddress.height := by simpa [nodeAddress] using hpos
    have hleNode : nodeAddress.height ≤ h := by simpa [nodeAddress] using hle
    let z : Fin h := ⟨nodeAddress.height - 1, by omega⟩
    have hz : z.val + 1 = nodeAddress.height := by
      dsimp [z]
      omega
    have ha : engineAddress a = Merkle.parentAddress e z := by
      apply Prod.ext
      · apply Fin.ext
        exact hz.symm
      · apply Fin.ext
        change nodeAddress.index = e.val / 2 ^ (z.val + 1)
        rw [hz]
        exact hidx
    rw [htree, PerfectMerkleTree.childPairAt_tree] at hinput
    have hheight : (a.natAddr 0).height - 1 = z.val := by
      rw [← hz]
      omega
    have hnodeIndex : (a.natAddr 0).index = e.val / 2 ^ (z.val + 1) := by
      rw [hz]
      exact hidx
    refine Or.inr ⟨z, ?_⟩
    simp only [addressKey] at haddress ⊢
    rw [haddress, ha, hinput]
    simp [honestMerkleChildren, PerfectMerkleTree.honestChildren, hheight, hnodeIndex]

/-- Every returned honest-tree collision has the original raw vector or the actual ordered
child roots of the generated tree as its first input. This includes path-only differences. -/
theorem findMerkleCollision_honest_shape [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP)
    (leaves : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h))
    (ys : Fin v → H) (q : Fin h → H) {c : HashCollision T X}
    (hc : P.findMerkleCollision pp e (leaves e) ys (P.authPath pp leaves e) q = some c) :
    (leaves e ≠ ys ∧
      c = ⟨P.treeTweak (0, e), P.vectorInput (leaves e), P.vectorInput ys⟩) ∨
      ∃ (z : Fin h) (u : H × H),
        c = ⟨P.treeTweak (Merkle.parentAddress e z),
          P.pairInput (P.honestMerkleChildren pp leaves e z), P.pairInput u⟩ ∧
        P.honestMerkleChildren pp leaves e z ≠ u := by
  unfold findMerkleCollision at hc
  split at hc
  next hleaf => exact Or.inl ⟨hleaf.1, (Option.some.inj hc).symm⟩
  next =>
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hc
    have hanc := findCollisionAddressed_isAncestorOf _ _ _ _ _ _ d hd
    have hidx := PerfectMerkleTree.natAddr_index_of_isAncestorOf_ofNat hanc
    have he : e.val / 2 ^ h = 0 := Nat.div_eq_of_lt e.isLt
    rw [he] at hidx
    let address := d.1
    let nodeAddress := address.natAddr 0
    obtain ⟨hpos, hle⟩ := address.natAddr_height_pos_le 0
    have hposNode : 0 < nodeAddress.height := by simpa [nodeAddress] using hpos
    have hleNode : nodeAddress.height ≤ h := by simpa [nodeAddress] using hle
    let z : Fin h := ⟨nodeAddress.height - 1, by omega⟩
    have hz : z.val + 1 = nodeAddress.height := by
      dsimp [z]
      omega
    have ha : engineAddress address = Merkle.parentAddress e z := by
      apply Prod.ext
      · apply Fin.ext
        exact hz.symm
      · apply Fin.ext
        change nodeAddress.index = e.val / 2 ^ (z.val + 1)
        rw [hz]
        exact hidx
    have hne := (findCollisionAddressed_sound _ _ _ _ _ _ d hd).1
    have hleaf : (PerfectMerkleTree.leafData (P.leafExtension pp leaves) h 0).get
        (SkeletonLeafIndex.ofNat h e) = P.leafHash pp e (leaves e) := by
      simpa [he] using PerfectMerkleTree.leafData_get_ofNat (P.leafExtension pp leaves) h e
    rw [openingProof_honest, engineHash_eq, ← hleaf] at hd
    have ho := finder_honest_pair _ _ _ _ _ d hd
    rw [← PerfectMerkleTree.tree, PerfectMerkleTree.childPairAt_tree] at ho
    let values := d.2
    let remaining := values.2
    let forged := remaining.2
    have hc : (values.1, remaining.1) = P.honestMerkleChildren pp leaves e z := by
      simpa [nodeAddress, address, values, remaining, honestMerkleChildren,
        PerfectMerkleTree.honestChildren, hz, ← hidx] using ho
    refine Or.inr ⟨z, (forged.1, forged.2), ?_, ?_⟩
    · simp [liftNodeCollision, address, ha, hc, values, remaining, forged]
    · rwa [← hc]

end GXMSS.HashInstance
