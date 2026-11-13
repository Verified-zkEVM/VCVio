/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.HashInstance
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Congruence

/-!
# Hashed-leaf Merkle adapters

Construction 1 of ePrint 2025/055 hashes endpoint vectors at level zero and pairs left to right.
The pinned perfect-tree engine supplies the root and leaf-first authentication paths.
Fixed-length paths use functions on `Fin h`; list conversion is confined to the engine boundary.
-/

public section

namespace GXMSS

variable {PP T X H : Type} {h w v : ℕ}

namespace HashInstance

/-- The endpoint vector is hashed under the level-zero tree tweak, even at height zero. -/
@[expose] def leafHash (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (xs : Fin v → H) : H :=
  (HashInstance.thf P).eval pp (P.treeTweak (0, e)) (P.vectorInput xs)

/-- Left/right pair hashing at a finite tree address. -/
@[expose] def nodeHash (P : HashInstance PP T X H h w v) (pp : PP)
    (z : Fin (h + 1)) (t : Fin (2 ^ h)) (left right : H) : H :=
  (HashInstance.thf P).eval pp (P.treeTweak (z, t)) (P.pairInput (left, right))

/-- Natural-index extension of finite leaves. The default is used only outside the leaf domain. -/
private def leafExtension (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (t : ℕ) : H :=
  if ht : t < 2 ^ h then P.leafHash pp ⟨t, ht⟩ (xs ⟨t, ht⟩) else P.leafHash pp 0 (xs 0)

/-- Natural-index extension of the full finite tree rectangle. Outside the rectangle it returns
its left argument; legal computations are independent of those values. -/
private def nodeExtension (P : HashInstance PP T X H h w v) (pp : PP)
    (z t : ℕ) (left right : H) : H :=
  if hz : z < h + 1 then
    if ht : t < 2 ^ h then P.nodeHash pp ⟨z, hz⟩ ⟨t, ht⟩ left right else left
  else left

/-- Finite-to-natural leaf conversion agrees with the hashed endpoint vector. -/
@[simp] private theorem leafExtension_fin (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) :
    P.leafExtension pp xs e = P.leafHash pp e (xs e) := by
  simp [leafExtension]

/-- Finite-to-natural node conversion preserves the full rectangle and left/right order. -/
@[simp] private theorem nodeExtension_fin (P : HashInstance PP T X H h w v) (pp : PP)
    (z : Fin (h + 1)) (t : Fin (2 ^ h)) (left right : H) :
    P.nodeExtension pp z t left right = P.nodeHash pp z t left right := by
  simp [nodeExtension, z.isLt]

/-- The root constructed from hashed endpoint vectors. -/
def merkleRoot (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) : H :=
  PerfectMerkleTree.merkleRoot (P.leafExtension pp xs) (P.nodeExtension pp) h 0

/-- Canonical authentication path, ordered from the leaf level upward. -/
def authPath (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) : Fin h → H :=
  fun z => (PerfectMerkleTree.authPath (P.leafExtension pp xs)
    (P.nodeExtension pp) e h)[z.val]'(by simp)

/-- Converting the finite path to the engine representation preserves leaf-first order. -/
@[simp] private theorem ofFn_authPath (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) :
    List.ofFn (P.authPath pp xs e) =
      PerfectMerkleTree.authPath (P.leafExtension pp xs) (P.nodeExtension pp) e h := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [authPath]

/-- Recover a root from a hashed endpoint vector and one sibling per level, leaf first. -/
def recoverRoot (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (xs : Fin v → H) (auth : Fin h → H) : H :=
  PerfectMerkleTree.climb (P.nodeExtension pp) e (P.leafHash pp e xs) (List.ofFn auth)

/-- The honest path reconstructs the constructed root at natural index zero. -/
theorem recoverRoot_authPath (P : HashInstance PP T X H h w v) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h)) :
    P.recoverRoot pp e (xs e) (P.authPath pp xs e) = P.merkleRoot pp xs := by
  have he : (e : ℕ) / 2 ^ h = 0 := Nat.div_eq_of_lt e.isLt
  simpa [recoverRoot, merkleRoot, he] using
    PerfectMerkleTree.climb_authPath (P.leafExtension pp xs) (P.nodeExtension pp) e h

/-- Height zero still hashes the sole endpoint vector. -/
theorem merkleRoot_zero (P : HashInstance PP T X H 0 w v) (pp : PP)
    (xs : Fin (2 ^ 0) → Fin v → H) :
    P.merkleRoot pp xs = P.leafHash pp 0 (xs 0) := by
  simp [merkleRoot, leafExtension]

/-- At height zero the authentication path is empty. -/
theorem authPath_zero (P : HashInstance PP T X H 0 w v) (pp : PP)
    (xs : Fin (2 ^ 0) → Fin v → H) (e : Fin (2 ^ 0)) :
    P.authPath pp xs e = Fin.elim0 := by
  funext z
  exact Fin.elim0 z

end HashInstance

namespace HashInstance

/-- Finite hashed-leaf agreement supplies the private natural-index adapter agreement. -/
private theorem leafExtension_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H)
    (hl : ∀ e, P.leafHash pp e (xs e) = Q.leafHash qq e (ys e)) (t : ℕ) (ht : t < 2 ^ h) :
    P.leafExtension pp xs t = Q.leafExtension qq ys t := by
  simpa [leafExtension, ht] using hl ⟨t, ht⟩

/-- Reachable finite hash agreement supplies all natural-index engine obligations. -/
private theorem nodeExtension_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (hn : PerfectMerkleTree.NodeHashAgreement h (P.nodeHash pp) (Q.nodeHash qq))
    (z : ℕ) (hpos : 0 < z) (hz : z ≤ h) (t : ℕ) (ht : (t + 1) * 2 ^ z ≤ 2 ^ h)
    (l r : H) : P.nodeExtension pp z t l r = Q.nodeExtension qq z t l r := by
  obtain ⟨hz', ht'⟩ := PerfectMerkleTree.subtree_legal hz ht
  simpa [nodeExtension, hz', ht'] using hn ⟨z, hz'⟩ ⟨t, ht'⟩ ⟨hpos, hz, ht⟩ l r

/-- Root construction depends on the supplied hashed leaves and reachable pair hashes. -/
theorem merkleRoot_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H)
    (hl : ∀ e, P.leafHash pp e (xs e) = Q.leafHash qq e (ys e))
    (hn : PerfectMerkleTree.NodeHashAgreement h (P.nodeHash pp) (Q.nodeHash qq)) :
    P.merkleRoot pp xs = Q.merkleRoot qq ys :=
  PerfectMerkleTree.root_extension_independent _ _ _ _ h h 0 le_rfl (by simp)
    (leafExtension_congr P Q pp qq xs ys hl) (nodeExtension_congr P Q pp qq hn)

/-- Canonical finite paths depend on the supplied hashed leaves and reachable pair hashes. -/
theorem authPath_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (xs ys : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h))
    (hl : ∀ i, P.leafHash pp i (xs i) = Q.leafHash qq i (ys i))
    (hn : PerfectMerkleTree.NodeHashAgreement h (P.nodeHash pp) (Q.nodeHash qq)) :
    P.authPath pp xs e = Q.authPath qq ys e := by
  apply List.ofFn_injective
  rw [ofFn_authPath, ofFn_authPath]
  exact PerfectMerkleTree.authPath_extension_independent _ _ _ _ h e
    (leafExtension_congr P Q pp qq xs ys hl) (nodeExtension_congr P Q pp qq hn)

/-- Recovery depends only on its starting hashed leaf and reachable pair hashes. -/
theorem recoverRoot_congr (P Q : HashInstance PP T X H h w v) (pp qq : PP)
    (e : Fin (2 ^ h)) (xs ys : Fin v → H) (auth : Fin h → H)
    (hl : P.leafHash pp e xs = Q.leafHash qq e ys)
    (hn : PerfectMerkleTree.NodeHashAgreement h (P.nodeHash pp) (Q.nodeHash qq)) :
    P.recoverRoot pp e xs auth = Q.recoverRoot qq e ys auth := by
  simpa only [recoverRoot, hl] using
    PerfectMerkleTree.climb_extension_independent (P.nodeExtension pp) (Q.nodeExtension qq) h e
      (P.leafHash pp e xs) auth (nodeExtension_congr P Q pp qq hn)

/-- A height-zero path performs only its starting vector hash, for every endpoint vector. -/
theorem recoverRoot_zero (P : HashInstance PP T X H 0 w v) (pp : PP)
    (e : Fin (2 ^ 0)) (xs : Fin v → H) (auth : Fin 0 → H) :
    P.recoverRoot pp e xs auth = P.leafHash pp e xs := by
  have ha : auth = Fin.elim0 := by
    funext z
    exact Fin.elim0 z
  rw [ha]
  rfl

end HashInstance

end GXMSS
