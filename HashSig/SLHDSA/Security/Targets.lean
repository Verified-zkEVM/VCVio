/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Scheme
public import HashSig.SLHDSA.Security.TargetProfile

/-!
# Concrete `d = 1` SLH-DSA target enumerations

The quantitative target profile is useful only if each number is tied to the actual ADRS values
queried by the construction.  This module enumerates those reachable target coordinates and maps
them through a primitive bundle's concrete address encoding.  The length theorems recover the
caps in `Params.d1TargetProfile`.

These theorems count issued targets.  They deliberately do not claim that `adrsToKey` is globally
injective: a concrete instantiation must prove `Nodup`/cross-disjointness on these reachable lists.
-/

@[expose] public section

namespace SLHDSA

/-- Internal nodes of a perfect binary tree, listed bottom-up as `(height, index)` pairs. -/
def perfectInternalCoords : ℕ → List (ℕ × ℕ)
  | 0 => []
  | h + 1 =>
      (List.range (2 ^ h)).map (fun i => (1, i)) ++
        (perfectInternalCoords h).map (fun zi => (zi.1 + 1, zi.2))

@[simp] theorem perfectInternalCoords_length (h : ℕ) :
    (perfectInternalCoords h).length = 2 ^ h - 1 := by
  induction h with
  | zero => simp [perfectInternalCoords]
  | succ h ih =>
      simp [perfectInternalCoords, ih, pow_succ]
      omega

namespace Params

/-- Every FORS secret-leaf target address, before concrete address encoding. -/
def d1ForsLeafAddresses (p : Params) : List Adrs :=
  (List.range p.d1LeafCount).flatMap fun idxLeaf =>
    (List.range p.k).flatMap fun tree =>
      (List.range p.t).map fun leaf =>
        forsNodeAdrs (forsAdrsOf idxLeaf) 0 (tree * p.t + leaf)

/-- Every FORS internal-node target address, before concrete address encoding. -/
def d1ForsTreeAddresses (p : Params) : List Adrs :=
  (List.range p.d1LeafCount).flatMap fun idxLeaf =>
    (List.range p.k).flatMap fun tree =>
      (perfectInternalCoords p.a).map fun zi =>
        forsNodeAdrs (forsAdrsOf idxLeaf) zi.1
          (tree * 2 ^ (p.a - zi.1) + zi.2)

/-- Every FORS-root-compression target address. -/
def d1ForsRootsAddresses (p : Params) : List Adrs :=
  (List.range p.d1LeafCount).map fun idxLeaf => forsPkAdrs (forsAdrsOf idxLeaf)

/-- The WOTS arity-one target addresses used by UD-C and PRE-C. -/
def d1WotsChainAddresses (p : Params) : List Adrs :=
  (List.range p.d1LeafCount).flatMap fun idxLeaf =>
    (List.range p.len).map fun chain => wotsChainAdrs (wotsLeafAdrs Adrs.zero idxLeaf) chain

/-- The WOTS arity-one target addresses used by TCR-C, including every chain position. -/
def d1WotsTcrAddresses (p : Params) : List Adrs :=
  (List.range p.d1LeafCount).flatMap fun idxLeaf =>
    (List.range p.len).flatMap fun chain =>
      (List.range p.w).map fun step =>
        (wotsChainAdrs (wotsLeafAdrs Adrs.zero idxLeaf) chain).setHashAddress step

/-- Every WOTS public-key-compression target address. -/
def d1WotsPkAddresses (p : Params) : List Adrs :=
  (List.range p.d1LeafCount).map fun idxLeaf => wotsPkAdrs (wotsLeafAdrs Adrs.zero idxLeaf)

/-- Every internal node of the single XMSS tree. -/
def d1XmssTreeAddresses (p : Params) : List Adrs :=
  (perfectInternalCoords p.hp).map fun zi => xmssNodeAdrs Adrs.zero zi.1 zi.2

@[simp] theorem d1ForsLeafAddresses_length (p : Params) :
    p.d1ForsLeafAddresses.length = p.d1TargetProfile.forsLeaf := by
  simp [d1ForsLeafAddresses, d1TargetProfile, d1LeafCount, Nat.mul_assoc]

@[simp] theorem d1ForsTreeAddresses_length (p : Params) :
    p.d1ForsTreeAddresses.length = p.d1TargetProfile.forsTree := by
  simp [d1ForsTreeAddresses, d1TargetProfile, d1LeafCount, t, Nat.mul_assoc]

@[simp] theorem d1ForsRootsAddresses_length (p : Params) :
    p.d1ForsRootsAddresses.length = p.d1TargetProfile.forsRoots := by
  simp [d1ForsRootsAddresses, d1TargetProfile, d1LeafCount]

@[simp] theorem d1WotsChainAddresses_length (p : Params) :
    p.d1WotsChainAddresses.length = p.d1TargetProfile.wotsUd := by
  simp [d1WotsChainAddresses, d1TargetProfile, d1LeafCount, Nat.mul_assoc]

@[simp] theorem d1WotsChainAddresses_length_pre (p : Params) :
    p.d1WotsChainAddresses.length = p.d1TargetProfile.wotsPre := by
  simp [d1WotsChainAddresses, d1TargetProfile, d1LeafCount, Nat.mul_assoc]

@[simp] theorem d1WotsTcrAddresses_length (p : Params) :
    p.d1WotsTcrAddresses.length = p.d1TargetProfile.wotsTcr := by
  simp [d1WotsTcrAddresses, d1TargetProfile, d1LeafCount, Nat.mul_assoc]

@[simp] theorem d1WotsPkAddresses_length (p : Params) :
    p.d1WotsPkAddresses.length = p.d1TargetProfile.wotsPk := by
  simp [d1WotsPkAddresses, d1TargetProfile, d1LeafCount]

@[simp] theorem d1XmssTreeAddresses_length (p : Params) :
    p.d1XmssTreeAddresses.length = p.d1TargetProfile.xmssTree := by
  simp [d1XmssTreeAddresses, d1TargetProfile, d1LeafCount]

end Params

namespace Primitives

variable {p : Params}

/-- Encode a reachable address list with the primitive bundle's actual tweak function. -/
def encodeTargets (prims : Primitives p) (addresses : List Adrs) : List prims.AdrsKey :=
  addresses.map prims.adrsToKey

def d1ForsLeafTweaks (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1ForsLeafAddresses

def d1ForsTreeTweaks (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1ForsTreeAddresses

def d1ForsRootsTweaks (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1ForsRootsAddresses

def d1WotsChainTweaks (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1WotsChainAddresses

def d1WotsTcrTweaks (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1WotsTcrAddresses

def d1WotsPkTweaks (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1WotsPkAddresses

def d1XmssTreeTweaks (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1XmssTreeAddresses

@[simp] theorem d1ForsLeafTweaks_length (prims : Primitives p) :
    prims.d1ForsLeafTweaks.length = p.d1TargetProfile.forsLeaf := by
  simp [d1ForsLeafTweaks, encodeTargets]

@[simp] theorem d1ForsTreeTweaks_length (prims : Primitives p) :
    prims.d1ForsTreeTweaks.length = p.d1TargetProfile.forsTree := by
  simp [d1ForsTreeTweaks, encodeTargets]

@[simp] theorem d1WotsTcrTweaks_length (prims : Primitives p) :
    prims.d1WotsTcrTweaks.length = p.d1TargetProfile.wotsTcr := by
  simp [d1WotsTcrTweaks, encodeTargets]

@[simp] theorem d1ForsRootsTweaks_length (prims : Primitives p) :
    prims.d1ForsRootsTweaks.length = p.d1TargetProfile.forsRoots := by
  simp [d1ForsRootsTweaks, encodeTargets]

@[simp] theorem d1WotsChainTweaks_length (prims : Primitives p) :
    prims.d1WotsChainTweaks.length = p.d1TargetProfile.wotsUd := by
  simp [d1WotsChainTweaks, encodeTargets]

@[simp] theorem d1WotsChainTweaks_length_pre (prims : Primitives p) :
    prims.d1WotsChainTweaks.length = p.d1TargetProfile.wotsPre := by
  simp [d1WotsChainTweaks, encodeTargets]

@[simp] theorem d1WotsPkTweaks_length (prims : Primitives p) :
    prims.d1WotsPkTweaks.length = p.d1TargetProfile.wotsPk := by
  simp [d1WotsPkTweaks, encodeTargets]

@[simp] theorem d1XmssTreeTweaks_length (prims : Primitives p) :
    prims.d1XmssTreeTweaks.length = p.d1TargetProfile.xmssTree := by
  simp [d1XmssTreeTweaks, encodeTargets]

end Primitives

end SLHDSA
