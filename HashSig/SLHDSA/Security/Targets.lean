/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Scheme
public import HashSig.SLHDSA.Security.TargetProfile

/-!
# Concrete `d = 1` SLH-DSA target coordinates

The quantitative target profile is useful only if each number is tied to the actual ADRS values
queried by the construction.  This module enumerates the message-independent FORS/XMSS targets
and maps them through a primitive bundle's concrete address encoding.  WOTS target selection is
message/hybrid dependent: its PRE transcript constructor is therefore parameterized by the honest
message at each leaf, while its TCR declaration is only the reachable address space from which a
reduction selects targets.  The length theorems recover, or upper-bound by, the caps in
`Params.d1TargetProfile`.

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

/-- The actual WOTS PRE-C target transcript for one honest WOTS message at each XMSS leaf.  Chain
`i` contributes a target at hash address `digit - 1` exactly when its honest digit is nonzero. -/
def d1WotsPreAddresses (p : Params) (core : CorePrimitives p)
    (messageAt : ℕ → core.Y) : List Adrs :=
  (List.range p.d1LeafCount).flatMap fun idxLeaf =>
    (List.range p.len).flatMap fun chain =>
      let digit := chainStepsCore core (messageAt idxLeaf) chain
      if digit = 0 then [] else
        [(wotsChainAdrs (wotsLeafAdrs Adrs.zero idxLeaf) chain).setHashAddress (digit - 1)]

/-- Reachable WOTS chain-step address space.  Actual TCR-C targets form a message-dependent
subsequence of this list.  There are only `w - 1` executed hash positions per chain; the source
reduction deliberately uses the looser `len * w` target cap. -/
def d1WotsTcrAddressSpace (p : Params) : List Adrs :=
  (List.range p.d1LeafCount).flatMap fun idxLeaf =>
    (List.range p.len).flatMap fun chain =>
      (List.range (p.w - 1)).map fun step =>
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

theorem d1WotsPreAddresses_length_le (p : Params) (core : CorePrimitives p)
    (messageAt : ℕ → core.Y) :
    (p.d1WotsPreAddresses core messageAt).length ≤ p.d1TargetProfile.wotsPre := by
  simp only [d1WotsPreAddresses, List.length_flatMap]
  calc
    (List.map
        (fun idxLeaf =>
          (List.map
            (fun chain =>
              (if chainStepsCore core (messageAt idxLeaf) chain = 0 then [] else
                [(wotsChainAdrs (wotsLeafAdrs Adrs.zero idxLeaf) chain).setHashAddress
                  (chainStepsCore core (messageAt idxLeaf) chain - 1)]).length)
            (List.range p.len)).sum)
        (List.range p.d1LeafCount)).sum ≤
        (List.map (fun _ => p.len) (List.range p.d1LeafCount)).sum := by
      apply List.sum_le_sum
      intro idxLeaf _
      calc
        _ ≤ (List.map (fun _ => 1) (List.range p.len)).sum := by
          apply List.sum_le_sum
          intro chain _
          split <;> simp
        _ = p.len := by simp
    _ = p.d1TargetProfile.wotsPre := by
      simp [d1TargetProfile, d1LeafCount]

theorem d1WotsTcrAddressSpace_length_le (p : Params) :
    p.d1WotsTcrAddressSpace.length ≤ p.d1TargetProfile.wotsTcr := by
  simp only [d1WotsTcrAddressSpace, List.length_flatMap, List.length_map,
    List.length_range]
  simp only [List.sum_replicate, List.map_const', nsmul_eq_mul]
  simp only [List.length_range]
  unfold d1TargetProfile
  calc
    p.d1LeafCount * (p.len * (p.w - 1)) =
        (p.d1LeafCount * p.len) * (p.w - 1) :=
      (Nat.mul_assoc _ _ _).symm
    _ ≤ (p.d1LeafCount * p.len) * p.w :=
      Nat.mul_le_mul_left _ (Nat.sub_le p.w 1)

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

def d1WotsPreTweaks (prims : Primitives p) (messageAt : ℕ → prims.Y) : List prims.AdrsKey :=
  prims.encodeTargets (p.d1WotsPreAddresses prims.core messageAt)

def d1WotsTcrTweakSpace (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1WotsTcrAddressSpace

def d1WotsPkTweaks (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1WotsPkAddresses

def d1XmssTreeTweaks (prims : Primitives p) : List prims.AdrsKey :=
  prims.encodeTargets p.d1XmssTreeAddresses

/-- Concrete address-encoding side condition for the target-selection phases of the `d = 1`
reductions.  The tweakable-hash games require distinct target tweaks, while `adrsToKey` need not
be globally injective (the SHA instantiation deliberately truncates ADRS).  Consequently the
right condition is `Nodup` on each reachable target family, including every message-dependent
WOTS PRE transcript, rather than a false global injectivity assumption.

The WOTS TCR field is stated for the whole reachable chain-step space, so it also covers every
message-dependent subsequence selected by the reduction.  Cross-disjointness from collection
queries remains a property of each concrete reduction transcript and is checked by the games'
final-validity monitor. -/
structure D1TargetTweakSeparation (prims : Primitives p) : Prop where
  forsLeaf : prims.d1ForsLeafTweaks.Nodup
  forsTree : prims.d1ForsTreeTweaks.Nodup
  forsRoots : prims.d1ForsRootsTweaks.Nodup
  wotsPre : ∀ messageAt : ℕ → prims.Y, (prims.d1WotsPreTweaks messageAt).Nodup
  wotsTcr : prims.d1WotsTcrTweakSpace.Nodup
  wotsPk : prims.d1WotsPkTweaks.Nodup
  xmssTree : prims.d1XmssTreeTweaks.Nodup

@[simp] theorem d1ForsLeafTweaks_length (prims : Primitives p) :
    prims.d1ForsLeafTweaks.length = p.d1TargetProfile.forsLeaf := by
  simp [d1ForsLeafTweaks, encodeTargets]

@[simp] theorem d1ForsTreeTweaks_length (prims : Primitives p) :
    prims.d1ForsTreeTweaks.length = p.d1TargetProfile.forsTree := by
  simp [d1ForsTreeTweaks, encodeTargets]

theorem d1WotsTcrTweakSpace_length_le (prims : Primitives p) :
    prims.d1WotsTcrTweakSpace.length ≤ p.d1TargetProfile.wotsTcr := by
  simpa [d1WotsTcrTweakSpace, encodeTargets] using p.d1WotsTcrAddressSpace_length_le

@[simp] theorem d1ForsRootsTweaks_length (prims : Primitives p) :
    prims.d1ForsRootsTweaks.length = p.d1TargetProfile.forsRoots := by
  simp [d1ForsRootsTweaks, encodeTargets]

theorem d1WotsPreTweaks_length_le (prims : Primitives p) (messageAt : ℕ → prims.Y) :
    (prims.d1WotsPreTweaks messageAt).length ≤ p.d1TargetProfile.wotsPre := by
  simpa [d1WotsPreTweaks, encodeTargets] using p.d1WotsPreAddresses_length_le prims.core messageAt

@[simp] theorem d1WotsPkTweaks_length (prims : Primitives p) :
    prims.d1WotsPkTweaks.length = p.d1TargetProfile.wotsPk := by
  simp [d1WotsPkTweaks, encodeTargets]

@[simp] theorem d1XmssTreeTweaks_length (prims : Primitives p) :
    prims.d1XmssTreeTweaks.length = p.d1TargetProfile.xmssTree := by
  simp [d1XmssTreeTweaks, encodeTargets]

end Primitives

end SLHDSA
