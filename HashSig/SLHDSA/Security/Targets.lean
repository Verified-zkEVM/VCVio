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

theorem perfectInternalCoords_height_pos {h : ℕ} {zi : ℕ × ℕ}
    (hmem : zi ∈ perfectInternalCoords h) : 0 < zi.1 := by
  induction h with
  | zero => simp [perfectInternalCoords] at hmem
  | succ h ih =>
      simp only [perfectInternalCoords, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨i, _, rfl⟩ | ⟨zi, hzi, rfl⟩
      · simp
      · exact Nat.succ_pos zi.1

/-- An internal coordinate's height never exceeds the height of its perfect tree. -/
theorem perfectInternalCoords_height_le {h : ℕ} {zi : ℕ × ℕ}
    (hmem : zi ∈ perfectInternalCoords h) : zi.1 ≤ h := by
  induction h generalizing zi with
  | zero => simp [perfectInternalCoords] at hmem
  | succ h ih =>
      simp only [perfectInternalCoords, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨i, _, rfl⟩ | ⟨zi, hzi, rfl⟩
      · exact Nat.succ_le_succ (Nat.zero_le h)
      · exact Nat.succ_le_succ (ih hzi)

/-- At height `z`, a perfect tree of height `h` has exactly `2^(h-z)` node positions. -/
theorem perfectInternalCoords_index_lt {h : ℕ} {zi : ℕ × ℕ}
    (hmem : zi ∈ perfectInternalCoords h) : zi.2 < 2 ^ (h - zi.1) := by
  induction h generalizing zi with
  | zero => simp [perfectInternalCoords] at hmem
  | succ h ih =>
      simp only [perfectInternalCoords, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨i, hi, rfl⟩ | ⟨zi, hzi, rfl⟩
      · simpa using hi
      · simpa only [Nat.succ_sub_succ_eq_sub] using ih hzi

/-- Internal perfect-tree coordinates are never repeated. -/
theorem perfectInternalCoords_nodup (h : ℕ) :
    (perfectInternalCoords h).Nodup := by
  induction h with
  | zero => simp [perfectInternalCoords]
  | succ h ih =>
      rw [perfectInternalCoords, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · exact List.nodup_range.map (fun _ _ hpair => Prod.mk.inj hpair |>.2)
      · exact ih.map (fun _ _ hpair => by
          have hfst := congrArg Prod.fst hpair
          have hsnd := congrArg Prod.snd hpair
          exact Prod.ext (Nat.succ.inj hfst) hsnd)
      · intro x hxLeft y hxRight hxy
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hxLeft
        obtain ⟨zi, hzi, rfl⟩ := List.mem_map.mp hxRight
        have hheight := congrArg Prod.fst hxy
        have hpos := perfectInternalCoords_height_pos hzi
        simp only at hheight
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

/-- FORS leaf addresses are structurally duplicate-free before concrete compression.  The
key-pair word identifies the XMSS leaf, while quotient and remainder of the global FORS leaf
index recover the tree and local leaf. -/
theorem d1ForsLeafAddresses_nodup (p : Params) :
    p.d1ForsLeafAddresses.Nodup := by
  let coords :=
    ((List.range p.d1LeafCount).product (List.range p.k)).product (List.range p.t)
  have hcoords : coords.Nodup :=
    (List.nodup_range.product List.nodup_range).product List.nodup_range
  have hmapped := hcoords.map_on (f := fun c : (ℕ × ℕ) × ℕ =>
      forsNodeAdrs (forsAdrsOf c.1.1) 0 (c.1.2 * p.t + c.2)) (by
    intro c hc d hd hadrs
    obtain ⟨ci, hci, cj, hcj, cl, hcl, rfl⟩ :
        ∃ ci < p.d1LeafCount, ∃ cj < p.k, ∃ cl < p.t, ((ci, cj), cl) = c := by
      simpa [coords, List.product] using hc
    obtain ⟨di, hdi, dj, hdj, dl, hdl, rfl⟩ :
        ∃ di < p.d1LeafCount, ∃ dj < p.k, ∃ dl < p.t, ((di, dj), dl) = d := by
      simpa [coords, List.product] using hd
    have houter : ci = di := by
      simpa [forsNodeAdrs, forsAdrsOf, Adrs.getKeyPairAddress,
        Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
        Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.zero] using
          congrArg Adrs.word1 hadrs
    have hglobal : cj * p.t + cl = dj * p.t + dl := by
      simpa [forsNodeAdrs, forsAdrsOf, Adrs.getKeyPairAddress,
        Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
        Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.zero] using
          congrArg Adrs.word3 hadrs
    have htpos : 0 < p.t := by unfold Params.t; positivity
    have htree : cj = dj := by
      have hdiv := congrArg (fun x => x / p.t) hglobal
      simpa [Nat.add_comm, Nat.add_mul_div_right, Nat.div_eq_of_lt,
        hcl, hdl, htpos] using hdiv
    have hleaf : cl = dl := by
      have hmod := congrArg (fun x => x % p.t) hglobal
      simpa [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt,
        hcl, hdl] using hmod
    exact Prod.ext (Prod.ext houter htree) hleaf)
  simpa [coords, List.product, d1ForsLeafAddresses, List.map_flatMap,
    List.flatMap_map, List.flatMap_assoc, List.map_map, Function.comp_def] using hmapped

@[simp] theorem d1ForsTreeAddresses_length (p : Params) :
    p.d1ForsTreeAddresses.length = p.d1TargetProfile.forsTree := by
  simp [d1ForsTreeAddresses, d1TargetProfile, d1LeafCount, t, Nat.mul_assoc]

/-- FORS internal-node addresses are structurally duplicate-free before concrete compression. -/
theorem d1ForsTreeAddresses_nodup (p : Params) :
    p.d1ForsTreeAddresses.Nodup := by
  let coords :=
    ((List.range p.d1LeafCount).product (List.range p.k)).product
      (perfectInternalCoords p.a)
  have hcoords : coords.Nodup :=
    (List.nodup_range.product List.nodup_range).product
      (perfectInternalCoords_nodup p.a)
  have hmapped := hcoords.map_on (f := fun c : (ℕ × ℕ) × (ℕ × ℕ) =>
      forsNodeAdrs (forsAdrsOf c.1.1) c.2.1
        (c.1.2 * 2 ^ (p.a - c.2.1) + c.2.2)) (by
    intro c hc d hd hadrs
    obtain ⟨ci, hci, cj, hcj, cz, hcz, rfl⟩ :
        ∃ ci < p.d1LeafCount, ∃ cj < p.k, ∃ cz ∈ perfectInternalCoords p.a,
          ((ci, cj), cz) = c := by
      simpa [coords, List.product] using hc
    obtain ⟨di, hdi, dj, hdj, dz, hdz, rfl⟩ :
        ∃ di < p.d1LeafCount, ∃ dj < p.k, ∃ dz ∈ perfectInternalCoords p.a,
          ((di, dj), dz) = d := by
      simpa [coords, List.product] using hd
    have houter : ci = di := by
      simpa [forsNodeAdrs, forsAdrsOf, Adrs.getKeyPairAddress,
        Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
        Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.zero] using
          congrArg Adrs.word1 hadrs
    have hheight : cz.1 = dz.1 := by
      simpa [forsNodeAdrs, forsAdrsOf, Adrs.getKeyPairAddress,
        Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
        Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.zero] using
          congrArg Adrs.word2 hadrs
    have hglobal : cj * 2 ^ (p.a - cz.1) + cz.2 =
        dj * 2 ^ (p.a - dz.1) + dz.2 := by
      simpa [forsNodeAdrs, forsAdrsOf, Adrs.getKeyPairAddress,
        Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
        Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.zero] using
          congrArg Adrs.word3 hadrs
    rw [hheight] at hglobal
    have hczBound := perfectInternalCoords_index_lt hcz
    have hdzBound := perfectInternalCoords_index_lt hdz
    have hczBound' : cz.2 < 2 ^ (p.a - dz.1) := by simpa [hheight] using hczBound
    have hpow : 0 < 2 ^ (p.a - dz.1) := by positivity
    have htree : cj = dj := by
      have hdiv := congrArg (fun x => x / 2 ^ (p.a - dz.1)) hglobal
      simpa [Nat.add_comm, Nat.add_mul_div_right, Nat.div_eq_of_lt,
        hczBound', hdzBound, hpow] using hdiv
    have hnode : cz.2 = dz.2 := by
      have hmod := congrArg (fun x => x % 2 ^ (p.a - dz.1)) hglobal
      simpa [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt,
        hczBound', hdzBound] using hmod
    exact Prod.ext (Prod.ext houter htree) (Prod.ext hheight hnode))
  simpa [coords, List.product, d1ForsTreeAddresses, List.map_flatMap,
    List.flatMap_map, List.flatMap_assoc, List.map_map, Function.comp_def] using hmapped

@[simp] theorem d1ForsRootsAddresses_length (p : Params) :
    p.d1ForsRootsAddresses.length = p.d1TargetProfile.forsRoots := by
  simp [d1ForsRootsAddresses, d1TargetProfile, d1LeafCount]

/-- FORS-root-compression addresses are structurally distinct before concrete encoding: their
key-pair word is exactly the XMSS leaf index. -/
theorem d1ForsRootsAddresses_nodup (p : Params) :
    p.d1ForsRootsAddresses.Nodup := by
  apply List.Nodup.map_on (d := List.nodup_range)
  intro i _ j _ hij
  have hword := congrArg Adrs.word1 hij
  simpa [forsPkAdrs, forsAdrsOf, Adrs.getKeyPairAddress, Adrs.setKeyPairAddress,
    Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.zero] using hword

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

/-- Every message-dependent WOTS PRE transcript is structurally duplicate-free before concrete
address compression.  Even though the selected hash step depends on the message, the leaf and
chain words already identify each possible entry. -/
theorem d1WotsPreAddresses_nodup (p : Params) (core : CorePrimitives p)
    (messageAt : ℕ → core.Y) :
    (p.d1WotsPreAddresses core messageAt).Nodup := by
  let coords := (List.range p.d1LeafCount).product (List.range p.len)
  let encode : ℕ × ℕ → Option Adrs := fun c =>
    let digit := chainStepsCore core (messageAt c.1) c.2
    if digit = 0 then none else
      some ((wotsChainAdrs (wotsLeafAdrs Adrs.zero c.1) c.2).setHashAddress (digit - 1))
  have hcoords : coords.Nodup := List.nodup_range.product List.nodup_range
  have hunique : ∀ a a' b, b ∈ encode a → b ∈ encode a' → a = a' := by
    intro a a' b hb hb'
    simp only [encode] at hb hb'
    split at hb <;> simp_all only [Option.not_mem_none, Option.mem_some_iff]
    split at hb' <;> simp_all only [Option.not_mem_none, Option.mem_some_iff]
    subst hb
    have hadrs := hb'
    apply Prod.ext
    · simpa [wotsChainAdrs, wotsLeafAdrs, Adrs.getKeyPairAddress,
        Adrs.setHashAddress, Adrs.setChainAddress, Adrs.setKeyPairAddress,
        Adrs.setTypeAndClear, Adrs.zero] using (congrArg Adrs.word1 hadrs).symm
    · simpa [wotsChainAdrs, wotsLeafAdrs, Adrs.getKeyPairAddress,
        Adrs.setHashAddress, Adrs.setChainAddress, Adrs.setKeyPairAddress,
        Adrs.setTypeAndClear, Adrs.zero] using (congrArg Adrs.word2 hadrs).symm
  have hencoded := hcoords.filterMap hunique
  rw [List.filterMap_eq_flatMap_toList] at hencoded
  have hencode_toList : ∀ c : ℕ × ℕ,
      (encode c).toList =
        (let digit := chainStepsCore core (messageAt c.1) c.2
         if digit = 0 then [] else
           [(wotsChainAdrs (wotsLeafAdrs Adrs.zero c.1) c.2).setHashAddress (digit - 1)]) := by
    intro c
    simp only [encode]
    split <;> simp_all
  simp_rw [hencode_toList] at hencoded
  simpa [coords, encode, List.product, d1WotsPreAddresses, List.flatMap_map,
    List.flatMap_assoc, Function.comp_def] using hencoded

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

/-- The complete reachable WOTS chain-step space is structurally duplicate-free before address
compression.  Its three varying words recover `(leaf, chain, step)` exactly. -/
theorem d1WotsTcrAddressSpace_nodup (p : Params) :
    p.d1WotsTcrAddressSpace.Nodup := by
  let coords :=
    ((List.range p.d1LeafCount).product (List.range p.len)).product
      (List.range (p.w - 1))
  have hcoords : coords.Nodup :=
    (List.nodup_range.product List.nodup_range).product List.nodup_range
  have hinj : Function.Injective (fun c : (ℕ × ℕ) × ℕ =>
      (wotsChainAdrs (wotsLeafAdrs Adrs.zero c.1.1) c.1.2).setHashAddress c.2) := by
    intro c d h
    apply Prod.ext
    · apply Prod.ext
      · simpa [wotsChainAdrs, wotsLeafAdrs, Adrs.getKeyPairAddress,
          Adrs.setHashAddress, Adrs.setChainAddress, Adrs.setKeyPairAddress,
          Adrs.setTypeAndClear, Adrs.zero] using congrArg Adrs.word1 h
      · simpa [wotsChainAdrs, wotsLeafAdrs, Adrs.getKeyPairAddress,
          Adrs.setHashAddress, Adrs.setChainAddress, Adrs.setKeyPairAddress,
          Adrs.setTypeAndClear, Adrs.zero] using congrArg Adrs.word2 h
    · simpa [wotsChainAdrs, wotsLeafAdrs, Adrs.getKeyPairAddress,
        Adrs.setHashAddress, Adrs.setChainAddress, Adrs.setKeyPairAddress,
        Adrs.setTypeAndClear, Adrs.zero] using congrArg Adrs.word3 h
  have hmapped := hcoords.map hinj
  simpa [coords, List.product, d1WotsTcrAddressSpace, List.map_flatMap,
    List.flatMap_map, List.flatMap_assoc, List.map_map, Function.comp_def] using hmapped

@[simp] theorem d1WotsPkAddresses_length (p : Params) :
    p.d1WotsPkAddresses.length = p.d1TargetProfile.wotsPk := by
  simp [d1WotsPkAddresses, d1TargetProfile, d1LeafCount]

/-- WOTS public-key-compression addresses are structurally distinct before concrete encoding. -/
theorem d1WotsPkAddresses_nodup (p : Params) :
    p.d1WotsPkAddresses.Nodup := by
  apply List.Nodup.map_on (d := List.nodup_range)
  intro i _ j _ hij
  have hword := congrArg Adrs.word1 hij
  simpa [wotsPkAdrs, wotsLeafAdrs, Adrs.getKeyPairAddress, Adrs.setKeyPairAddress,
    Adrs.setTypeAndClear, Adrs.zero] using hword

@[simp] theorem d1XmssTreeAddresses_length (p : Params) :
    p.d1XmssTreeAddresses.length = p.d1TargetProfile.xmssTree := by
  simp [d1XmssTreeAddresses, d1TargetProfile, d1LeafCount]

/-- XMSS internal-node addresses are structurally duplicate-free before concrete compression. -/
theorem d1XmssTreeAddresses_nodup (p : Params) :
    p.d1XmssTreeAddresses.Nodup := by
  apply List.Nodup.map_on (d := perfectInternalCoords_nodup p.hp)
  intro zi _ zj _ hadrs
  apply Prod.ext
  · simpa [xmssNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
      Adrs.setTypeAndClear, Adrs.zero] using congrArg Adrs.word2 hadrs
  · simpa [xmssNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex,
      Adrs.setTypeAndClear, Adrs.zero] using congrArg Adrs.word3 hadrs

end Params

namespace Primitives

variable {p : Params}

/-- Encode a reachable address list with the primitive bundle's actual tweak function. -/
def encodeTargets (prims : Primitives p) (addresses : List Adrs) : List prims.AdrsKey :=
  addresses.map prims.adrsToKey

/-- Exact proof interface for compressed-address separation: once an unencoded address list is
known to be duplicate-free, its encoded image is duplicate-free iff `adrsToKey` is injective on
that reachable list.  This avoids asking for the false global injectivity property of SHA ADRSc. -/
theorem encodeTargets_nodup_iff_injOn (prims : Primitives p) (addresses : List Adrs)
    (haddresses : addresses.Nodup) :
    (prims.encodeTargets addresses).Nodup ↔
      ∀ a ∈ addresses, ∀ b ∈ addresses, prims.adrsToKey a = prims.adrsToKey b → a = b := by
  simpa [encodeTargets] using List.nodup_map_iff_inj_on (f := prims.adrsToKey) haddresses

/-- Forward constructor form of `encodeTargets_nodup_iff_injOn`. -/
theorem encodeTargets_nodup_of_injOn (prims : Primitives p) (addresses : List Adrs)
    (haddresses : addresses.Nodup)
    (hinj : ∀ a ∈ addresses, ∀ b ∈ addresses,
      prims.adrsToKey a = prims.adrsToKey b → a = b) :
    (prims.encodeTargets addresses).Nodup :=
  (prims.encodeTargets_nodup_iff_injOn addresses haddresses).2 hinj

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

/-- Build the exact game-facing separation certificate from injectivity of the concrete address
encoding on each reachable target family.  The structural `Nodup` facts are unconditional and
proved above; consequently a concrete SHA instantiation need only reason about the information
retained by `ADRSc` on these seven restricted domains. -/
theorem D1TargetTweakSeparation.ofInjOn (prims : Primitives p)
    (hForsLeaf : ∀ a ∈ p.d1ForsLeafAddresses, ∀ b ∈ p.d1ForsLeafAddresses,
      prims.adrsToKey a = prims.adrsToKey b → a = b)
    (hForsTree : ∀ a ∈ p.d1ForsTreeAddresses, ∀ b ∈ p.d1ForsTreeAddresses,
      prims.adrsToKey a = prims.adrsToKey b → a = b)
    (hForsRoots : ∀ a ∈ p.d1ForsRootsAddresses, ∀ b ∈ p.d1ForsRootsAddresses,
      prims.adrsToKey a = prims.adrsToKey b → a = b)
    (hWotsPre : ∀ messageAt : ℕ → prims.Y,
      ∀ a ∈ p.d1WotsPreAddresses prims.core messageAt,
        ∀ b ∈ p.d1WotsPreAddresses prims.core messageAt,
          prims.adrsToKey a = prims.adrsToKey b → a = b)
    (hWotsTcr : ∀ a ∈ p.d1WotsTcrAddressSpace, ∀ b ∈ p.d1WotsTcrAddressSpace,
      prims.adrsToKey a = prims.adrsToKey b → a = b)
    (hWotsPk : ∀ a ∈ p.d1WotsPkAddresses, ∀ b ∈ p.d1WotsPkAddresses,
      prims.adrsToKey a = prims.adrsToKey b → a = b)
    (hXmssTree : ∀ a ∈ p.d1XmssTreeAddresses, ∀ b ∈ p.d1XmssTreeAddresses,
      prims.adrsToKey a = prims.adrsToKey b → a = b) :
    D1TargetTweakSeparation prims where
  forsLeaf := prims.encodeTargets_nodup_of_injOn _ p.d1ForsLeafAddresses_nodup hForsLeaf
  forsTree := prims.encodeTargets_nodup_of_injOn _ p.d1ForsTreeAddresses_nodup hForsTree
  forsRoots := prims.encodeTargets_nodup_of_injOn _ p.d1ForsRootsAddresses_nodup hForsRoots
  wotsPre messageAt := prims.encodeTargets_nodup_of_injOn _
    (p.d1WotsPreAddresses_nodup prims.core messageAt) (hWotsPre messageAt)
  wotsTcr := prims.encodeTargets_nodup_of_injOn _ p.d1WotsTcrAddressSpace_nodup hWotsTcr
  wotsPk := prims.encodeTargets_nodup_of_injOn _ p.d1WotsPkAddresses_nodup hWotsPk
  xmssTree := prims.encodeTargets_nodup_of_injOn _ p.d1XmssTreeAddresses_nodup hXmssTree

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
