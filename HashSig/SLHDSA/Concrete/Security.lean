/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Concrete.Instance
public import HashSig.SLHDSA.Security.Targets

/-!
# Concrete SHA2-128-24 security side conditions

This module discharges the two representation-level hypotheses used by the generic `d = 1`
SLH-DSA reduction: full-width WOTS message encoding (proved in `Concrete.Instance`) and separation
of every reachable target tweak after FIPS 205 `ADRSc` compression.

The latter statement is deliberately restricted to the seven target families.  `ADRSc` is not
globally injective, but all coordinates retained by those families fit in its 32-bit words.
-/

@[expose] public section

namespace SLHDSA.Concrete

open SLHDSA

/-- Lift restricted injectivity of the list-valued `ADRSc` encoding to its fixed-width vector. -/
theorem shaAdrsKey_injective_of_header_eq {a b : Adrs}
    (hlayer : a.layer = b.layer) (htree : a.tree = b.tree) (htype : a.type = b.type)
    (ha1 : a.word1 < 4294967296) (hb1 : b.word1 < 4294967296)
    (ha2 : a.word2 < 4294967296) (hb2 : b.word2 < 4294967296)
    (ha3 : a.word3 < 4294967296) (hb3 : b.word3 < 4294967296)
    (h : shaAdrsKey a = shaAdrsKey b) : a = b := by
  apply Adrs.compressSha2_injective_of_header_eq hlayer htree htype ha1 hb1 ha2 hb2 ha3 hb3
  simpa using congrArg Vector.toList h

private theorem shaAdrsKey_injective_on_d1ForsLeafAddresses :
    ∀ a ∈ slhdsaSha2_128_24.d1ForsLeafAddresses,
      ∀ b ∈ slhdsaSha2_128_24.d1ForsLeafAddresses,
        shaAdrsKey a = shaAdrsKey b → a = b := by
  intro a ha b hb hab
  obtain ⟨ai, hai, aj, haj, al, hal, rfl⟩ :
      ∃ ai < slhdsaSha2_128_24.d1LeafCount,
        ∃ aj < slhdsaSha2_128_24.k, ∃ al < slhdsaSha2_128_24.t,
          forsNodeAdrs (forsAdrsOf ai) 0 (aj * slhdsaSha2_128_24.t + al) = a := by
    simpa [Params.d1ForsLeafAddresses] using ha
  obtain ⟨bi, hbi, bj, hbj, bl, hbl, rfl⟩ :
      ∃ bi < slhdsaSha2_128_24.d1LeafCount,
        ∃ bj < slhdsaSha2_128_24.k, ∃ bl < slhdsaSha2_128_24.t,
          forsNodeAdrs (forsAdrsOf bi) 0 (bj * slhdsaSha2_128_24.t + bl) = b := by
    simpa [Params.d1ForsLeafAddresses] using hb
  apply shaAdrsKey_injective_of_header_eq <;>
    simp [forsNodeAdrs, forsAdrsOf, Adrs.getKeyPairAddress,
      Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
      Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.zero,
      slhdsaSha2_128_24, ParameterSet.params, Params.d1LeafCount, Params.t] at * <;>
    omega

private theorem shaAdrsKey_injective_on_d1ForsRootsAddresses :
    ∀ a ∈ slhdsaSha2_128_24.d1ForsRootsAddresses,
      ∀ b ∈ slhdsaSha2_128_24.d1ForsRootsAddresses,
        shaAdrsKey a = shaAdrsKey b → a = b := by
  intro a ha b hb hab
  obtain ⟨ai, hai, rfl⟩ : ∃ ai < slhdsaSha2_128_24.d1LeafCount,
      forsPkAdrs (forsAdrsOf ai) = a := by
    simpa [Params.d1ForsRootsAddresses] using ha
  obtain ⟨bi, hbi, rfl⟩ : ∃ bi < slhdsaSha2_128_24.d1LeafCount,
      forsPkAdrs (forsAdrsOf bi) = b := by
    simpa [Params.d1ForsRootsAddresses] using hb
  apply shaAdrsKey_injective_of_header_eq <;>
    simp [forsPkAdrs, forsAdrsOf, Adrs.getKeyPairAddress,
      Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.zero,
      slhdsaSha2_128_24, ParameterSet.params, Params.d1LeafCount] at * <;>
    omega

private theorem shaAdrsKey_injective_on_d1WotsPkAddresses :
    ∀ a ∈ slhdsaSha2_128_24.d1WotsPkAddresses,
      ∀ b ∈ slhdsaSha2_128_24.d1WotsPkAddresses,
        shaAdrsKey a = shaAdrsKey b → a = b := by
  intro a ha b hb hab
  obtain ⟨ai, hai, rfl⟩ : ∃ ai < slhdsaSha2_128_24.d1LeafCount,
      wotsPkAdrs (wotsLeafAdrs Adrs.zero ai) = a := by
    simpa [Params.d1WotsPkAddresses] using ha
  obtain ⟨bi, hbi, rfl⟩ : ∃ bi < slhdsaSha2_128_24.d1LeafCount,
      wotsPkAdrs (wotsLeafAdrs Adrs.zero bi) = b := by
    simpa [Params.d1WotsPkAddresses] using hb
  apply shaAdrsKey_injective_of_header_eq <;>
    simp [wotsPkAdrs, wotsLeafAdrs, Adrs.getKeyPairAddress,
      Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.zero,
      slhdsaSha2_128_24, ParameterSet.params, Params.d1LeafCount] at * <;>
    omega

private theorem shaAdrsKey_injective_on_d1WotsTcrAddressSpace :
    ∀ a ∈ slhdsaSha2_128_24.d1WotsTcrAddressSpace,
      ∀ b ∈ slhdsaSha2_128_24.d1WotsTcrAddressSpace,
        shaAdrsKey a = shaAdrsKey b → a = b := by
  intro a ha b hb hab
  obtain ⟨ai, hai, ac, hac, astep, hastep, rfl⟩ :
      ∃ ai < slhdsaSha2_128_24.d1LeafCount,
        ∃ ac < slhdsaSha2_128_24.len, ∃ astep < slhdsaSha2_128_24.w - 1,
          (wotsChainAdrs (wotsLeafAdrs Adrs.zero ai) ac).setHashAddress astep = a := by
    simpa [Params.d1WotsTcrAddressSpace] using ha
  obtain ⟨bi, hbi, bc, hbc, bstep, hbstep, rfl⟩ :
      ∃ bi < slhdsaSha2_128_24.d1LeafCount,
        ∃ bc < slhdsaSha2_128_24.len, ∃ bstep < slhdsaSha2_128_24.w - 1,
          (wotsChainAdrs (wotsLeafAdrs Adrs.zero bi) bc).setHashAddress bstep = b := by
    simpa [Params.d1WotsTcrAddressSpace] using hb
  have hlen : slhdsaSha2_128_24.len = 68 := by decide
  rw [hlen] at hac hbc
  apply shaAdrsKey_injective_of_header_eq <;>
    simp [wotsChainAdrs, wotsLeafAdrs, Adrs.getKeyPairAddress, Adrs.setHashAddress,
      Adrs.setChainAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.zero,
      slhdsaSha2_128_24, ParameterSet.params, Params.d1LeafCount, Params.len, Params.len1,
      Params.len2, Params.w] at * <;>
    omega

private theorem shaAdrsKey_injective_on_d1WotsPreAddresses
    (messageAt : ℕ → shaPrimitives.Y) :
    ∀ a ∈ slhdsaSha2_128_24.d1WotsPreAddresses shaPrimitives.core messageAt,
      ∀ b ∈ slhdsaSha2_128_24.d1WotsPreAddresses shaPrimitives.core messageAt,
        shaAdrsKey a = shaAdrsKey b → a = b := by
  intro a ha b hb hab
  obtain ⟨ai, hai, ac, hac, hadigit, rfl⟩ :
      ∃ ai < slhdsaSha2_128_24.d1LeafCount,
        ∃ ac < slhdsaSha2_128_24.len,
          chainStepsCore shaPrimitives.core (messageAt ai) ac ≠ 0 ∧
            a = (wotsChainAdrs (wotsLeafAdrs Adrs.zero ai) ac).setHashAddress
              (chainStepsCore shaPrimitives.core (messageAt ai) ac - 1) := by
    simpa [Params.d1WotsPreAddresses] using ha
  obtain ⟨bi, hbi, bc, hbc, hbdigit, rfl⟩ :
      ∃ bi < slhdsaSha2_128_24.d1LeafCount,
        ∃ bc < slhdsaSha2_128_24.len,
          chainStepsCore shaPrimitives.core (messageAt bi) bc ≠ 0 ∧
            b = (wotsChainAdrs (wotsLeafAdrs Adrs.zero bi) bc).setHashAddress
              (chainStepsCore shaPrimitives.core (messageAt bi) bc - 1) := by
    simpa [Params.d1WotsPreAddresses] using hb
  have hadigitBound := chainStepsCore_lt shaPrimitives.core (messageAt ai) ac
  have hbdigitBound := chainStepsCore_lt shaPrimitives.core (messageAt bi) bc
  have hlen : slhdsaSha2_128_24.len = 68 := by decide
  rw [hlen] at hac hbc
  apply shaAdrsKey_injective_of_header_eq <;>
    simp [wotsChainAdrs, wotsLeafAdrs, Adrs.getKeyPairAddress, Adrs.setHashAddress,
      Adrs.setChainAddress, Adrs.setKeyPairAddress, Adrs.setTypeAndClear, Adrs.zero,
      slhdsaSha2_128_24, ParameterSet.params, Params.d1LeafCount, Params.w] at * <;>
    omega

private theorem shaAdrsKey_injective_on_d1ForsTreeAddresses :
    ∀ a ∈ slhdsaSha2_128_24.d1ForsTreeAddresses,
      ∀ b ∈ slhdsaSha2_128_24.d1ForsTreeAddresses,
        shaAdrsKey a = shaAdrsKey b → a = b := by
  intro a ha b hb hab
  obtain ⟨ai, hai, aj, haj, azi, hazi, rfl⟩ :
      ∃ ai < slhdsaSha2_128_24.d1LeafCount,
        ∃ aj < slhdsaSha2_128_24.k,
          ∃ azi ∈ perfectInternalCoords slhdsaSha2_128_24.a,
            forsNodeAdrs (forsAdrsOf ai) azi.1
              (aj * 2 ^ (slhdsaSha2_128_24.a - azi.1) + azi.2) = a := by
    simpa [Params.d1ForsTreeAddresses] using ha
  obtain ⟨bi, hbi, bj, hbj, bzi, hbzi, rfl⟩ :
      ∃ bi < slhdsaSha2_128_24.d1LeafCount,
        ∃ bj < slhdsaSha2_128_24.k,
          ∃ bzi ∈ perfectInternalCoords slhdsaSha2_128_24.a,
            forsNodeAdrs (forsAdrsOf bi) bzi.1
              (bj * 2 ^ (slhdsaSha2_128_24.a - bzi.1) + bzi.2) = b := by
    simpa [Params.d1ForsTreeAddresses] using hb
  have ahle := perfectInternalCoords_height_le hazi
  have bhle := perfectInternalCoords_height_le hbzi
  have aidx := perfectInternalCoords_index_lt hazi
  have bidx := perfectInternalCoords_index_lt hbzi
  have apow : 2 ^ (slhdsaSha2_128_24.a - azi.1) ≤ 2 ^ slhdsaSha2_128_24.a :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have bpow : 2 ^ (slhdsaSha2_128_24.a - bzi.1) ≤ 2 ^ slhdsaSha2_128_24.a :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have aqpos : 0 < 2 ^ (slhdsaSha2_128_24.a - azi.1) := by positivity
  have bqpos : 0 < 2 ^ (slhdsaSha2_128_24.a - bzi.1) := by positivity
  norm_num [slhdsaSha2_128_24, ParameterSet.params] at haj hbj
  have aword3 :
      aj * 2 ^ (slhdsaSha2_128_24.a - azi.1) + azi.2 < 4294967296 := by
    calc
      _ < 6 * 2 ^ (slhdsaSha2_128_24.a - azi.1) := by nlinarith
      _ ≤ 6 * 2 ^ slhdsaSha2_128_24.a := Nat.mul_le_mul_left 6 apow
      _ < 4294967296 := by decide
  have bword3 :
      bj * 2 ^ (slhdsaSha2_128_24.a - bzi.1) + bzi.2 < 4294967296 := by
    calc
      _ < 6 * 2 ^ (slhdsaSha2_128_24.a - bzi.1) := by nlinarith
      _ ≤ 6 * 2 ^ slhdsaSha2_128_24.a := Nat.mul_le_mul_left 6 bpow
      _ < 4294967296 := by decide
  apply shaAdrsKey_injective_of_header_eq <;>
    simp [forsNodeAdrs, forsAdrsOf, Adrs.getKeyPairAddress,
      Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
      Adrs.setTypeAndClear, Adrs.setTreeAddress, Adrs.zero,
      slhdsaSha2_128_24, ParameterSet.params, Params.d1LeafCount] at * <;>
    omega

private theorem shaAdrsKey_injective_on_d1XmssTreeAddresses :
    ∀ a ∈ slhdsaSha2_128_24.d1XmssTreeAddresses,
      ∀ b ∈ slhdsaSha2_128_24.d1XmssTreeAddresses,
        shaAdrsKey a = shaAdrsKey b → a = b := by
  intro a ha b hb hab
  obtain ⟨azi, hazi, rfl⟩ := List.mem_map.mp ha
  obtain ⟨bzi, hbzi, rfl⟩ := List.mem_map.mp hb
  have ahle := perfectInternalCoords_height_le hazi
  have bhle := perfectInternalCoords_height_le hbzi
  have aidx := perfectInternalCoords_index_lt hazi
  have bidx := perfectInternalCoords_index_lt hbzi
  have apow : 2 ^ (slhdsaSha2_128_24.hp - azi.1) ≤ 2 ^ slhdsaSha2_128_24.hp :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have bpow : 2 ^ (slhdsaSha2_128_24.hp - bzi.1) ≤ 2 ^ slhdsaSha2_128_24.hp :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  apply shaAdrsKey_injective_of_header_eq <;>
    simp [xmssNodeAdrs, Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.setTypeAndClear,
      Adrs.zero, slhdsaSha2_128_24, ParameterSet.params] at * <;>
    omega

/-- Every reachable `d = 1` target family has distinct encoded tweaks for the concrete
SLH-DSA-SHA2-128-24 primitive bundle. -/
theorem shaPrimitives_d1TargetTweakSeparation :
    Primitives.D1TargetTweakSeparation shaPrimitives :=
  Primitives.D1TargetTweakSeparation.ofInjOn shaPrimitives
    shaAdrsKey_injective_on_d1ForsLeafAddresses
    shaAdrsKey_injective_on_d1ForsTreeAddresses
    shaAdrsKey_injective_on_d1ForsRootsAddresses
    (fun messageAt => shaAdrsKey_injective_on_d1WotsPreAddresses messageAt)
    shaAdrsKey_injective_on_d1WotsTcrAddressSpace
    shaAdrsKey_injective_on_d1WotsPkAddresses
    shaAdrsKey_injective_on_d1XmssTreeAddresses

end SLHDSA.Concrete
