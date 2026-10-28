/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Security.AddressKeys
public import HashSig.SLHDSA.Security.RomDescentSecret

/-!
# The ledger range of a WOTS+ chain honest entry

Regression checks for the address premise of `Security.HonestEntry.wotsChain`, at the FIPS
parameter set SLH-DSA-SHAKE-128s (`w = 16`, `len = 35`).

The premise places the entry address `(wotsChainAdrs adrs i).setHashAddress t` in the union ledger
`Security.constructionAddresses`. That forces the hash address below the top step, `t < w - 1`,
and the chain index below `len` (`wotsChain_hmem_range`). The FIPS 205 address encodes the hash
address in a 32-bit word, so the lapped step address `t + 2 ^ 32` shares its key with step `t`;
the premise excludes it, because the lapped address is not in the ledger (`lap_not_mem`).
-/

public section

namespace SLHDSA.BridgeEventsTest

open Security

/-- The FIPS parameter set SLH-DSA-SHAKE-128s. -/
abbrev shake128s : ValidatedParams :=
  FipsParameterSet.validatedParams .SLHDSA_SHAKE_128s

/-- At SLH-DSA-SHAKE-128s, a WOTS+ hash-step address in the union ledger has hash address
`t < 15` and chain index `i < 35`. -/
theorem wotsChain_hmem_range {adrs : Adrs} {i t : ℕ}
    (hmem : (wotsChainAdrs adrs i).setHashAddress t ∈ constructionAddresses shake128s) :
    t < 15 ∧ i < 35 := by
  rw [mem_constructionAddresses_iff] at hmem
  rcases hmem with h | h | h | h | h | h
  · simp only [forsLeafAddresses, List.mem_map] at h
    obtain ⟨_, -, he⟩ := h
    have := congrArg Adrs.type he
    simp [forsNodeAdrs_eq, wotsChainAdrs_setHashAddress_eq] at this
  · simp only [forsTreeAddresses, List.mem_map] at h
    obtain ⟨_, -, he⟩ := h
    have := congrArg Adrs.type he
    simp [forsNodeAdrs_eq, wotsChainAdrs_setHashAddress_eq] at this
  · simp only [forsRootAddresses, List.mem_map] at h
    obtain ⟨_, -, he⟩ := h
    have := congrArg Adrs.type he
    simp [forsPkAdrs, Adrs.setKeyPairAddress, Adrs.setTypeAndClear,
      wotsChainAdrs_setHashAddress_eq, AddrType.toCode] at this
  · simp only [wotsStepAddresses, List.mem_map] at h
    obtain ⟨⟨⟨_, ci⟩, st⟩, -, he⟩ := h
    simp only [wotsStepAdrs, wotsChainAdrs_setHashAddress_eq, Adrs.mk.injEq] at he
    obtain ⟨-, -, -, -, rfl, rfl⟩ := he
    exact ⟨st.isLt, ci.isLt⟩
  · simp only [wotsPkAddresses, List.mem_map] at h
    obtain ⟨_, -, he⟩ := h
    have := congrArg Adrs.type he
    simp [wotsPkAdrs_eq, wotsChainAdrs_setHashAddress_eq] at this
  · simp only [xmssNodeAddresses, List.mem_map] at h
    obtain ⟨_, -, he⟩ := h
    have := congrArg Adrs.type he
    simp [xmssNodeAdrs_eq, wotsChainAdrs_setHashAddress_eq] at this

/-- At SLH-DSA-SHAKE-128s, the lapped hash-step address `t + 2 ^ 32` of any WOTS+ chain is not in
the union ledger. -/
theorem lap_not_mem (adrs : Adrs) (i t : ℕ) :
    (wotsChainAdrs adrs i).setHashAddress (t + 2 ^ 32) ∉ constructionAddresses shake128s :=
  fun h => absurd (wotsChain_hmem_range h).1 (by omega)

end SLHDSA.BridgeEventsTest
