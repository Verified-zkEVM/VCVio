/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSig.SLHDSA.Security.RomDescentSecret
import HashSig.SLHDSA.Security.AddressKeys

/-!
# Uniqueness of the honest input at a tweakable-hash key

Under key injectivity on the in-range addresses (`CorePrimitives.KeyInjective`) and the FIPS 205
address widths (`CanonicalAddressBounds`), an oracle key carries at most one honest input:
two honest entries (`HonestEntry`) at one `thash` key, for one provider, public seed and cache,
have equal inputs (`honestEntry_input_unique`).

The argument has three steps.

* Every address of the union ledger `constructionAddresses vp` is in range
  (`addressFacts_of_mem_constructionAddresses`), and each constructor of `HonestEntry` places its
  entry address in that ledger, so key injectivity makes the two entry addresses equal.
* Equal entry addresses have equal type words, which fixes the constructor: the six entry
  addresses have types `2` (XMSS node), `1` (WOTS+ public key), `0` (WOTS+ chain step), `3` (FORS
  leaf and FORS node) and `4` (FORS roots), and a FORS leaf sits at tree height `0` while a FORS
  node of `HonestEntry` sits at a positive height.  Equal entry addresses of one constructor have
  equal fields.
* The cache readers an honest entry consults depend on the base address only through the fields
  the entry address records: the layer and the tree for the XMSS reader, and in addition the key
  pair for the WOTS+ and FORS readers.  These dependencies are definitional
  (`xmssNodeWithSecret?_base`, `wotsPkGenTopsWithSecret?_base`, `wotsChainAdrs_base`,
  `wotsSkAdrs_base`, `forsSkAdrs_base`, `forsNodeWithSecret?_base`), so the two entries read the
  same values and their inputs agree.

## Labels

Nine declarations, none private.

*Ledger addresses are in range*: `addressFacts_of_mem_constructionAddresses`.

*Base-address dependencies of the readers*: `xmssNodeWithSecret?_base`,
`wotsPkGenTopsWithSecret?_base`, `wotsChainAdrs_base`, `wotsSkAdrs_base`, `forsSkAdrs_base`,
`forsNodeWithSecret?_base`.

*Uniqueness*: `honestEntry_input_unique`, `CorePrimitives.KeyDiscipline.honestEntry_input_unique`.

## References

- NIST FIPS 205, §4.2 (ADRS and its type words)
-/

public section

namespace SLHDSA

namespace Security

/-! ## Ledger addresses are in range -/

/-- Every address of the union ledger is FIPS-canonical and lies in the hypertree's layer and tree
ranges. -/
theorem addressFacts_of_mem_constructionAddresses {vp : ValidatedParams}
    (hb : CanonicalAddressBounds vp.params) {a : Adrs} (ha : a ∈ constructionAddresses vp) :
    AddressFacts vp a := by
  rcases (mem_constructionAddresses_iff a).1 ha with h | h | h | h | h | h
  · exact addressFacts_forsLeafAddresses vp hb a h
  · exact addressFacts_forsTreeAddresses vp hb a h
  · exact addressFacts_forsRootAddresses vp hb a h
  · exact addressFacts_wotsStepAddresses vp hb a h
  · exact addressFacts_wotsPkAddresses vp hb a h
  · exact addressFacts_xmssNodeAddresses vp hb a h

/-! ## Base-address dependencies of the readers -/

/-- The WOTS+ chain base address depends on its base address only through the layer, the tree and
the key pair. -/
theorem wotsChainAdrs_base (adrs : Adrs) (i : ℕ) :
    wotsChainAdrs adrs i = wotsChainAdrs ⟨adrs.layer, adrs.tree, 0, adrs.word1, 0, 0⟩ i := rfl

/-- The WOTS+ secret-key address depends on its base address only through the layer, the tree and
the key pair. -/
theorem wotsSkAdrs_base (adrs : Adrs) (i : ℕ) :
    wotsSkAdrs adrs i = wotsSkAdrs ⟨adrs.layer, adrs.tree, 0, adrs.word1, 0, 0⟩ i := rfl

/-- The FORS secret-key address depends on its base address only through the layer, the tree and
the key pair. -/
theorem forsSkAdrs_base (adrs : Adrs) (t : ℕ) :
    forsSkAdrs adrs t = forsSkAdrs ⟨adrs.layer, adrs.tree, 0, adrs.word1, 0, 0⟩ t := rfl

section Readers

variable {p : Params} (core : CorePrimitives p) (c : PublicHash.Cache core)
  (secret : Adrs → OracleComp (publicHashSpec core) core.Y) (pk : core.PkSeed)

/-- The XMSS subtree reader depends on its base address only through the layer and the tree. -/
theorem xmssNodeWithSecret?_base (adrs : Adrs) (z t : ℕ) :
    xmssNodeWithSecret? core c secret pk adrs z t =
      xmssNodeWithSecret? core c secret pk ⟨adrs.layer, adrs.tree, 0, 0, 0, 0⟩ z t := rfl

/-- The WOTS+ chain-tops reader depends on its base address only through the layer, the tree and
the key pair. -/
theorem wotsPkGenTopsWithSecret?_base (adrs : Adrs) :
    wotsPkGenTopsWithSecret? core c secret pk adrs =
      wotsPkGenTopsWithSecret? core c secret pk ⟨adrs.layer, adrs.tree, 0, adrs.word1, 0, 0⟩ :=
  rfl

/-- The FORS subtree reader depends on its base address only through the layer, the tree and the
key pair. -/
theorem forsNodeWithSecret?_base (adrs : Adrs) (z t : ℕ) :
    forsNodeWithSecret? core c secret pk adrs z t =
      forsNodeWithSecret? core c secret pk ⟨adrs.layer, adrs.tree, 0, adrs.word1, 0, 0⟩ z t :=
  rfl

end Readers

/-! ## Uniqueness -/

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-- At most one honest input per tweakable-hash key: under key injectivity on the in-range
addresses and the FIPS 205 address widths, two honest entries at one key, for one provider,
public seed and cache, have equal inputs. -/
theorem honestEntry_input_unique (hinj : core.KeyInjective vp)
    (hb : CanonicalAddressBounds vp.params)
    {secret : Adrs → OracleComp (publicHashSpec core) core.Y} {pk : core.PkSeed}
    {c : PublicHash.Cache core} {key : core.AdrsKey} {xs xs' : List core.Y}
    (h : HonestEntry secret pk c (.thash pk key xs))
    (h' : HonestEntry secret pk c (.thash pk key xs')) :
    xs = xs' := by
  generalize hk : key = key' at h'
  revert hk
  cases h <;> cases h' <;> intro hkey <;>
    have heq := hinj (addressFacts_of_mem_constructionAddresses hb (by assumption))
      (addressFacts_of_mem_constructionAddresses hb (by assumption)) hkey <;>
    simp only [xmssNodeAdrs_eq, wotsPkAdrs_eq, wotsChainAdrs_setHashAddress_eq, forsNodeAdrs_eq,
      forsPkAdrs_eq, Adrs.mk.injEq, true_and, and_true] at heq <;>
    try omega
  case xmssNode.xmssNode a z i l r _ _ hl hr a' z' i' l' r' _ _ hl' hr' =>
    obtain ⟨hL, hT, rfl, rfl⟩ := heq
    rw [xmssNodeWithSecret?_base, hL, hT, ← xmssNodeWithSecret?_base] at hl hr
    rw [Option.some.inj (hl.symm.trans hl'), Option.some.inj (hr.symm.trans hr')]
  case wotsPk.wotsPk a tops _ h a' tops' _ h' =>
    obtain ⟨hL, hT, hW⟩ := heq
    rw [wotsPkGenTopsWithSecret?_base, hL, hT, hW, ← wotsPkGenTopsWithSecret?_base] at h
    rw [Option.some.inj (h.symm.trans h')]
  case wotsChain.wotsChain a i t x v _ hx h a' i' t' x' v' _ hx' h' =>
    obtain ⟨hL, hT, hW, rfl, rfl⟩ := heq
    rw [wotsSkAdrs_base, hL, hT, hW, ← wotsSkAdrs_base, hx'] at hx
    rw [wotsChainAdrs_base, hL, hT, hW, ← wotsChainAdrs_base, ← Option.some.inj hx] at h
    rw [Option.some.inj (h.symm.trans h')]
  case forsLeaf.forsLeaf a t x _ hx a' t' x' _ hx' =>
    obtain ⟨hL, hT, hW, rfl⟩ := heq
    rw [forsSkAdrs_base, hL, hT, hW, ← forsSkAdrs_base] at hx
    rw [Option.some.inj (hx.symm.trans hx')]
  case forsNode.forsNode a z i l r _ _ hl hr a' z' i' l' r' _ _ hl' hr' =>
    obtain ⟨hL, hT, hW, rfl, rfl⟩ := heq
    rw [forsNodeWithSecret?_base, hL, hT, hW, ← forsNodeWithSecret?_base] at hl hr
    rw [Option.some.inj (hl.symm.trans hl'), Option.some.inj (hr.symm.trans hr')]
  case forsRoots.forsRoots a roots _ h a' roots' _ h' =>
    obtain ⟨hL, hT, hW⟩ := heq
    congr 1
    ext i hi
    have e := h ⟨i, hi⟩
    rw [forsNodeWithSecret?_base, hL, hT, hW, ← forsNodeWithSecret?_base, h' ⟨i, hi⟩] at e
    exact (Option.some.inj e).symm

/-- At most one honest input per tweakable-hash key, under the key discipline. -/
theorem _root_.SLHDSA.CorePrimitives.KeyDiscipline.honestEntry_input_unique
    (hd : core.KeyDiscipline vp)
    {secret : Adrs → OracleComp (publicHashSpec core) core.Y} {pk : core.PkSeed}
    {c : PublicHash.Cache core} {key : core.AdrsKey} {xs xs' : List core.Y}
    (h : HonestEntry secret pk c (.thash pk key xs))
    (h' : HonestEntry secret pk c (.thash pk key xs')) :
    xs = xs' :=
  Security.honestEntry_input_unique hd.keyInjective hd.canonicalAddressBounds h h'

end Security

end SLHDSA
