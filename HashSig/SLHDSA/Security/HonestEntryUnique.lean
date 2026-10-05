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

The honest relation `HonestEntry` ranges every entry over the in-range addresses of the union
ledger, but the oracle is keyed by `core.adrsToKey` of the entry address, not by the address.
Where the key encoding is injective on the in-range addresses (`CorePrimitives.KeyInjective`),
and under the FIPS 205 address widths (`CanonicalAddressBounds`), an oracle key carries at most
one honest input: two honest entries at one `thash` key, for one provider, public seed and cache,
have equal inputs (`HonestEntry.input_unique`).

The argument has three steps.

* Every address of the union ledger `constructionAddresses vp` is in range
  (`addressFacts_of_mem_constructionAddresses`), and each constructor of `HonestEntry` places its
  entry address in that ledger (`HonestEntry.exists_mem_constructionAddresses`), so key
  injectivity makes the two entry addresses equal.
* Equal entry addresses have equal type words, which fixes the constructor: the six entry
  addresses have types `2` (XMSS node), `1` (WOTS+ public key), `0` (WOTS+ chain step), `3` (FORS
  leaf and FORS node) and `4` (FORS roots), and a FORS leaf sits at tree height `0` while a FORS
  node of `HonestEntry` sits at a positive height.  Equal entry addresses of one constructor have
  equal fields.
* The cache readers an honest entry consults depend on the base address only through the fields
  the entry address records: the layer and the tree for the XMSS reader, and in addition the key
  pair for the WOTS+ and FORS readers (`xmssNodeWithSecret?_congr`,
  `wotsPkGenTopsWithSecret?_congr`, `wotsChainAdrs_congr`, `wotsSkAdrs_congr`,
  `forsSkAdrs_congr`, `forsNodeWithSecret?_congr`), so the two entries read the same values and
  their inputs agree.

## Labels

Ten declarations, none private.

*Ledger addresses*: `addressFacts_of_mem_constructionAddresses`,
`HonestEntry.exists_mem_constructionAddresses`.

*Base-address dependencies of the readers*: `xmssNodeWithSecret?_congr`,
`wotsPkGenTopsWithSecret?_congr`, `wotsChainAdrs_congr`, `wotsSkAdrs_congr`, `forsSkAdrs_congr`,
`forsNodeWithSecret?_congr`.

*Uniqueness*: `HonestEntry.input_unique`, `CorePrimitives.KeyDiscipline.honestEntry_input_unique`.

## References

- NIST FIPS 205, §4.2 (ADRS and its type words)
-/

public section

namespace SLHDSA

namespace Security

/-! ## Ledger addresses -/

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

/-- The key of an honest entry is the key of an address of the union ledger. -/
theorem HonestEntry.exists_mem_constructionAddresses {vp : ValidatedParams}
    {core : CorePrimitives vp.params} {secret : Adrs → OracleComp (publicHashSpec core) core.Y}
    {pk : core.PkSeed} {c : PublicHash.Cache core} {key : core.AdrsKey} {xs : List core.Y}
    (h : HonestEntry secret pk c (.thash pk key xs)) :
    ∃ a ∈ constructionAddresses vp, core.adrsToKey a = key := by
  cases h <;> exact ⟨_, by assumption, rfl⟩

/-! ## Base-address dependencies of the readers -/

/-- The WOTS+ chain base address depends on its base address only through the layer, the tree and
the key pair. -/
theorem wotsChainAdrs_congr {a b : Adrs} (hL : a.layer = b.layer) (hT : a.tree = b.tree)
    (hW : a.word1 = b.word1) (i : ℕ) :
    wotsChainAdrs a i = wotsChainAdrs b i :=
  show wotsChainAdrs ⟨a.layer, a.tree, 0, a.word1, 0, 0⟩ i =
    wotsChainAdrs ⟨b.layer, b.tree, 0, b.word1, 0, 0⟩ i by rw [hL, hT, hW]

/-- The WOTS+ secret-key address depends on its base address only through the layer, the tree and
the key pair. -/
theorem wotsSkAdrs_congr {a b : Adrs} (hL : a.layer = b.layer) (hT : a.tree = b.tree)
    (hW : a.word1 = b.word1) (i : ℕ) :
    wotsSkAdrs a i = wotsSkAdrs b i :=
  show wotsSkAdrs ⟨a.layer, a.tree, 0, a.word1, 0, 0⟩ i =
    wotsSkAdrs ⟨b.layer, b.tree, 0, b.word1, 0, 0⟩ i by rw [hL, hT, hW]

/-- The FORS secret-key address depends on its base address only through the layer, the tree and
the key pair. -/
theorem forsSkAdrs_congr {a b : Adrs} (hL : a.layer = b.layer) (hT : a.tree = b.tree)
    (hW : a.word1 = b.word1) (t : ℕ) :
    forsSkAdrs a t = forsSkAdrs b t :=
  show forsSkAdrs ⟨a.layer, a.tree, 0, a.word1, 0, 0⟩ t =
    forsSkAdrs ⟨b.layer, b.tree, 0, b.word1, 0, 0⟩ t by rw [hL, hT, hW]

section Readers

variable {p : Params} {core : CorePrimitives p} {c : PublicHash.Cache core}
  {secret : Adrs → OracleComp (publicHashSpec core) core.Y} {pk : core.PkSeed} {a b : Adrs}

/-- The XMSS subtree reader depends on its base address only through the layer and the tree. -/
theorem xmssNodeWithSecret?_congr (hL : a.layer = b.layer) (hT : a.tree = b.tree) (z t : ℕ) :
    xmssNodeWithSecret? core c secret pk a z t = xmssNodeWithSecret? core c secret pk b z t :=
  show xmssNodeWithSecret? core c secret pk ⟨a.layer, a.tree, 0, 0, 0, 0⟩ z t =
    xmssNodeWithSecret? core c secret pk ⟨b.layer, b.tree, 0, 0, 0, 0⟩ z t by rw [hL, hT]

/-- The WOTS+ chain-tops reader depends on its base address only through the layer, the tree and
the key pair. -/
theorem wotsPkGenTopsWithSecret?_congr (hL : a.layer = b.layer) (hT : a.tree = b.tree)
    (hW : a.word1 = b.word1) :
    wotsPkGenTopsWithSecret? core c secret pk a = wotsPkGenTopsWithSecret? core c secret pk b :=
  show wotsPkGenTopsWithSecret? core c secret pk ⟨a.layer, a.tree, 0, a.word1, 0, 0⟩ =
    wotsPkGenTopsWithSecret? core c secret pk ⟨b.layer, b.tree, 0, b.word1, 0, 0⟩ by
    rw [hL, hT, hW]

/-- The FORS subtree reader depends on its base address only through the layer, the tree and the
key pair. -/
theorem forsNodeWithSecret?_congr (hL : a.layer = b.layer) (hT : a.tree = b.tree)
    (hW : a.word1 = b.word1) (z t : ℕ) :
    forsNodeWithSecret? core c secret pk a z t = forsNodeWithSecret? core c secret pk b z t :=
  show forsNodeWithSecret? core c secret pk ⟨a.layer, a.tree, 0, a.word1, 0, 0⟩ z t =
    forsNodeWithSecret? core c secret pk ⟨b.layer, b.tree, 0, b.word1, 0, 0⟩ z t by
    rw [hL, hT, hW]

end Readers

/-! ## Uniqueness -/

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-- At most one honest input per tweakable-hash key: under key injectivity on the in-range
addresses and the FIPS 205 address widths, two honest entries at one key, for one provider,
public seed and cache, have equal inputs. -/
theorem HonestEntry.input_unique (hinj : core.KeyInjective vp)
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
    rw [xmssNodeWithSecret?_congr hL hT] at hl hr
    rw [Option.some.inj (hl.symm.trans hl'), Option.some.inj (hr.symm.trans hr')]
  case wotsPk.wotsPk a tops _ h a' tops' _ h' =>
    obtain ⟨hL, hT, hW⟩ := heq
    rw [wotsPkGenTopsWithSecret?_congr hL hT hW] at h
    rw [Option.some.inj (h.symm.trans h')]
  case wotsChain.wotsChain a i t x v _ hx h a' i' t' x' v' _ hx' h' =>
    obtain ⟨hL, hT, hW, rfl, rfl⟩ := heq
    rw [wotsSkAdrs_congr hL hT hW, hx'] at hx
    rw [wotsChainAdrs_congr hL hT hW, ← Option.some.inj hx] at h
    rw [Option.some.inj (h.symm.trans h')]
  case forsLeaf.forsLeaf a t x _ hx a' t' x' _ hx' =>
    obtain ⟨hL, hT, hW, rfl⟩ := heq
    rw [forsSkAdrs_congr hL hT hW] at hx
    rw [Option.some.inj (hx.symm.trans hx')]
  case forsNode.forsNode a z i l r _ _ hl hr a' z' i' l' r' _ _ hl' hr' =>
    obtain ⟨hL, hT, hW, rfl, rfl⟩ := heq
    rw [forsNodeWithSecret?_congr hL hT hW] at hl hr
    rw [Option.some.inj (hl.symm.trans hl'), Option.some.inj (hr.symm.trans hr')]
  case forsRoots.forsRoots a roots _ h a' roots' _ h' =>
    obtain ⟨hL, hT, hW⟩ := heq
    congr 1
    ext i hi
    exact Option.some.inj
      (((h ⟨i, hi⟩).symm.trans (forsNodeWithSecret?_congr hL hT hW _ _)).trans (h' ⟨i, hi⟩))

/-- At most one honest input per tweakable-hash key, under the key discipline. -/
theorem _root_.SLHDSA.CorePrimitives.KeyDiscipline.honestEntry_input_unique
    (hd : core.KeyDiscipline vp)
    {secret : Adrs → OracleComp (publicHashSpec core) core.Y} {pk : core.PkSeed}
    {c : PublicHash.Cache core} {key : core.AdrsKey} {xs xs' : List core.Y}
    (h : HonestEntry secret pk c (.thash pk key xs))
    (h' : HonestEntry secret pk c (.thash pk key xs')) :
    xs = xs' :=
  h.input_unique hd.keyInjective hd.canonicalAddressBounds h'

end Security

end SLHDSA
