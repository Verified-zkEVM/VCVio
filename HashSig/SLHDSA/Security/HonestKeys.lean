/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomDescent

/-!
# One honest input per role address

`HashSig.SLHDSA.Security.RomDescent`'s `HonestEntry` has six constructors, one per role of the
tweakable hash in SLH-DSA: an XMSS node, a WOTS+ public key, a WOTS+ chain value, a FORS leaf
secret, a FORS node, the FORS roots.  Each constructor's `thash` key is the encoding of a *role
address* built from a base address, and the six builders put pairwise distinguishable values in
the `type` field (tree 2, wotsPk 1, wotsHash 0, forsTree 3, forsRoots 4) and, for the two
`forsTree` roles, in `word2` (a node has positive height, a leaf has height `0`).  Six `rfl`
identities record those fields.

`HonestInput` collects the six readings *at the role address itself*, which the reader
congruences of `HashSig.SLHDSA.Security.CacheReaders` licence because every builder preserves
exactly the base-address fields its role's reading consumes.  It is therefore a predicate of the
role address alone, and `HonestInput.unique` says a role address carries at most one honest input
list.  `honestInput_of_honestEntry` factors every honest entry through it, and
`honestEntry_unique` concludes that a `thash` key carries at most one honest input — the
separator hypothesis of `HashSig.SLHDSA.Security.RomKeyed` at `r = 1` — **from an injectivity
hypothesis on the address encoding that no shipped tweak map satisfies**.

## Scope

* **`Function.Injective core.adrsToKey` is false for every shipped tweak map.**  `Adrs`' six
  fields are naturals while every encoding writes each into four bytes, so `⟨0, 0, 3, 0, 0, 0⟩`
  and `⟨0, 0, 3, 0, 0, 2 ^ 32⟩` share a key under `Adrs.toBytes`/`Adrs.toVector` (the SHAKE map)
  and under `Adrs.compressSha2` (the compatibility bundle's map); the FIPS SHA-2 map collapses
  every address its checked compression rejects onto one zero key.
  `HashSigTest.SLHDSA.RomKeyed` computes all three collisions at the field each bundle installs.
  `honestEntry_unique` is correct and its hypothesis is what is missing; the *unrestricted* form
  assumed here is discharged nowhere in the repository, while the *in-range* form is —
  `forsLeafAdrsKey_injective`, `forsTreeAdrsKey_injective` and `forsRootAdrsKey_injective` of
  `HashSig.SLHDSA.Security.ForsWitnesses` prove per-role injectivity of the encoded address on
  coordinates in range under `EncodedTargetLedgerConditions`, discharged per profile by
  `approvedEncodedTargetLedgerConditions`, and every collision witness uses out-of-range indices,
  which those lemmas exclude.  The repository never claims the unrestricted form:
  `Adrs.compressSha2_injective_of_fits` carries twelve range hypotheses.
* **The non-injectivity does not by itself refute the conclusion.**  The two honest entries the
  encoding identifies carry *different* inputs only if the two FORS leaf secrets differ, and at
  every shipped bundle they are provably **equal**: the secret-key function factors through the
  very encoding that caused the key collision — the two byte-oriented bundles hash the same
  truncated encoding, and at the principal FIPS SHA-2 bundle both addresses of the exhibited pair
  are rejected by the checked compression and collapse to the same zero value
  (`forsSkGenCore_shake_eq`, `forsSkGenCore_sha_eq`, `forsSkGenCore_sha2_eq` of
  `HashSigTest.SLHDSA.RomKeyed`).  What remains genuinely open is only whether some *other* key
  collision separates the secret-key function.
* The repair replaces injectivity by two weaker hypotheses — that `core.PRF` factors through
  `core.adrsToKey`, and that the encoding's kernel is preserved by the role builders — plus a
  height-bound lemma for the differing-height case.  None of that is done here, but the first is
  close to free at each concrete core, the factorization being exactly what the three
  computations above exhibit.
* `HonestInput` is a predicate of a cache and an address, not of a run.  Nothing here is
  probabilistic and no query budget appears.
* Nothing here is quantum: the cache is a classical table.

## Labels

Ten declarations.

*The six role addresses, field by field*: `xmssNodeAdrs_eq`, `wotsPkAdrs_eq`,
`wotsChainAdrs_setHashAddress_eq`, `wotsSkAdrs_eq`, `forsNodeAdrs_eq`, `forsPkAdrs_eq`.

*One honest input per role address*: `HonestInput`, `HonestInput.unique`,
`honestInput_of_honestEntry`, `honestEntry_unique`.

## References

- NIST FIPS 205, §4.2 (ADRS), §11.2 (ADRSc compression)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## The six role addresses, field by field -/

/-- The XMSS node address in full. -/
theorem xmssNodeAdrs_eq (a : Adrs) (z t : ℕ) :
    xmssNodeAdrs a z t = ⟨a.layer, a.tree, 2, 0, z, t⟩ := rfl

/-- The WOTS+ public-key address in full. -/
theorem wotsPkAdrs_eq (a : Adrs) : wotsPkAdrs a = ⟨a.layer, a.tree, 1, a.word1, 0, 0⟩ := rfl

/-- The WOTS+ chain address at one hash address in full. -/
theorem wotsChainAdrs_setHashAddress_eq (a : Adrs) (i t : ℕ) :
    (wotsChainAdrs a i).setHashAddress t = ⟨a.layer, a.tree, 0, a.word1, i, t⟩ := rfl

/-- The WOTS+ secret-key address in full. -/
theorem wotsSkAdrs_eq (a : Adrs) (i : ℕ) :
    wotsSkAdrs a i = ⟨a.layer, a.tree, 5, a.word1, i, 0⟩ := rfl

/-- The FORS node address in full; height `0` is a FORS leaf. -/
theorem forsNodeAdrs_eq (a : Adrs) (z t : ℕ) :
    forsNodeAdrs a z t = ⟨a.layer, a.tree, 3, a.word1, z, t⟩ := rfl

/-- The FORS roots address in full. -/
theorem forsPkAdrs_eq (a : Adrs) : forsPkAdrs a = ⟨a.layer, a.tree, 4, a.word1, 0, 0⟩ := rfl

/-! ## One honest input per role address -/

/-- The honest input list at a *role address*: `a.type` selects the role, `a.word1` the key pair,
and `a.word2`/`a.word3` the role's height and index, with every honest reading taken at `a`
itself.  A function of the role address alone. -/
def HonestInput (o : RomOutcome vp core) (c : PublicHash.Cache core) (a : Adrs)
    (xs : List core.Y) : Prop :=
  (a.type = 2 ∧ 0 < a.word2 ∧ ∃ l r, xs = [l, r] ∧
      xmssNode? core c o.sk.skSeed o.pk.pkSeed a (a.word2 - 1) (2 * a.word3) = some l ∧
      xmssNode? core c o.sk.skSeed o.pk.pkSeed a (a.word2 - 1) (2 * a.word3 + 1) = some r) ∨
  (a.type = 1 ∧ ∃ tops : Vector core.Y vp.params.len, xs = tops.toList ∧
      wotsPkGenTops? core c o.sk.skSeed o.pk.pkSeed a = some tops) ∨
  (a.type = 0 ∧ ∃ v, xs = [v] ∧ chain? core c o.pk.pkSeed (wotsChainAdrs a a.word2)
      (core.PRF o.pk.pkSeed o.sk.skSeed (wotsSkAdrs a a.word2)) 0 a.word3 = some v) ∨
  (a.type = 3 ∧ 0 < a.word2 ∧ ∃ l r, xs = [l, r] ∧
      forsNode? core c o.sk.skSeed o.pk.pkSeed a (a.word2 - 1) (2 * a.word3) = some l ∧
      forsNode? core c o.sk.skSeed o.pk.pkSeed a (a.word2 - 1) (2 * a.word3 + 1) = some r) ∨
  (a.type = 3 ∧ a.word2 = 0 ∧
      xs = [forsSkGenCore core o.sk.skSeed o.pk.pkSeed a a.word3]) ∨
  (a.type = 4 ∧ ∃ roots : Vector core.Y vp.params.k, xs = roots.toList ∧
      ∀ i : Fin vp.params.k,
        forsNode? core c o.sk.skSeed o.pk.pkSeed a vp.params.a i.val = some roots[i])

/-- **At most one honest input list per role address.** -/
theorem HonestInput.unique {o : RomOutcome vp core} {c : PublicHash.Cache core} {a : Adrs}
    {xs ys : List core.Y} (hx : HonestInput o c a xs) (hy : HonestInput o c a ys) :
    xs = ys := by
  rcases hx with ⟨h, hw, l, r, rfl, hl, hr⟩ | ⟨h, tops, rfl, ht⟩ | ⟨h, v, rfl, hv⟩ |
      ⟨h, hw, l, r, rfl, hl, hr⟩ | ⟨h, hw, rfl⟩ | ⟨h, roots, rfl, hro⟩ <;>
    rcases hy with ⟨h', hw', l', r', rfl, hl', hr'⟩ | ⟨h', tops', rfl, ht'⟩ |
        ⟨h', v', rfl, hv'⟩ | ⟨h', hw', l', r', rfl, hl', hr'⟩ | ⟨h', hw', rfl⟩ |
        ⟨h', roots', rfl, hro'⟩ <;>
    first
      | omega
      | rw [Option.some_inj.mp (hl.symm.trans hl'), Option.some_inj.mp (hr.symm.trans hr')]
      | rw [Option.some_inj.mp (ht.symm.trans ht')]
      | rw [Option.some_inj.mp (hv.symm.trans hv')]
      | rfl
      | (congr 1
         ext i hi
         exact Option.some_inj.mp ((hro ⟨i, hi⟩).symm.trans (hro' ⟨i, hi⟩)))

/-- **Every honest entry is an honest input at its own role address.** -/
theorem honestInput_of_honestEntry {o : RomOutcome vp core} {c : PublicHash.Cache core}
    {p : core.PkSeed} {k : core.AdrsKey} {xs : List core.Y}
    (h : HonestEntry o c (.thash p k xs)) :
    ∃ a : Adrs, k = core.adrsToKey a ∧ HonestInput o c a xs := by
  cases h with
  | xmssNode adrs hgt i l r hh hl hr =>
    exact ⟨xmssNodeAdrs adrs hgt i, rfl, Or.inl ⟨rfl, hh, l, r, rfl,
      (xmssNode?_congr core c _ _ rfl rfl _ _).trans hl,
      (xmssNode?_congr core c _ _ rfl rfl _ _).trans hr⟩⟩
  | wotsPk adrs tops ht =>
    exact ⟨wotsPkAdrs adrs, rfl, Or.inr (Or.inl ⟨rfl, tops, rfl,
      (wotsPkGenTops?_congr core c _ _ rfl rfl rfl).trans ht⟩)⟩
  | wotsChain adrs i steps v hv =>
    exact ⟨(wotsChainAdrs adrs i).setHashAddress steps, rfl,
      Or.inr (Or.inr (Or.inl ⟨rfl, v, rfl, hv⟩))⟩
  | forsLeaf adrs leaf =>
    exact ⟨forsNodeAdrs adrs 0 leaf, rfl,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))⟩
  | forsNode adrs hgt i l r hh hl hr =>
    exact ⟨forsNodeAdrs adrs hgt i, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hh, l, r, rfl,
      (forsNode?_congr core c _ _ rfl rfl rfl _ _).trans hl,
      (forsNode?_congr core c _ _ rfl rfl rfl _ _).trans hr⟩)))⟩
  | forsRoots adrs roots hr =>
    exact ⟨forsPkAdrs adrs, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, roots, rfl,
      fun i => (forsNode?_congr core c _ _ rfl rfl rfl _ _).trans (hr i)⟩))))⟩

/-- **A `thash` key carries at most one honest input**, under an injective address encoding.
The hypothesis is *false* for every shipped tweak map — each writes the address fields into four
bytes apiece, while `Adrs`' fields are naturals — so this theorem is not instantiable at any of
them; `HashSigTest.SLHDSA.RomKeyed` carries the computations that refute it. -/
theorem honestEntry_unique (hinj : Function.Injective core.adrsToKey)
    {o : RomOutcome vp core} {c : PublicHash.Cache core} {p : core.PkSeed} {k : core.AdrsKey}
    {xs ys : List core.Y} (hx : HonestEntry o c (.thash p k xs))
    (hy : HonestEntry o c (.thash p k ys)) : xs = ys := by
  obtain ⟨a, hka, hIa⟩ := honestInput_of_honestEntry hx
  obtain ⟨b, hkb, hIb⟩ := honestInput_of_honestEntry hy
  obtain rfl : a = b := hinj (hka.symm.trans hkb)
  exact hIa.unique hIb

end SLHDSA.Security
