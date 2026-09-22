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
* **The non-injectivity does not by itself refute the conclusion.**  Two honest entries the
  encoding identifies carry *different* inputs only if the secret values at the two addresses
  differ, and whether they can is a question about the secret-key function, stated here as
  `ForsLeafSecretsAgreeOn` and `WotsChainSecretsAgreeOn` — two properties, because `HonestInput`
  reads a secret *at the role address itself* in exactly two of its six branches, the `forsLeaf`
  branch through `forsSkAdrs` and the `wotsChain` branch through `wotsSkAdrs`.  Each property is
  relative to a set of addresses, so a bundle answers it once per set.
  `HashSigTest.SLHDSA.RomKeyed` carries the answers: at the two byte-oriented bundles both hold
  with **no restriction at all** — the secret-key function reads the address through exactly the
  map the key uses, and `toBytes_blocks` / `compressSha2_blocks` turn equal serializations into
  equal per-field byte blocks, which is what the role builders keep and hence what the
  derived-address congruences need.  At the principal FIPS SHA-2 bundle both hold **on the
  addresses the checked compression accepts**, where the encoding is injective, and the FORS-leaf
  one holds unrestrictedly as well: key and secret are rejected by the same three conditions, and
  in the mixed case the accepted address's key is `zeroBytes 22`, which forces that address to be
  `Adrs.zero`, whose `type` is `0`.  Unrestrictedly, the **WOTS+-chain one is false** at that
  bundle, because the rejection fallback aliases `Adrs.zero`, whose type code is exactly that
  role's.
* **What the one false cell does and does not show.**  It is a permissiveness of this *model*,
  not a property of SHA-2: the colliding partner `⟨0, 0, 0, 0, 2 ^ 32, 0⟩` is non-canonical and
  its chain index is far outside `len`, so no conformant run reaches it, and
  `HashSig.SLHDSA.Security.EncodedTargets` already excludes it — `AddressFacts` and
  `sha2Domain_of_addressFacts` put every reachable target address inside the accepting domain.
  What admits it is `HonestEntry`, whose addresses are unconstrained by construction.  So the
  conclusion is that `honestEntry_unique` needs canonicality *somewhere*, not that the bundle
  breaks the separator.  The witnesses give two honest entries of one transcript at one encoded
  key with different inputs, conditional on the run's own secret at the all-zero WOTS+
  secret-key address being nonzero; they say nothing about the constant `r` of
  `HashSig.SLHDSA.Security.RomKeyed`, whose theorems quantify the separator over
  `SettledHonest (HonestSeeded …)` and which no lemma here lifts to.
* There are two ways to repair `honestEntry_unique`, and they address different causes.  Carrying
  canonicality into `HonestEntry` addresses the actual cause; whether that restriction breaks
  existing proofs is the decisive question and is not examined here.  Changing `sha2AdrsKey`'s
  rejection fallback to a value outside the compressed image would also remove the false cell,
  and changes no behaviour on the specified domain, but it treats the encoding for a gap that the
  model opened.
* Either repair still needs the rest: that `core.PRF` factors through `core.adrsToKey`, which is
  what the cells above settle bundle by bundle, and that the encoding's kernel is preserved by
  the role builders, plus a height bound for the differing-height case
  (`pow_le_enncard_of_forsNode?` and `pow_le_enncard_of_xmssNode?` of
  `HashSig.SLHDSA.Security.CacheCoverage`).  None of that is done here, and the two properties
  above cover less than the repair needs: they compare secrets only at the role address itself,
  while the other four branches read secrets too, at *nested* addresses — `wotsPkGenTopsWith`
  reads `core.PRF pk sk (wotsSkAdrs adrs i)` for every `i : Fin len`, `xmssLeafWith` descends to
  the same builder, and the two FORS-node branches descend to `forsSkGenCore`.  The four-byte
  truncation applies to every role address, and that is not formalised either.
* `HonestInput` is a predicate of a cache and an address, not of a run.  Nothing here is
  probabilistic and no query budget appears.
* Nothing here is quantum: the cache is a classical table.

## Labels

Twenty-one declarations.

*The role addresses, field by field*: `xmssNodeAdrs_eq`, `wotsPkAdrs_eq`,
`wotsChainAdrs_setHashAddress_eq`, `wotsSkAdrs_eq`, `forsNodeAdrs_eq`, `forsSkAdrs_eq`,
`forsPkAdrs_eq`.

*Block extraction from the two byte-oriented encodings*: `toBytes_blocks`,
`compressSha2_blocks`, `toBytes_forsSkAdrs_congr`, `toBytes_wotsSkAdrs_congr`,
`compressSha2_forsSkAdrs_congr`, `compressSha2_wotsSkAdrs_congr`.

*Equal keys force equal secrets*: `ForsLeafRole`, `WotsChainRole`, `ForsLeafSecretsAgreeOn`,
`WotsChainSecretsAgreeOn`.

*One honest input per role address*: `HonestInput`, `HonestInput.unique`,
`honestInput_of_honestEntry`, `honestEntry_unique`.

## References

- NIST FIPS 205, §4.2 (ADRS), §11.2 (ADRSc compression)
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## The role addresses, field by field -/

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

/-- The FORS secret-key address in full. -/
theorem forsSkAdrs_eq (a : Adrs) (t : ℕ) :
    forsSkAdrs a t = ⟨a.layer, a.tree, 6, a.word1, 0, t⟩ := rfl

/-- The FORS roots address in full. -/
theorem forsPkAdrs_eq (a : Adrs) : forsPkAdrs a = ⟨a.layer, a.tree, 4, a.word1, 0, 0⟩ := rfl

/-! ## Block extraction from the two byte-oriented encodings -/

/-- Equal 32-byte address serializations have equal per-field byte blocks. -/
theorem toBytes_blocks {a b : Adrs} (h : a.toBytes = b.toBytes) :
    Adrs.toBytesBE a.layer 4 = Adrs.toBytesBE b.layer 4 ∧
      Adrs.toBytesBE a.tree 12 = Adrs.toBytesBE b.tree 12 ∧
      Adrs.toBytesBE a.type 4 = Adrs.toBytesBE b.type 4 ∧
      Adrs.toBytesBE a.word1 4 = Adrs.toBytesBE b.word1 4 ∧
      Adrs.toBytesBE a.word2 4 = Adrs.toBytesBE b.word2 4 ∧
      Adrs.toBytesBE a.word3 4 = Adrs.toBytesBE b.word3 4 := by
  simp only [Adrs.toBytes] at h
  obtain ⟨h, h3⟩ := List.append_inj h (by simp)
  obtain ⟨h, h2⟩ := List.append_inj h (by simp)
  obtain ⟨h, h1⟩ := List.append_inj h (by simp)
  obtain ⟨h, hty⟩ := List.append_inj h (by simp)
  obtain ⟨hl, ht⟩ := List.append_inj h (by simp)
  exact ⟨hl, ht, hty, h1, h2, h3⟩

/-- Equal 22-byte `ADRSc` compressions have equal per-field byte blocks. -/
theorem compressSha2_blocks {a b : Adrs} (h : a.compressSha2 = b.compressSha2) :
    Adrs.toBytesBE a.layer 1 = Adrs.toBytesBE b.layer 1 ∧
      Adrs.toBytesBE a.tree 8 = Adrs.toBytesBE b.tree 8 ∧
      Adrs.toBytesBE a.type 1 = Adrs.toBytesBE b.type 1 ∧
      Adrs.toBytesBE a.word1 4 = Adrs.toBytesBE b.word1 4 ∧
      Adrs.toBytesBE a.word2 4 = Adrs.toBytesBE b.word2 4 ∧
      Adrs.toBytesBE a.word3 4 = Adrs.toBytesBE b.word3 4 := by
  simp only [Adrs.compressSha2] at h
  obtain ⟨h, h3⟩ := List.append_inj h (by simp)
  obtain ⟨h, h2⟩ := List.append_inj h (by simp)
  obtain ⟨h, h1⟩ := List.append_inj h (by simp)
  obtain ⟨h, hty⟩ := List.append_inj h (by simp)
  obtain ⟨hl, ht⟩ := List.append_inj h (by simp)
  exact ⟨hl, ht, hty, h1, h2, h3⟩

/-- Two addresses with the same 32-byte serialization have FORS secret-key addresses with the
same 32-byte serialization. -/
theorem toBytes_forsSkAdrs_congr {a b : Adrs} (h : a.toBytes = b.toBytes) :
    (forsSkAdrs a a.word3).toBytes = (forsSkAdrs b b.word3).toBytes := by
  obtain ⟨hl, ht, -, h1, -, h3⟩ := toBytes_blocks h
  simp only [forsSkAdrs_eq, Adrs.toBytes, hl, ht, h1, h3]

/-- Two addresses with the same 32-byte serialization have WOTS+ secret-key addresses with the
same 32-byte serialization. -/
theorem toBytes_wotsSkAdrs_congr {a b : Adrs} (h : a.toBytes = b.toBytes) :
    (wotsSkAdrs a a.word2).toBytes = (wotsSkAdrs b b.word2).toBytes := by
  obtain ⟨hl, ht, -, h1, h2, -⟩ := toBytes_blocks h
  simp only [wotsSkAdrs_eq, Adrs.toBytes, hl, ht, h1, h2]

/-- Two addresses with the same `ADRSc` compression have FORS secret-key addresses with the same
`ADRSc` compression. -/
theorem compressSha2_forsSkAdrs_congr {a b : Adrs} (h : a.compressSha2 = b.compressSha2) :
    (forsSkAdrs a a.word3).compressSha2 = (forsSkAdrs b b.word3).compressSha2 := by
  obtain ⟨hl, ht, -, h1, -, h3⟩ := compressSha2_blocks h
  simp only [forsSkAdrs_eq, Adrs.compressSha2, hl, ht, h1, h3]

/-- Two addresses with the same `ADRSc` compression have WOTS+ secret-key addresses with the same
`ADRSc` compression. -/
theorem compressSha2_wotsSkAdrs_congr {a b : Adrs} (h : a.compressSha2 = b.compressSha2) :
    (wotsSkAdrs a a.word2).compressSha2 = (wotsSkAdrs b b.word2).compressSha2 := by
  obtain ⟨hl, ht, -, h1, h2, -⟩ := compressSha2_blocks h
  simp only [wotsSkAdrs_eq, Adrs.compressSha2, hl, ht, h1, h2]

/-! ## Equal keys force equal secrets -/

/-- The role restriction of the `forsLeaf` branch of `HonestInput`: a `FORS_TREE` address at
height zero. -/
@[expose] def ForsLeafRole (a : Adrs) : Prop := a.type = 3 ∧ a.word2 = 0

/-- The role restriction of the `wotsChain` branch of `HonestInput`: a `WOTS_HASH` address. -/
@[expose] def WotsChainRole (a : Adrs) : Prop := a.type = 0

/-- **The FORS-leaf secret value factors through the address key** on the addresses satisfying
`D`: two addresses in `D` with one address key carry the same FORS secret value at their own
leaf index.  `D = fun _ => True` is the unrestricted form. -/
@[expose] def ForsLeafSecretsAgreeOn {p : Params} (core : CorePrimitives p)
    (D : Adrs → Prop) : Prop :=
  ∀ (pk : core.PkSeed) (sk : core.SkSeed) (a b : Adrs), D a → D b →
    core.adrsToKey a = core.adrsToKey b →
      forsSkGenCore core sk pk a a.word3 = forsSkGenCore core sk pk b b.word3

/-- **The WOTS+ chain secret value factors through the address key** on the addresses satisfying
`D`: two addresses in `D` with one address key carry the same WOTS+ secret value at their own
chain index.  `D = fun _ => True` is the unrestricted form. -/
@[expose] def WotsChainSecretsAgreeOn {p : Params} (core : CorePrimitives p)
    (D : Adrs → Prop) : Prop :=
  ∀ (pk : core.PkSeed) (sk : core.SkSeed) (a b : Adrs), D a → D b →
    core.adrsToKey a = core.adrsToKey b →
      core.PRF pk sk (wotsSkAdrs a a.word2) = core.PRF pk sk (wotsSkAdrs b b.word2)

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
