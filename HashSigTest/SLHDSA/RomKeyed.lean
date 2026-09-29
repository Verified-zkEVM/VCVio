/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomKeyed
public import HashSig.SLHDSA.Security.AddressKeys
public import HashSig.SLHDSA.Security.EncodedTargets
public import HashSig.SLHDSA.ForsConformance
public import HashSig.SLHDSA.XmssConformance
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Concrete.Instance

/-!
# SLH-DSA address-encoding witnesses

Computations at the three shipped primitive bundles about the address encoding `core.adrsToKey`
that keys the tweakable-hash oracle: where it is not injective, where the bundles' secret-key
functions nevertheless agree across a key collision, the checked domain of the FIPS SHA-2
compression, and the leaf-index range of a subtree.  They are the concrete
facts a separator for the key-weighted collision bound of `HashSig.SLHDSA.Security.RomKeyed` is
checked against.

## The address encoding is not injective at any shipped bundle

`SLHDSA.Adrs` has six natural-number fields; every encoding writes each of them into four bytes.
So `⟨0, 0, 3, 0, 0, 0⟩` and `⟨0, 0, 3, 0, 0, 2 ^ 32⟩` — two FORS leaf addresses of one tree,
differing only in the leaf index — have the same 32-byte serialization (`toBytes_collision`) and
the same 22-byte `ADRSc` compression (`compressSha2_collision`).  The FIPS SHA-2 tweak map
`SLHDSA.Concrete.sha2AdrsKey` routes through the *checked* compression instead, and is
non-injective for a different reason: it maps every address it rejects to the same zero key
(`sha2AdrsKey_toList_collision`).  Hence `not_injective_adrsToKey_shake`,
`not_injective_adrsToKey_sha` and `not_injective_adrsToKey_sha2`, stated at the field each bundle
installs, with the carrier-level `not_injective_toBytes`, `not_injective_compressSha2` and
`not_injective_sha2AdrsKey` underneath.  `SLHDSA.Adrs.compressSha2_injective_of_fits` carries
twelve range hypotheses.

## The secret-key function agrees across the exhibited collision

At every shipped bundle the two FORS leaf secrets of that pair are equal, because the secret-key
function reads the address through the same encoding that collides.

* SHAKE: `shakePRF` reads the address only through `SLHDSA.Adrs.toBytes` (`shakePRF_congr`), and
  the two FORS secret-key addresses share it (`forsSkAdrs_toBytes_collision`), so the secrets
  coincide (`forsSkGenCore_shake_eq`).
* The compatibility bundle: `shaPRF` reads the address only through `SLHDSA.Adrs.compressSha2`
  (`shaPRF_congr`), and the pair shares it (`forsSkAdrs_compressSha2_collision`), so the secrets
  coincide (`forsSkGenCore_sha_eq`).
* FIPS SHA-2: both addresses of a pair of out-of-range leaf indices are rejected by
  `SLHDSA.Concrete.Sha2Address.ofAdrs` (`forsSkAdrs_isCanonical_eq_false`), so the checked `PRF`
  falls back to the zero value at both (`forsSkGenCore_sha2_eq`).

## The FIPS SHA-2 checked domain

`SLHDSA.Concrete.sha2AdrsKey` and the checked `PRF` reject on the same conditions
(`sha2AdrsKey_eq_zero_of_not_sha2Domain`, `prf_eq_zero_of_not_sha2Domain`), a key equal to the
zero key on the domain forces the all-zero address (`eq_zero_of_key_eq_zeroBytes`), and the
encoding is injective on the domain (`injOn_adrsToKey_sha2`).  A `FORS_TREE` role address and its
secret-key address lie in the domain together (`sha2Domain_forsSkAdrs_iff`), and so do the FORS
node and zero-step WOTS+ chain addresses of a base address in the domain
(`sha2Domain_forsNodeAdrs`, `sha2Domain_wotsChainStepZero`).

Outside the domain the zero-key fallback aliases `SLHDSA.Adrs.zero`, a `WOTS_HASH` address:
`⟨0, 0, 0, 0, 0, 0⟩` (accepted, `zero_isCanonical`) and `⟨0, 0, 0, 0, 2 ^ 32, 0⟩` (rejected,
`outOfRange_isCanonical`, `not_sha2Domain_outOfRange`) share a key
(`sha2AdrsKey_wots_collision`) while their WOTS+ secret-key addresses do not
(`sha2AdrsKey_wotsSk_ne`), and the second takes the zero fallback
(`sha2_prf_wotsSk_out_of_range`).  The same pair also collides under the SHAKE encoding
(`shake_wots_collision`).  Its chain index is far outside `len`, so no conformant run reaches it.

At the two byte-oriented bundles, two role addresses with equal keys have secret-key addresses
(at each role's own index) with equal keys (`SLHDSA.Security.toBytes_wotsSkAdrs_congr` and its
companions in `HashSig.SLHDSA.Security.AddressKeys`).  At FIPS SHA-2 that implication fails
(`sha2AdrsKey_wots_collision`, `sha2AdrsKey_wotsSk_ne`), so a separator bound of `1` there needs
the checked-domain restriction or a change to the zero-key fallback.

## The leaf-index range of a subtree

Every global leaf index under the subtree at height `z` and index `t` fits a four-byte field once
the subtree's own index range does (`fits_four_of_mem_leafRange`), which keeps the FORS node and
WOTS+ chain addresses of a checked-domain base address inside the checked domain.

Every statement is a `Prop` about an address encoding, so the file has
no `main` and is built by the `HashSigTest` library glob alone.
-/

public section

namespace SLHDSA.RomKeyedTest

open Security Concrete OracleComp OracleSpec

/-! ## The address encoding is not injective at any shipped bundle -/

/-- Two FORS leaf addresses differing only by `2 ^ 32` in the leaf index have the same 32-byte
serialization. -/
theorem toBytes_collision :
    Adrs.toBytes ⟨0, 0, 3, 0, 0, 0⟩ = Adrs.toBytes ⟨0, 0, 3, 0, 0, 2 ^ 32⟩ := by decide

/-- The same two addresses have the same 22-byte `ADRSc` compression. -/
theorem compressSha2_collision :
    Adrs.compressSha2 ⟨0, 0, 3, 0, 0, 0⟩ = Adrs.compressSha2 ⟨0, 0, 3, 0, 0, 2 ^ 32⟩ := by decide

/-- The FIPS SHA-2 tweak map sends every address the checked compression rejects to one zero
key. -/
theorem sha2AdrsKey_toList_collision : (sha2AdrsKey ⟨0, 0, 3, 0, 0, 2 ^ 32⟩).toList =
    (sha2AdrsKey ⟨0, 0, 3, 0, 0, 2 ^ 32 + 1⟩).toList := by decide

/-- The 32-byte address serialization is not injective. -/
theorem not_injective_toBytes : ¬ Function.Injective Adrs.toBytes :=
  fun h => absurd (h toBytes_collision) (by decide)

/-- The 22-byte `ADRSc` compression is not injective. -/
theorem not_injective_compressSha2 : ¬ Function.Injective Adrs.compressSha2 :=
  fun h => absurd (h compressSha2_collision) (by decide)

/-- The FIPS SHA-2 tweak map is not injective. -/
theorem not_injective_sha2AdrsKey : ¬ Function.Injective sha2AdrsKey :=
  fun h => absurd (h (Vector.toList_inj.mp sha2AdrsKey_toList_collision)) (by decide)

/-- The tweak map the SHAKE bundle installs is not injective. -/
theorem not_injective_adrsToKey_shake (p : Params) :
    ¬ Function.Injective (shakePrimitives p).adrsToKey := fun h =>
  absurd (h (show Adrs.toVector _ = Adrs.toVector _ from
    Vector.toList_inj.mp (by simpa [Adrs.toVector] using toBytes_collision))) (by decide)

/-- The tweak map the compatibility bundle installs is not injective. -/
theorem not_injective_adrsToKey_sha : ¬ Function.Injective shaPrimitives.adrsToKey := fun h =>
  absurd (h (show shaAdrsKey _ = shaAdrsKey _ from
    Vector.toList_inj.mp (by simpa using compressSha2_collision))) (by decide)

/-- The tweak map the FIPS SHA-2 bundle installs is not injective. -/
theorem not_injective_adrsToKey_sha2 (p : Params) :
    ¬ Function.Injective (sha2Primitives p).adrsToKey := fun h =>
  absurd (h (show sha2AdrsKey _ = sha2AdrsKey _ from
    Vector.toList_inj.mp sha2AdrsKey_toList_collision)) (by decide)

/-! ## The secret-key function agrees across the exhibited collision -/

/-- The SHAKE `PRF` reads the address only through `SLHDSA.Adrs.toBytes`. -/
theorem shakePRF_congr {n : ℕ} (pkSeed skSeed : Bytes n) {a b : Adrs}
    (h : a.toBytes = b.toBytes) : shakePRF pkSeed skSeed a = shakePRF pkSeed skSeed b := by
  simp only [shakePRF, shakeAddress, h]

/-- The compatibility bundle's `PRF` reads the address only through
`SLHDSA.Adrs.compressSha2`. -/
theorem shaPRF_congr (pkSeed skSeed : Bytes 16) {a b : Adrs}
    (h : a.compressSha2 = b.compressSha2) : shaPRF pkSeed skSeed a = shaPRF pkSeed skSeed b := by
  simp only [shaPRF, thashPrefix, h]

/-- The two FORS secret-key addresses of the collision witness have the same serialization. -/
theorem forsSkAdrs_toBytes_collision :
    (forsSkAdrs ⟨0, 0, 3, 0, 0, 0⟩ 0).toBytes
      = (forsSkAdrs ⟨0, 0, 3, 0, 0, 0⟩ (2 ^ 32)).toBytes := by decide

/-- The two FORS secret-key addresses of the collision witness have the same compression. -/
theorem forsSkAdrs_compressSha2_collision :
    (forsSkAdrs ⟨0, 0, 3, 0, 0, 0⟩ 0).compressSha2
      = (forsSkAdrs ⟨0, 0, 3, 0, 0, 0⟩ (2 ^ 32)).compressSha2 := by decide

/-- **At the SHAKE bundle the two FORS leaf secrets of the collision witness are equal.** -/
theorem forsSkGenCore_shake_eq (p : Params) (sk pk : Bytes p.n) :
    forsSkGenCore (shakePrimitives p).core sk pk ⟨0, 0, 3, 0, 0, 0⟩ 0 =
      forsSkGenCore (shakePrimitives p).core sk pk ⟨0, 0, 3, 0, 0, 0⟩ (2 ^ 32) :=
  shakePRF_congr pk sk forsSkAdrs_toBytes_collision

/-- **At the compatibility bundle the two FORS leaf secrets of the collision witness are
equal.** -/
theorem forsSkGenCore_sha_eq (sk pk : Bytes 16) :
    forsSkGenCore shaPrimitives.core sk pk ⟨0, 0, 3, 0, 0, 0⟩ 0 =
      forsSkGenCore shaPrimitives.core sk pk ⟨0, 0, 3, 0, 0, 0⟩ (2 ^ 32) :=
  shaPRF_congr pk sk forsSkAdrs_compressSha2_collision

/-- A FORS secret-key address at an out-of-range leaf index is non-canonical. -/
theorem forsSkAdrs_isCanonical_eq_false (t : ℕ) (h : Adrs.Fits 4 (2 ^ 32 + t) = false) :
    (forsSkAdrs ⟨0, 0, 3, 0, 0, 0⟩ (2 ^ 32 + t)).isCanonical = false := by
  simp only [forsSkAdrs, Adrs.isCanonical, Adrs.setTreeIndex, Adrs.setKeyPairAddress,
    Adrs.setTypeAndClear, Adrs.getKeyPairAddress, h]
  simp

/-- **At the FIPS SHA-2 bundle the two FORS leaf secrets of the collision witness are equal**:
the checked `PRF` rejects both non-canonical addresses and falls back to the zero value. -/
theorem forsSkGenCore_sha2_eq (p : Params) (sk pk : Bytes p.n) :
    forsSkGenCore (sha2Primitives p).core sk pk ⟨0, 0, 3, 0, 0, 0⟩ (2 ^ 32) =
      forsSkGenCore (sha2Primitives p).core sk pk ⟨0, 0, 3, 0, 0, 0⟩ (2 ^ 32 + 1) := by
  have h0 := forsSkAdrs_isCanonical_eq_false 0 (by decide)
  have h1 := forsSkAdrs_isCanonical_eq_false 1 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [forsSkGenCore, sha2Primitives, sha2PRFChecked,
    Sha2Address.ofAdrs, h0, h1, checkedNodeOrZero]
  simp

/-! ## The FIPS SHA-2 checked-compression domain -/

/-- Outside the checked domain the FIPS SHA-2 tweak map takes its zero fallback. -/
theorem sha2AdrsKey_eq_zero_of_not_sha2Domain {a : Adrs} (h : ¬ Sha2Domain a) :
    sha2AdrsKey a = zeroBytes 22 := by
  unfold Sha2Domain at h
  simp only [sha2AdrsKey, Adrs.compressSha2Checked]
  by_cases hc : a.isCanonical = true
  · by_cases hl : Adrs.Fits 1 a.layer = true
    · have ht : Adrs.Fits 8 a.tree ≠ true := fun ht => h ⟨hc, hl, ht⟩
      simp [hc, hl, Bool.eq_false_iff.2 ht]
    · simp [hc, Bool.eq_false_iff.2 hl]
  · simp [Bool.eq_false_iff.2 hc]

/-- Outside the checked domain the FIPS SHA-2 secret-key function takes its zero fallback: it
rejects on exactly the conditions the tweak map rejects on. -/
theorem prf_eq_zero_of_not_sha2Domain {p : Params} (pk sk : Bytes p.n) {a : Adrs}
    (h : ¬ Sha2Domain a) : (sha2Primitives p).core.PRF pk sk a = zeroBytes p.n := by
  unfold Sha2Domain at h
  simp only [sha2Primitives, sha2PRFChecked, Sha2Address.ofAdrs]
  by_cases hc : a.isCanonical = true
  · by_cases hl : Adrs.Fits 1 a.layer = true
    · have ht : Adrs.Fits 8 a.tree ≠ true := fun ht => h ⟨hc, hl, ht⟩
      simp [hc, hl, ht, checkedNodeOrZero]
    · simp [hc, hl, checkedNodeOrZero]
  · simp [hc, checkedNodeOrZero]

/-- The zero key of the FIPS SHA-2 fallback is also the genuine `ADRSc` of exactly one
checked-domain address: the all-zero `WOTS_HASH` address. -/
theorem eq_zero_of_key_eq_zeroBytes {a : Adrs} (h : Sha2Domain a)
    (hk : sha2AdrsKey a = zeroBytes 22) : a = Adrs.zero := by
  rw [sha2AdrsKey_eq_compressed a h.1 h.2.1 h.2.2] at hk
  have hbytes : a.compressSha2 = List.replicate 22 0 := by
    simpa [zeroBytes] using congrArg Vector.toList hk
  have := Adrs.fromCompressedSha2_compressSha2 a h.2.1 h.2.2
    (Adrs.fits_one_type_of_isCanonical h.1) (Adrs.fits_of_isCanonical a h.1).2.2.2.1
    (Adrs.fits_of_isCanonical a h.1).2.2.2.2.1 (Adrs.fits_of_isCanonical a h.1).2.2.2.2.2
  rw [hbytes] at this
  rw [← this]
  decide

/-- A `FORS_TREE` role address and its FORS secret-key address are in the checked domain
together. -/
theorem sha2Domain_forsSkAdrs_iff {a : Adrs} (hat : a.type = 3) (haw : a.word2 = 0) :
    Sha2Domain (forsSkAdrs a a.word3) ↔ Sha2Domain a := by
  simp only [Sha2Domain, forsSkAdrs_eq, Adrs.isCanonical, hat, haw, AddrType.ofCode,
    Bool.and_eq_true, Option.isSome_some, show Adrs.Fits 4 6 = true from by decide,
    show Adrs.Fits 4 3 = true from by decide, show Adrs.Fits 4 0 = true from by decide,
    decide_true, and_true, and_assoc]

/-- The address encoding of the FIPS SHA-2 bundle is injective on the checked domain. -/
theorem injOn_adrsToKey_sha2 (p : Params) :
    Set.InjOn (sha2Primitives p).core.adrsToKey {a | Sha2Domain a} := by
  intro a ha b hb h
  replace h : sha2AdrsKey a = sha2AdrsKey b := h
  exact sha2AdrsKey_injective_of_domain ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2 h

/-! ## Reachable role addresses are in the checked domain -/

/-- A FORS node address of a checked-domain base address is in the checked domain once its height
and index fit their four-byte fields.  Both extra conditions of the domain read only the layer
and tree fields, which the builder preserves. -/
theorem sha2Domain_forsNodeAdrs {adrs : Adrs} (hbase : Sha2Domain adrs) {z t : ℕ}
    (hz : Adrs.Fits 4 z = true) (ht : Adrs.Fits 4 t = true) :
    Sha2Domain (forsNodeAdrs adrs z t) :=
  ⟨ForsConformance.forsNodeAdrs_isCanonical adrs z t hbase.1 hz ht, hbase.2.1, hbase.2.2⟩

/-- The chain-step-zero address of XMSS leaf `i` under a checked-domain base address is in the
checked domain once `i` fits its four-byte field. -/
theorem sha2Domain_wotsChainStepZero {adrs : Adrs} (hbase : Sha2Domain adrs) {i : ℕ}
    (hi : Adrs.Fits 4 i = true) :
    Sha2Domain ((wotsChainAdrs (wotsLeafAdrs adrs i) 0).setHashAddress 0) :=
  ⟨wotsChainHashAdrs_isCanonical _ 0 0
      (XmssConformance.wotsLeafAdrs_isCanonical adrs i hbase.1 hi) (by decide) (by decide),
    hbase.2.1, hbase.2.2⟩

/-! ## The one collision the checked domain does not cover -/

/-- The all-zero `WOTS_HASH` address and the same address with an out-of-range chain index share
the FIPS SHA-2 key: the second is rejected and collapses onto the first's genuine `ADRSc`. -/
theorem sha2AdrsKey_wots_collision :
    sha2AdrsKey ⟨0, 0, 0, 0, 0, 0⟩ = sha2AdrsKey ⟨0, 0, 0, 0, 2 ^ 32, 0⟩ :=
  Vector.toList_inj.mp (by decide)

/-- Their two WOTS+ secret-key addresses do not share it. -/
theorem sha2AdrsKey_wotsSk_ne :
    sha2AdrsKey (wotsSkAdrs ⟨0, 0, 0, 0, 0, 0⟩ 0) ≠
      sha2AdrsKey (wotsSkAdrs ⟨0, 0, 0, 0, 2 ^ 32, 0⟩ (2 ^ 32)) := by
  simp only [wotsSkAdrs_eq]
  intro h
  exact absurd (congrArg Vector.toList h) (by decide)

/-- The WOTS+ secret-key address at the out-of-range chain index takes the zero fallback. -/
theorem sha2_prf_wotsSk_out_of_range (p : Params) (pk sk : Bytes p.n) :
    (sha2Primitives p).core.PRF pk sk (wotsSkAdrs ⟨0, 0, 0, 0, 2 ^ 32, 0⟩ (2 ^ 32)) =
      zeroBytes p.n :=
  prf_eq_zero_of_not_sha2Domain pk sk (by simp only [Sha2Domain, wotsSkAdrs_eq]; decide)

/-- The all-zero `WOTS_HASH` address is in the checked SHA-2 compression domain, so its key is a
genuine `ADRSc` and not the fallback. -/
theorem zero_isCanonical : (⟨0, 0, 0, 0, 0, 0⟩ : Adrs).isCanonical = true := by decide

/-- Its colliding partner is rejected, `SLHDSA.Adrs.Fits 4` failing on `word2`. -/
theorem outOfRange_isCanonical : (⟨0, 0, 0, 0, 2 ^ 32, 0⟩ : Adrs).isCanonical = false := by decide

/-- **The colliding partner is outside the checked domain**, hence outside the addresses
`SLHDSA.Security.sha2Domain_of_addressFacts` puts every reachable target address in, so an
address property that holds on the checked domain says nothing about it. -/
theorem not_sha2Domain_outOfRange : ¬ Sha2Domain (⟨0, 0, 0, 0, 2 ^ 32, 0⟩ : Adrs) := by
  simp only [Sha2Domain, outOfRange_isCanonical]
  simp

/-- The same pair collides under the SHAKE encoding as well, there by four-byte truncation of
`word2`. -/
theorem shake_wots_collision :
    Adrs.toVector ⟨0, 0, 0, 0, 0, 0⟩ = Adrs.toVector ⟨0, 0, 0, 0, 2 ^ 32, 0⟩ :=
  Vector.toList_inj.mp (by decide)

/-! ## The leaf-index range of a subtree -/

/-- Every global leaf index under the subtree at `(height z, index t)` fits a four-byte field
once the subtree's index range does. -/
theorem fits_four_of_mem_leafRange {z t i : ℕ} (hrange : (t + 1) * 2 ^ z ≤ 2 ^ 32)
    (hi : i / 2 ^ z = t) : Adrs.Fits 4 i = true := by
  refine Adrs.fits_iff.2 (lt_of_lt_of_le ?_ (by norm_num at hrange ⊢; omega))
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos z)).mp (hi ▸ Nat.lt_succ_self t)

end SLHDSA.RomKeyedTest
