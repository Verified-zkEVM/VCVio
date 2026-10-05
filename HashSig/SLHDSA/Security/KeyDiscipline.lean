/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.EncodedTargets
public import HashSig.SLHDSA.Security.KeySeparation

/-!
# The key discipline of the SLH-DSA address encoding

The tweakable-hash oracle is keyed by `core.adrsToKey`, a finite encoding of an unbounded address
type, so no shipped encoding is injective on every address. `CorePrimitives.KeyDiscipline vp core`
collects the three facts about the encoding that a reduction to the random oracle uses:

* `CorePrimitives.KeyInjective vp core`: the encoding is injective on the in-range addresses of
  `vp`, those satisfying `Security.AddressFacts vp`;
* `Security.CanonicalAddressBounds vp.params`: the parameter set's address fields fit their
  FIPS 205 widths, which is what places the construction's addresses in that range (every
  `Security.addressFacts_*` ledger lemma takes it);
* `CorePrimitives.KeySeparated core`: no address of type at most `4` shares its key with a
  secret-key address, at every address, in range or not.

The first does not imply the third: injectivity on the in-range addresses says nothing about an
out-of-range secret-key address, and a key map that sends one to the key of an in-range hash
address is injective on the in-range addresses and not key-separated.

## Discharges

* SHAKE (`Concrete.shakePrimitives`): `Concrete.keyInjective_shakePrimitives` holds for every
  validated parameter set, because the full 32-byte serialization is injective on canonical
  addresses; `Concrete.keyDiscipline_shakePrimitives` under `CanonicalAddressBounds`.
* FIPS SHA-2 (`Concrete.sha2Primitives`): `Concrete.keyInjective_sha2Primitives` under
  `ApprovedAddressBounds`, the compressed `ADRSc` widths; `Concrete.keyDiscipline_sha2Primitives`.
* The SLH-DSA-SHA2-128-24 compatibility bundle (`Concrete.shaPrimitives`):
  `Concrete.injOn_shaAdrsKey` for every parameter set under `ApprovedAddressBounds`, and
  `Concrete.keyDiscipline_shaPrimitives` at the bundle's own parameter set.
* Every FIPS 205 parameter set (`Concrete.keyDiscipline_approvedPrimitives`) and the limited
  SHA2-128-24 profile under FIPS SHA-2 (`Concrete.keyDiscipline_limited`), with the bounds from
  `Security.fipsApprovedAddressBounds` and `Security.limitedApprovedAddressBounds`.
-/

public section

namespace SLHDSA

open Security

/-- The address-to-key encoding of `core` is injective on the in-range addresses of `vp`: two
addresses that are FIPS-canonical and lie in the hypertree's layer and tree ranges
(`Security.AddressFacts vp`) and share an oracle key are equal. -/
@[expose] def CorePrimitives.KeyInjective (vp : ValidatedParams)
    (core : CorePrimitives vp.params) : Prop :=
  Set.InjOn core.adrsToKey {a : Adrs | AddressFacts vp a}

/-- The key discipline of an address encoding: it is injective on the in-range addresses, the
parameter set's address fields fit their FIPS 205 widths, and it is key-separated at every
address. -/
structure CorePrimitives.KeyDiscipline (vp : ValidatedParams) (core : CorePrimitives vp.params) :
    Prop where
  /-- The encoding is injective on the in-range addresses. -/
  keyInjective : core.KeyInjective vp
  /-- The parameter set's address fields fit their FIPS 205 widths. -/
  canonicalAddressBounds : CanonicalAddressBounds vp.params
  /-- No address of type at most `4` shares its key with a secret-key address. -/
  keySeparated : core.KeySeparated

namespace Concrete

/-- The SHAKE encoding, the full 32-byte serialization, is injective on canonical addresses, so on
the in-range addresses of every validated parameter set. -/
theorem keyInjective_shakePrimitives (vp : ValidatedParams) :
    (shakePrimitives vp.params).core.KeyInjective vp := by
  intro a ha b hb hkey
  have hvec : Adrs.fromVector a.toVector = Adrs.fromVector b.toVector :=
    congrArg Adrs.fromVector hkey
  rwa [Adrs.fromVector_toVector_of_isCanonical a ha.canonical,
    Adrs.fromVector_toVector_of_isCanonical b hb.canonical] at hvec

/-- Under the compressed `ADRSc` widths the FIPS SHA-2 encoding is injective on the in-range
addresses: they lie in its checked domain, where the key is `ADRSc`. -/
theorem keyInjective_sha2Primitives (vp : ValidatedParams)
    (hb : ApprovedAddressBounds vp.params) :
    (sha2Primitives vp.params).core.KeyInjective vp := by
  intro a ha b hb' hkey
  obtain ⟨hac, hal, hat⟩ := sha2Domain_of_addressFacts hb ha
  obtain ⟨hbc, hbl, hbt⟩ := sha2Domain_of_addressFacts hb hb'
  exact sha2AdrsKey_injective_of_domain hac hal hat hbc hbl hbt hkey

/-- Under the compressed `ADRSc` widths the unchecked `ADRSc` key of the compatibility bundle is
injective on the in-range addresses of every validated parameter set. -/
theorem injOn_shaAdrsKey (vp : ValidatedParams) (hb : ApprovedAddressBounds vp.params) :
    Set.InjOn shaAdrsKey {a : Adrs | AddressFacts vp a} := by
  intro a ha b hb' hkey
  obtain ⟨hac, hal, hat⟩ := sha2Domain_of_addressFacts hb ha
  obtain ⟨hbc, hbl, hbt⟩ := sha2Domain_of_addressFacts hb hb'
  have hlist : a.compressSha2 = b.compressSha2 := by
    rw [← shaAdrsKey_toList, ← shaAdrsKey_toList, hkey]
  rcases Adrs.fits_of_isCanonical a hac with ⟨_, _, _, ha1, ha2, ha3⟩
  rcases Adrs.fits_of_isCanonical b hbc with ⟨_, _, _, hb1, hb2, hb3⟩
  exact Adrs.compressSha2_injective_of_fits hal hat (Adrs.fits_one_type_of_isCanonical hac)
    ha1 ha2 ha3 hbl hbt (Adrs.fits_one_type_of_isCanonical hbc) hb1 hb2 hb3 hlist

/-- The compatibility bundle's encoding is injective on the in-range addresses of its own
parameter set. -/
theorem keyInjective_shaPrimitives :
    shaPrimitives.core.KeyInjective (LimitedParameterSet.validatedParams .SLHDSA_SHA2_128_24) :=
  injOn_shaAdrsKey _ (limitedApprovedAddressBounds .SLHDSA_SHA2_128_24)

/-- The SHAKE bundles satisfy the key discipline at every parameter set whose address fields fit
their FIPS 205 widths. -/
theorem keyDiscipline_shakePrimitives (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) :
    (shakePrimitives vp.params).core.KeyDiscipline vp :=
  ⟨keyInjective_shakePrimitives vp, hb, keySeparated_shakePrimitives vp.params⟩

/-- The FIPS SHA-2 bundles satisfy the key discipline at every parameter set that fits the
compressed `ADRSc` widths. -/
theorem keyDiscipline_sha2Primitives (vp : ValidatedParams)
    (hb : ApprovedAddressBounds vp.params) :
    (sha2Primitives vp.params).core.KeyDiscipline vp :=
  ⟨keyInjective_sha2Primitives vp hb, hb.toCanonicalAddressBounds,
    keySeparated_sha2Primitives vp.params⟩

/-- The SLH-DSA-SHA2-128-24 compatibility bundle satisfies the key discipline. -/
theorem keyDiscipline_shaPrimitives :
    shaPrimitives.core.KeyDiscipline (LimitedParameterSet.validatedParams .SLHDSA_SHA2_128_24) :=
  ⟨keyInjective_shaPrimitives,
    (limitedApprovedAddressBounds .SLHDSA_SHA2_128_24).toCanonicalAddressBounds,
    keySeparated_shaPrimitives⟩

/-- The FIPS SHA-2 bundle at the limited SHA2-128-24 profile satisfies the key discipline. -/
theorem keyDiscipline_limited (ps : LimitedParameterSet) :
    (sha2Primitives ps.params).core.KeyDiscipline ps.validatedParams :=
  keyDiscipline_sha2Primitives ps.validatedParams (limitedApprovedAddressBounds ps)

/-- Every FIPS 205 parameter set's approved bundle satisfies the key discipline. -/
theorem keyDiscipline_approvedPrimitives (ps : FipsParameterSet) :
    (approvedPrimitives ps).core.KeyDiscipline ps.validatedParams := by
  have hb : ApprovedAddressBounds ps.validatedParams.params := fipsApprovedAddressBounds ps
  rw [approvedPrimitives]
  cases ps.hashFamily with
  | sha2 => exact keyDiscipline_sha2Primitives ps.validatedParams hb
  | shake => exact keyDiscipline_shakePrimitives ps.validatedParams hb.toCanonicalAddressBounds

/-- Every FIPS 205 parameter set's approved bundle is injective on its in-range addresses. -/
theorem keyInjective_approvedPrimitives (ps : FipsParameterSet) :
    (approvedPrimitives ps).core.KeyInjective ps.validatedParams :=
  (keyDiscipline_approvedPrimitives ps).keyInjective

/-- Every FIPS 205 parameter set's approved bundle is key-separated. -/
theorem keySeparated_approvedPrimitives (ps : FipsParameterSet) :
    (approvedPrimitives ps).core.KeySeparated :=
  (keyDiscipline_approvedPrimitives ps).keySeparated

end Concrete

end SLHDSA
