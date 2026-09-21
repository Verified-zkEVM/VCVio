/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomKeyed
public import HashSig.SLHDSA.Security.HonestKeys
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Concrete.Instance

/-!
# SLH-DSA keyed-collision obstruction witnesses

The scheme-facing bound of `HashSig.SLHDSA.Security.RomKeyed` is stated at the seed-pinned honest
relation `SLHDSA.Security.HonestSeeded`, which coincides with the run's own `HonestEntry`, so the
separator hypothesis is a statement about the run's own key.  What still stands between that bound
and a number is the address encoding, and that is what these witnesses record: the encoding is
non-injective at every shipped bundle, and the secret-key function provably does *not* separate
the exhibited collision at any of them.

## The address encoding is not injective at any shipped bundle

`SLHDSA.Adrs` has six natural-number fields; every encoding writes each of them into four bytes.
So `⟨0, 0, 3, 0, 0, 0⟩` and `⟨0, 0, 3, 0, 0, 2 ^ 32⟩` — two FORS leaf addresses of one tree,
differing only in the leaf index — have the same 32-byte serialization (`toBytes_collision`) and
the same 22-byte `ADRSc` compression (`compressSha2_collision`).  The FIPS SHA-2 tweak map
`SLHDSA.Concrete.sha2AdrsKey` routes through the *checked* compression instead, and is
non-injective for a different reason: it maps every address it rejects to the same zero key
(`sha2AdrsKey_toList_collision`).

`Function.Injective core.adrsToKey` — the hypothesis of
`SLHDSA.Security.evalDist_romRunFull_targetCollision_le_one` — therefore fails at the map each
of the three shipped bundles installs, stated at the bundle's own field:
`not_injective_adrsToKey_shake`, `not_injective_adrsToKey_sha`, `not_injective_adrsToKey_sha2`.
The carrier-level negations `not_injective_toBytes`, `not_injective_compressSha2` and
`not_injective_sha2AdrsKey` record the cause underneath.

The repository never claimed otherwise: `SLHDSA.Adrs.compressSha2_injective_of_fits` carries
twelve range hypotheses.

## The secret-key function does not separate the exhibited collision

Non-injectivity of the encoding is by itself *not* enough to break the separator.  The two honest
entries of `exists_two_honestEntry_same_key` differ only if the two FORS leaf secrets differ, and
at every shipped bundle they are provably **equal**, because the secret-key function factors
through the very encoding that caused the key collision.

* SHAKE: `shakePRF` reads the address only through `SLHDSA.Adrs.toBytes` (`shakePRF_congr`), the
  same truncating serialization as the SHAKE tweak map's carrier, and the two FORS secret-key
  addresses of the pair share it (`forsSkAdrs_toBytes_collision`), so the secrets coincide
  (`forsSkGenCore_shake_eq`).
* The compatibility bundle: `shaPRF` reads the address only through `SLHDSA.Adrs.compressSha2`
  (`shaPRF_congr`), the same map as `SLHDSA.Concrete.shaAdrsKey`, and the pair shares it
  (`forsSkAdrs_compressSha2_collision`), so the secrets coincide (`forsSkGenCore_sha_eq`).
* FIPS SHA-2: both addresses of a pair of out-of-range leaf indices are rejected by
  `SLHDSA.Concrete.Sha2Address.ofAdrs` (`forsSkAdrs_isCanonical_eq_false`), so the checked `PRF`
  falls back to the zero value at both (`forsSkGenCore_sha2_eq`).

So the hypothesis that the secret-key function factors through the address key — the first of the
three pieces the repair of
`SLHDSA.Security.evalDist_romRunFull_targetCollision_le_one` needs — is close to free at each
concrete core, a rewrite along the factorization rather than a fresh assumption.

## The separator constant at the hypothesis the theorems have

Every theorem of `HashSig.SLHDSA.Security.RomKeyed` quantifies the separator over
`SLHDSA.Security.SettledHonest (SLHDSA.Security.HonestSeeded skSeed pkSeed)`, not over the bare
honest-entry relation, so a lower bound on the admissible constant must be stated there and at a
cache that settles the queries it uses.  `card_le_of_separator_settled` is that bound, taken at
`fullCache`, the cache that settles every public-hash query: any `ρ` meeting the real hypothesis
has `r` at least the number of FORS leaf indices the encoding identifies and the secret-key
function separates.

## What these witnesses do not establish

* **That any key collision breaks the separator.**  The exhibited word3-truncation family at the
  FORS secret-key role does not: `forsSkGenCore_shake_eq`, `forsSkGenCore_sha_eq` and
  `forsSkGenCore_sha2_eq` refute its separation hypothesis at all three bundles.  Whether some
  *other* key collision separates the secret-key function is open, and it is the only thing that
  would make the separator constant of a shipped bundle exceed `1`.
* **That the repair works.**  Of the three pieces, only the factorization is witnessed here, and
  only bundle by bundle rather than as a hypothesis of the general theorem; the kernel-preservation
  clause and the height-bound lemma the differing-height case needs are not proved anywhere.
* **That no other `HonestEntry` constructor is affected.**  Only the `forsLeaf` role is witnessed;
  the same truncation applies to every role address, and that is not formalised.
* **Unrestricted injectivity of the encoded role addresses.**  The *in-range* half is already in
  the repository: `SLHDSA.Security.forsLeafAdrsKey_injective`,
  `SLHDSA.Security.forsTreeAdrsKey_injective` and `SLHDSA.Security.forsRootAdrsKey_injective` of
  `HashSig.SLHDSA.Security.ForsWitnesses` prove per-role injectivity of the encoded address on
  coordinates in range under `SLHDSA.Security.EncodedTargetLedgerConditions`, discharged per
  profile by `SLHDSA.Security.approvedEncodedTargetLedgerConditions`.  Every witness here uses
  out-of-range indices, which those lemmas exclude.

Every statement is a `Prop` over a cache, an address encoding or an `ℝ≥0∞` bound, so the file has
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

/-! ## The secret-key function does not separate the exhibited collision -/

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

/-- **At the SHAKE bundle the two FORS leaf secrets of the collision witness are equal**, so the
witnessed honest entries carry the same input and the pair does not break the separator. -/
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

/-! ## The separator constant at the hypothesis the theorems have -/

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-- Two FORS leaf secrets at one encoded key are two honest entries of **one** transcript with
different inputs.  Nothing in `SLHDSA.Security.HonestEntry.forsLeaf` bounds the leaf index.  The
separation hypothesis is refuted at all three shipped bundles by `forsSkGenCore_shake_eq`,
`forsSkGenCore_sha_eq` and `forsSkGenCore_sha2_eq`. -/
theorem exists_two_honestEntry_same_key (o : RomOutcome vp core) (c : PublicHash.Cache core)
    (adrs : Adrs) (t t' : ℕ)
    (hkey : core.adrsToKey (forsNodeAdrs adrs 0 t) = core.adrsToKey (forsNodeAdrs adrs 0 t'))
    (hne : forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t ≠
      forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t') :
    ∃ (p : core.PkSeed) (k : core.AdrsKey) (xs ys : List core.Y), xs ≠ ys ∧
      HonestEntry o c (.thash p k xs) ∧ HonestEntry o c (.thash p k ys) :=
  ⟨o.pk.pkSeed, core.adrsToKey (forsNodeAdrs adrs 0 t),
    [forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t],
    [forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t'],
    fun h => hne (List.head_eq_of_cons_eq h), .forsLeaf adrs t, hkey ▸ .forsLeaf adrs t'⟩

/-- The cache that settles every public-hash query. -/
@[expose] def fullCache [(publicHashSpec core).Inhabited] : PublicHash.Cache core :=
  QueryCache.ofFn fun _ => some default

@[simp] theorem fullCache_apply [(publicHashSpec core).Inhabited]
    (t : (publicHashSpec core).Domain) :
    (fullCache (core := core)) t = some default := rfl

/-- The separator constant admitted by the theorems of `HashSig.SLHDSA.Security.RomKeyed` — those
quantify over `SLHDSA.Security.SettledHonest (SLHDSA.Security.HonestSeeded …)` — is at least the
number of FORS leaf indices the encoding identifies and the secret-key function distinguishes, at
one fixed transcript. -/
theorem card_le_of_separator_settled [(publicHashSpec core).Inhabited]
    (o : RomOutcome vp core) (r : ℕ) (ρ : (publicHashSpec core).Domain → Fin r)
    (hρ : ∀ (c : PublicHash.Cache core) p k (xs ys : List core.Y),
      SettledHonest (HonestSeeded o.sk.skSeed o.pk.pkSeed) c (.thash p k xs) →
      SettledHonest (HonestSeeded o.sk.skSeed o.pk.pkSeed) c (.thash p k ys) →
      ρ (.thash p k xs) = ρ (.thash p k ys) → xs = ys)
    (adrs : Adrs) (T : Finset ℕ)
    (hkey : ∀ t ∈ T, core.adrsToKey (forsNodeAdrs adrs 0 t) =
      core.adrsToKey (forsNodeAdrs adrs 0 0))
    (hinj : ∀ t ∈ T, ∀ t' ∈ T,
      forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t =
        forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t' → t = t') :
    T.card ≤ r := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := T) (t := (Finset.univ : Finset (Fin r)))
    (f := fun t => ρ (.thash o.pk.pkSeed (core.adrsToKey (forsNodeAdrs adrs 0 0))
      [forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t]))
    (fun _ _ => Finset.mem_univ _) ?_
  · simpa using h
  · intro t htm t' htm' heq
    refine hinj t htm t' htm' ?_
    have hx : SettledHonest (HonestSeeded o.sk.skSeed o.pk.pkSeed) fullCache
        (.thash o.pk.pkSeed (core.adrsToKey (forsNodeAdrs adrs 0 0))
          [forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t]) :=
      ⟨by simp, (honestSeeded_iff o _ _).mpr (hkey t htm ▸ HonestEntry.forsLeaf adrs t)⟩
    have hy : SettledHonest (HonestSeeded o.sk.skSeed o.pk.pkSeed) fullCache
        (.thash o.pk.pkSeed (core.adrsToKey (forsNodeAdrs adrs 0 0))
          [forsSkGenCore core o.sk.skSeed o.pk.pkSeed adrs t']) :=
      ⟨by simp, (honestSeeded_iff o _ _).mpr (hkey t' htm' ▸ HonestEntry.forsLeaf adrs t')⟩
    simpa using hρ fullCache _ _ _ _ hx hy heq

end SLHDSA.RomKeyedTest
