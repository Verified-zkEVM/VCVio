/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomKeyed
public import HashSig.SLHDSA.Security.HonestKeys
public import HashSig.SLHDSA.Security.CacheCoverage
public import HashSig.SLHDSA.Security.EncodedTargets
public import HashSig.SLHDSA.ForsConformance
public import HashSig.SLHDSA.XmssConformance
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Concrete.Instance

/-!
# SLH-DSA keyed-collision obstruction witnesses

The scheme-facing bound of `HashSig.SLHDSA.Security.RomKeyed` is stated at the seed-pinned honest
relation `SLHDSA.Security.HonestSeeded`, which coincides with the run's own `HonestEntry`, so the
separator hypothesis is a statement about the run's own key.  What still stands between that bound
and a number is the address encoding, and that is what these witnesses record: the encoding is
non-injective at every shipped bundle; the secret-key function nevertheless forces equal secrets
at every bundle and both secret-reading roles **on the addresses a conformant run reaches**; and
without that restriction exactly one of the six cells fails, at the one bundle and one role where
the rejection fallback aliases an address the role owns.  The witnesses also record the
distinctness hypothesis of the cache-size bounds and how it is discharged at the FIPS SHA-2
bundle.

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

## Which bundles and roles the factorization covers

`SLHDSA.Security.HonestInput` reads a secret *at the role address itself* in exactly two of its six
branches — the `forsLeaf` branch through `SLHDSA.forsSkAdrs` and the `wotsChain` branch through
`SLHDSA.wotsSkAdrs` — so "equal keys force equal secrets" is two statements,
`SLHDSA.Security.ForsLeafSecretsAgreeOn` and `SLHDSA.Security.WotsChainSecretsAgreeOn`, each
relative to a set of addresses.  Six cells, and **all six hold on the addresses the FIPS SHA-2
checked compression accepts**; five hold with no restriction at all.

* At the two byte-oriented bundles **both roles force equal secrets, unrestricted**:
  `forsLeafSecretsAgreeOn_shake`, `wotsChainSecretsAgreeOn_shake`, `forsLeafSecretsAgreeOn_sha`,
  `wotsChainSecretsAgreeOn_sha`.  Those bundles read the address through exactly the map the key
  uses, but the role builders keep only some of its fields, so the proofs go through block
  extraction — equal serializations have equal per-field byte blocks
  (`SLHDSA.Security.toBytes_blocks`, `SLHDSA.Security.compressSha2_blocks`) — and then through the
  derived-address congruences.
* At the principal FIPS SHA-2 bundle **both roles force equal secrets on
  `SLHDSA.Security.Sha2Domain`**, the addresses the checked compression accepts:
  `forsLeafSecretsAgreeOn_sha2_domain` and `wotsChainSecretsAgreeOn_sha2_domain`, both from
  `injOn_adrsToKey_sha2` alone — on that domain equal keys are equal addresses, so no hash
  property is used.  This is the cell a conformant run needs, because
  `SLHDSA.Security.sha2Domain_of_addressFacts` puts **every reachable target address** in that
  domain, out of `SLHDSA.Security.AddressFacts`, and the per-builder canonicality lemmas
  (`SLHDSA.wotsChainHashAdrs_isCanonical`, `SLHDSA.XmssConformance.wotsLeafAdrs_isCanonical`,
  `SLHDSA.ForsConformance.forsNodeAdrs_isCanonical`) carry it to the derived role addresses;
  `sha2Domain_forsNodeAdrs` and `sha2Domain_wotsChainStepZero` are the two instances used here.
* At that bundle the **FORS-leaf role also holds unrestrictedly** (`forsLeafSecretsAgreeOn_sha2`),
  on its role restriction alone.  `SLHDSA.Concrete.sha2AdrsKey` and
  `SLHDSA.Concrete.sha2PRFChecked` reject on the same three conditions, so key and secret agree
  about which addresses are rejected, and the trichotomy is both-accepted (injective on the
  checked domain, so the addresses are equal), both-rejected (both secrets the all-zero node), or
  one accepted and one rejected — and there the accepted one's key is `zeroBytes 22`, which forces
  it to be `SLHDSA.Adrs.zero` (`eq_zero_of_key_eq_zeroBytes`), whose `type` is `0`.  For the
  `FORS_TREE` role, type `3`, the mixed case is therefore impossible.
* Unrestrictedly, the **WOTS+-chain role is false** at that bundle
  (`not_wotsChainSecretsAgreeOn_sha2`), and its own role restriction does not save it.  The mixed
  case is live for exactly the role whose addresses have type `0`: the rejection fallback aliases
  the all-zero address, and that is a `WOTS_HASH` address.  `⟨0, 0, 0, 0, 0, 0⟩` (accepted) and
  `⟨0, 0, 0, 0, 2 ^ 32, 0⟩` (rejected, since `SLHDSA.Adrs.Fits 4` fails on `word2`) share a key
  (`sha2AdrsKey_wots_collision`) while their WOTS+ secret-key addresses do not
  (`sha2AdrsKey_wotsSk_ne`) and their secrets differ — one a genuine SHA-256 value, the other the
  zero fallback (`sha2_prf_wotsSk_out_of_range`).

## What the one false cell shows, and what it does not

It is a permissiveness of this *model*, not a property of SHA-2.  The colliding partner is
**outside the checked domain** (`not_sha2Domain_outOfRange`, from `outOfRange_isCanonical`), and
its chain index is far outside `len`, so no conformant run reaches it and the machinery of
`HashSig.SLHDSA.Security.EncodedTargets` already excludes it.  What admits it is
`SLHDSA.Security.HonestEntry`, whose addresses are unconstrained by construction.  The same pair
also collides under the SHAKE encoding (`shake_wots_collision`), where the secrets are equal, so
within the FIPS SHA-2 bundle the cause is the zero-key fallback aliasing `SLHDSA.Adrs.zero` — the
hazard `SLHDSA.Concrete.sha2AdrsKey`'s own docstring warns about — and not the four-byte
truncation the witnesses of the previous section are about.

What the witnesses then give is `sha2_two_honestEntry_same_key`: two `wotsChain` honest entries of
one transcript at one encoded key with different input lists, at zero-step chains, so nothing in
the reading queries the cache and no height or chain budget bounds the pair.  That is a statement
about `HonestEntry`; it is **not** a lower bound on the separator constant of
`HashSig.SLHDSA.Security.RomKeyed`, whose theorems quantify the separator over
`SLHDSA.Security.SettledHonest (SLHDSA.Security.HonestSeeded …)` and to which nothing here lifts
it — see the next section for what a bound at that hypothesis takes.

So `SLHDSA.Security.honestEntry_unique` needs canonicality somewhere, and there are two repairs
for different causes.  Carrying canonicality into `SLHDSA.Security.HonestEntry` addresses the
actual cause; whether that restriction breaks existing proofs is the decisive question and is not
examined here.  Changing `SLHDSA.Concrete.sha2AdrsKey`'s rejection fallback to a value outside the
compressed image would also remove the false cell, and changes no behaviour on the specified
domain (`SLHDSA.Concrete.sha2AdrsKey_eq_compressed` is unaffected), but it treats the encoding for
a gap the model opened, and it is an interface change to `SLHDSA.CorePrimitives.AdrsKey` with churn
in the codec agreement lemmas and the byte-law witnesses.

## The distinctness hypothesis of the cache-size bounds

`SLHDSA.Security.pow_le_enncard_of_forsNode?` and `SLHDSA.Security.pow_le_enncard_of_xmssNode?`
bound a cache from below by `2 ^ z` at a settled honest subtree of height `z`, under a
distinctness hypothesis on the leaves' certifying queries.  That hypothesis is **necessary for an
arbitrary core**, not convenient: `not_forall_pow_le_enncard_of_forsNode?` refutes the
unconditional statement at `forsNode?` itself with a core whose address encoding and secret-key
function are both constant, over a cache of two entries that settles every honest FORS subtree at
every height; `PerfectMerkleTree.not_forall_pow_le_enncard_of_simulateQ_merkleRootM` refutes the
generic form.

At the FIPS SHA-2 bundle it is **not an extra assumption**: `injOn_forsLeafKey_sha2` and
`injOn_xmssLeafKey_sha2` discharge it at every height, every subtree index and every
checked-domain base address, from the index range alone — no hash property and no property of the
secret values.  Both go through `SLHDSA.Security.injOn_forsLeafKey_of_injOn_adrsToKey` and
`SLHDSA.Security.injOn_xmssLeafKey_of_injOn_adrsToKey`, which reduce distinctness of the leaf keys
to injectivity of the address encoding on a set containing the leaf addresses, because the leaf
index is a field of the leaf address.

## The separator constant at the hypothesis the theorems have

Every theorem of `HashSig.SLHDSA.Security.RomKeyed` quantifies the separator over
`SLHDSA.Security.SettledHonest (SLHDSA.Security.HonestSeeded skSeed pkSeed)`, not over the bare
honest-entry relation, so a lower bound on the admissible constant must be stated there and at a
cache that settles the queries it uses.  `card_le_of_separator_settled` is that bound, taken at
`fullCache`, the cache that settles every public-hash query: any `ρ` meeting the real hypothesis
has `r` at least the number of FORS leaf indices the encoding identifies and the secret-key
function separates.  No such bound is claimed for the WOTS+-chain collision above: it is stated at
`HonestEntry`, and no lemma here lifts it to `SettledHonest (HonestSeeded …)`.

## What these witnesses do not establish

* **A nonzero concrete hash output.**  Both hypotheses named `hne` say that the genuine SHA-256
  secret at the all-zero WOTS+ secret-key address is not the all-zero node, and `decide` has no
  instance for that at a non-literal byte width while the native route would mint an axiom.  Their
  status differs.  In `not_wotsChainSecretsAgreeOn_sha2` the parameter set and both seeds are
  explicit arguments, so it is a closed proposition and an evaluation outside the gate settles it
  at a chosen instance.  In `sha2_two_honestEntry_same_key` it is about the run's own *sampled*
  seeds, so no evaluation discharges it at all: that conclusion holds on an event of the seed
  space, which fails for a `Nat.card core.Y`-fraction of seed pairs.
* **That the repair works.**  Of the three pieces, the factorization is witnessed bundle by bundle
  rather than as a hypothesis of the general theorem, and it is *false* at one of its six cells
  without a domain restriction; the kernel-preservation clause is not proved anywhere.  Nor is it
  known whether restricting `SLHDSA.Security.HonestEntry` to canonical addresses — the repair that
  addresses the actual cause — breaks any existing proof.
* **That no other `HonestEntry` branch is covered.**  The two properties compare secrets only at
  the role address itself, while the other four branches read secrets too, at *nested* addresses:
  `SLHDSA.wotsPkGenTopsWith` reads `core.PRF pk sk (SLHDSA.wotsSkAdrs adrs i)` for every
  `i : Fin len`, `SLHDSA.xmssLeafWith` descends to the same builder, and the two FORS-node
  branches descend to `SLHDSA.forsSkGenCore`.  The four-byte truncation applies to every role
  address, and that is not formalised either.
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

/-! ## Equal keys force equal secrets: the six cells -/

/-- **At the SHAKE bundle the FORS-leaf secret value factors through the address key**, with no
restriction at all: the secret reads the address through the same serialization as the key, and
block extraction carries that through the role builder. -/
theorem forsLeafSecretsAgreeOn_shake (p : Params) :
    ForsLeafSecretsAgreeOn (shakePrimitives p).core fun _ => True := by
  intro pk sk a b _ _ hkey
  replace hkey : Adrs.toVector a = Adrs.toVector b := hkey
  have h : a.toBytes = b.toBytes := by
    simpa [Adrs.toVector] using congrArg Vector.toList hkey
  change shakePRF pk sk _ = shakePRF pk sk _
  simp only [shakePRF, shakeAddress, toBytes_forsSkAdrs_congr h]

/-- **At the SHAKE bundle the WOTS+-chain secret value factors through the address key**, with no
restriction at all. -/
theorem wotsChainSecretsAgreeOn_shake (p : Params) :
    WotsChainSecretsAgreeOn (shakePrimitives p).core fun _ => True := by
  intro pk sk a b _ _ hkey
  replace hkey : Adrs.toVector a = Adrs.toVector b := hkey
  have h : a.toBytes = b.toBytes := by
    simpa [Adrs.toVector] using congrArg Vector.toList hkey
  change shakePRF pk sk _ = shakePRF pk sk _
  simp only [shakePRF, shakeAddress, toBytes_wotsSkAdrs_congr h]

/-- **At the compatibility bundle the FORS-leaf secret value factors through the address key**,
with no restriction at all. -/
theorem forsLeafSecretsAgreeOn_sha :
    ForsLeafSecretsAgreeOn shaPrimitives.core fun _ => True := by
  intro pk sk a b _ _ hkey
  replace hkey : shaAdrsKey a = shaAdrsKey b := hkey
  have h : a.compressSha2 = b.compressSha2 := by
    simpa [shaAdrsKey] using congrArg Vector.toList hkey
  change shaPRF pk sk _ = shaPRF pk sk _
  simp only [shaPRF, thashPrefix, compressSha2_forsSkAdrs_congr h]

/-- **At the compatibility bundle the WOTS+-chain secret value factors through the address key**,
with no restriction at all. -/
theorem wotsChainSecretsAgreeOn_sha :
    WotsChainSecretsAgreeOn shaPrimitives.core fun _ => True := by
  intro pk sk a b _ _ hkey
  replace hkey : shaAdrsKey a = shaAdrsKey b := hkey
  have h : a.compressSha2 = b.compressSha2 := by
    simpa [shaAdrsKey] using congrArg Vector.toList hkey
  change shaPRF pk sk _ = shaPRF pk sk _
  simp only [shaPRF, thashPrefix, compressSha2_wotsSkAdrs_congr h]

/-- **At the FIPS SHA-2 bundle the FORS-leaf secret value factors through the address key** on
the `forsLeaf` role, with no domain restriction.  Key and secret are rejected together, so the
cases are both-accepted (injective on the checked domain), both-rejected (both secrets the zero
fallback), or one accepted and one rejected — and there the accepted address is
`SLHDSA.Adrs.zero`, whose `type` is `0`, not `3`. -/
theorem forsLeafSecretsAgreeOn_sha2 (p : Params) :
    ForsLeafSecretsAgreeOn (sha2Primitives p).core ForsLeafRole := by
  intro pk sk a b ⟨hat, haw⟩ ⟨hbt, hbw⟩ hkey
  replace hkey : sha2AdrsKey a = sha2AdrsKey b := hkey
  by_cases ha : Sha2Domain a
  · by_cases hb : Sha2Domain b
    · obtain rfl : a = b :=
        sha2AdrsKey_injective_of_domain ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2 hkey
      rfl
    · rw [sha2AdrsKey_eq_zero_of_not_sha2Domain hb] at hkey
      rw [eq_zero_of_key_eq_zeroBytes ha hkey] at hat
      exact absurd hat (by decide)
  · by_cases hb : Sha2Domain b
    · rw [sha2AdrsKey_eq_zero_of_not_sha2Domain ha] at hkey
      rw [eq_zero_of_key_eq_zeroBytes hb hkey.symm] at hbt
      exact absurd hbt (by decide)
    · exact (prf_eq_zero_of_not_sha2Domain pk sk
          (fun h => ha ((sha2Domain_forsSkAdrs_iff hat haw).mp h))).trans
        (prf_eq_zero_of_not_sha2Domain pk sk
          (fun h => hb ((sha2Domain_forsSkAdrs_iff hbt hbw).mp h))).symm

/-- **At the FIPS SHA-2 bundle the FORS-leaf secret value factors through the address key** on
the checked domain, with no role restriction: there the encoding is injective, so equal keys are
equal addresses. -/
theorem forsLeafSecretsAgreeOn_sha2_domain (p : Params) :
    ForsLeafSecretsAgreeOn (sha2Primitives p).core Sha2Domain := by
  intro pk sk a b ha hb hkey
  obtain rfl := injOn_adrsToKey_sha2 p ha hb hkey
  rfl

/-- **At the FIPS SHA-2 bundle the WOTS+-chain secret value factors through the address key** on
the checked domain, with no role restriction.  Since every reachable target address is in that
domain (`SLHDSA.Security.sha2Domain_of_addressFacts`), this is the cell a conformant run needs,
and the unrestricted failure below is outside it. -/
theorem wotsChainSecretsAgreeOn_sha2_domain (p : Params) :
    WotsChainSecretsAgreeOn (sha2Primitives p).core Sha2Domain := by
  intro pk sk a b ha hb hkey
  obtain rfl := injOn_adrsToKey_sha2 p ha hb hkey
  rfl

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
`SLHDSA.Security.sha2Domain_of_addressFacts` puts every reachable target address in.  This is why
the failure below is a permissiveness of `SLHDSA.Security.HonestEntry`, whose addresses are
unconstrained, and not a property of the bundle. -/
theorem not_sha2Domain_outOfRange : ¬ Sha2Domain (⟨0, 0, 0, 0, 2 ^ 32, 0⟩ : Adrs) := by
  simp only [Sha2Domain, outOfRange_isCanonical]
  simp

/-- The same pair collides under the SHAKE encoding as well — there by four-byte truncation of
`word2` — but there the two secrets are equal (`wotsChainSecretsAgreeOn_shake`), so the FIPS SHA-2
failure is caused by the zero-key fallback and not by the truncation. -/
theorem shake_wots_collision :
    Adrs.toVector ⟨0, 0, 0, 0, 0, 0⟩ = Adrs.toVector ⟨0, 0, 0, 0, 2 ^ 32, 0⟩ :=
  Vector.toList_inj.mp (by decide)

/-- **Without a domain restriction the WOTS+-chain secret value does not factor through the
address key at the FIPS SHA-2 bundle**, not even on the `wotsChain` role: the rejection fallback
aliases `SLHDSA.Adrs.zero`, whose type code is exactly that role's, so the mixed case is live at
that one role.  The hypothesis is that the genuine SHA-256 secret at the all-zero WOTS+
secret-key address is not the all-zero node; since the parameter set and both seeds are explicit
arguments, it is a closed proposition, discharged by evaluation outside the gate. -/
theorem not_wotsChainSecretsAgreeOn_sha2 (p : Params) (pk sk : Bytes p.n)
    (hne : (sha2Primitives p).core.PRF pk sk (wotsSkAdrs ⟨0, 0, 0, 0, 0, 0⟩ 0) ≠ zeroBytes p.n) :
    ¬ WotsChainSecretsAgreeOn (sha2Primitives p).core WotsChainRole := by
  intro h
  have hkey : (sha2Primitives p).core.adrsToKey (⟨0, 0, 0, 0, 0, 0⟩ : Adrs) =
      (sha2Primitives p).core.adrsToKey (⟨0, 0, 0, 0, 2 ^ 32, 0⟩ : Adrs) :=
    sha2AdrsKey_wots_collision
  exact hne ((h pk sk ⟨0, 0, 0, 0, 0, 0⟩ ⟨0, 0, 0, 0, 2 ^ 32, 0⟩ rfl rfl hkey).trans
    (sha2_prf_wotsSk_out_of_range p pk sk))

/-- **Two `wotsChain` honest entries of one transcript at one encoded key with different input
lists**, at zero-step chains — so nothing in the reading queries the cache, and no height or
chain budget bounds the pair.  The second entry's address is outside the checked domain
(`not_sha2Domain_outOfRange`), so this exhibits the permissiveness of
`SLHDSA.Security.HonestEntry` rather than a reachable collision.  The hypothesis is about the
run's own *sampled* seeds, so it is not a closed proposition and no evaluation discharges it: the
conclusion holds on the event that the run's secret at the all-zero WOTS+ secret-key address is
not the all-zero node, which fails for a `Nat.card core.Y`-fraction of seed pairs. -/
theorem sha2_two_honestEntry_same_key (vp : ValidatedParams)
    (o : RomOutcome vp (sha2Primitives vp.params).core)
    (c : PublicHash.Cache (sha2Primitives vp.params).core)
    (hne : (sha2Primitives vp.params).core.PRF o.pk.pkSeed o.sk.skSeed
      (wotsSkAdrs ⟨0, 0, 0, 0, 0, 0⟩ 0) ≠ zeroBytes vp.params.n) :
    ∃ (k : (sha2Primitives vp.params).core.AdrsKey)
      (xs ys : List (sha2Primitives vp.params).core.Y), xs ≠ ys ∧
        HonestEntry o c (.thash o.pk.pkSeed k xs) ∧
        HonestEntry o c (.thash o.pk.pkSeed k ys) := by
  refine ⟨(sha2Primitives vp.params).core.adrsToKey ⟨0, 0, 0, 0, 0, 0⟩,
    [(sha2Primitives vp.params).core.PRF o.pk.pkSeed o.sk.skSeed
      (wotsSkAdrs ⟨0, 0, 0, 0, 0, 0⟩ 0)],
    [(sha2Primitives vp.params).core.PRF o.pk.pkSeed o.sk.skSeed
      (wotsSkAdrs ⟨0, 0, 0, 0, 0, 0⟩ (2 ^ 32))], ?_, ?_, ?_⟩
  · intro h
    exact hne ((List.head_eq_of_cons_eq h).trans
      (sha2_prf_wotsSk_out_of_range vp.params o.pk.pkSeed o.sk.skSeed))
  · exact .wotsChain ⟨0, 0, 0, 0, 0, 0⟩ 0 0 _ (chain?_zero _ _ _ _ _ _)
  · have h : (sha2Primitives vp.params).core.adrsToKey
        ((wotsChainAdrs ⟨0, 0, 0, 0, 0, 0⟩ (2 ^ 32)).setHashAddress 0) =
        (sha2Primitives vp.params).core.adrsToKey (⟨0, 0, 0, 0, 0, 0⟩ : Adrs) :=
      sha2AdrsKey_wots_collision.symm
    exact h ▸ .wotsChain ⟨0, 0, 0, 0, 0, 0⟩ (2 ^ 32) 0 _ (chain?_zero _ _ _ _ _ _)

/-! ## The distinctness hypothesis of the cache-size bounds, at the FIPS SHA-2 bundle -/

/-- Every global leaf index under the subtree at `(height z, index t)` fits a four-byte field
once the subtree's index range does. -/
theorem fits_four_of_mem_leafRange {z t i : ℕ} (hrange : (t + 1) * 2 ^ z ≤ 2 ^ 32)
    (hi : i / 2 ^ z = t) : Adrs.Fits 4 i = true := by
  refine Adrs.fits_iff.2 (lt_of_lt_of_le ?_ (by norm_num at hrange ⊢; omega))
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos z)).mp (hi ▸ Nat.lt_succ_self t)

/-- **At the FIPS SHA-2 bundle the FORS distinctness hypothesis of
`SLHDSA.Security.pow_le_enncard_of_forsNode?` follows from address-range facts alone**, at every
height, index and checked-domain base address: no property of the hash and no property of the
secret values is used. -/
theorem injOn_forsLeafKey_sha2 (p : Params) (sk pk : Bytes p.n) {adrs : Adrs}
    (hbase : Sha2Domain adrs) {z t : ℕ} (hrange : (t + 1) * 2 ^ z ≤ 2 ^ 32) :
    Set.InjOn (forsLeafKey (sha2Primitives p).core sk pk adrs) {i | i / 2 ^ z = t} :=
  injOn_forsLeafKey_of_injOn_adrsToKey _ _ _ _ (injOn_adrsToKey_sha2 p)
    fun _i hi =>
      sha2Domain_forsNodeAdrs hbase (by decide) (fits_four_of_mem_leafRange hrange hi)

/-- **At the FIPS SHA-2 bundle the XMSS distinctness hypothesis of
`SLHDSA.Security.pow_le_enncard_of_xmssNode?` follows from address-range facts alone**, at every
height, index and checked-domain base address. -/
theorem injOn_xmssLeafKey_sha2 (p : Params) (sk pk : Bytes p.n) {adrs : Adrs}
    (hbase : Sha2Domain adrs) {z t : ℕ} (hrange : (t + 1) * 2 ^ z ≤ 2 ^ 32) :
    Set.InjOn (xmssLeafKey (sha2Primitives p).core sk pk adrs) {i | i / 2 ^ z = t} :=
  injOn_xmssLeafKey_of_injOn_adrsToKey _ _ _ _ (injOn_adrsToKey_sha2 p)
    fun _i hi => sha2Domain_wotsChainStepZero hbase (fits_four_of_mem_leafRange hrange hi)

/-! ## The unconditional height bound is false for an arbitrary core -/

/-- A core whose address encoding and secret-key function are both constant. -/
@[expose] def constantCore (p : Params) : CorePrimitives p where
  PkSeed := Unit
  SkSeed := Unit
  SkPrf := Unit
  Y := Unit
  AdrsKey := Unit
  adrsToKey := fun _ => ()
  PRF := fun _ _ _ => ()
  PRFmsg := fun _ _ _ => ()
  yToBytes := fun _ => Vector.replicate p.n 0

/-- A cache that answers exactly the arity-one and arity-two `thash` queries. -/
@[expose] def twoEntryCache (p : Params) : PublicHash.Cache (constantCore p) :=
  QueryCache.ofFn fun q =>
    match q with
    | .thash _ _ [_] => some ()
    | .thash _ _ [_, _] => some ()
    | _ => none

/- The two witnesses above are matched against lemmas whose `CorePrimitives` argument is implicit,
so their carrier fields must unfold at implicit transparency for those lemmas to apply.  The
attribute is file-local, so no importer's unifier or instance resolution is affected. -/
attribute [local implicit_reducible] constantCore twoEntryCache

/-- **Every honest FORS subtree of the constant core, at every height, is settled by that
two-entry cache.** -/
theorem forsNode?_twoEntryCache (p : Params) (adrs : Adrs) : ∀ z t : ℕ,
    forsNode? (constantCore p) (twoEntryCache p) () () adrs z t = some () := by
  intro z
  induction z with
  | zero =>
    intro t
    simp only [forsNode?, PerfectMerkleTree.merkleRootM]
    rw [show forsLeafWith (constantCore p) (PublicHash.f (constantCore p) ()) () () adrs t
          = PublicHash.f (constantCore p) () (forsNodeAdrs adrs 0 t)
              (forsSkGenCore (constantCore p) () () adrs t) from rfl,
      simulateQ_toPartialImpl_f]
    rfl
  | succ z ih =>
    intro t
    simp only [forsNode?, PerfectMerkleTree.merkleRootM] at ih ⊢
    rw [simulateQ_bind_eq_some_iff]
    refine ⟨(), ih (2 * t), ?_⟩
    rw [simulateQ_bind_eq_some_iff]
    refine ⟨(), ih (2 * t + 1), ?_⟩
    rw [show forsNodeHashWith (PublicHash.h (constantCore p) ()) adrs (z + 1) t () ()
          = PublicHash.h (constantCore p) () (forsNodeAdrs adrs (z + 1) t) () () from rfl,
      simulateQ_toPartialImpl_h]
    rfl

/-- That cache holds at most two entries. -/
theorem enncard_twoEntryCache_le (p : Params) : QueryCache.enncard (twoEntryCache p) ≤ 2 := by
  have hsub : (twoEntryCache p).toSet ⊆
      {⟨PublicHashQuery.thash () () [()], ()⟩, ⟨PublicHashQuery.thash () () [(), ()], ()⟩} := by
    rintro ⟨q, r⟩ hq
    simp only [QueryCache.mem_toSet, twoEntryCache, QueryCache.ofFn_apply] at hq
    obtain ⟨pk, k, xs⟩ | ⟨y, pk, root, msg⟩ := q
    · match xs with
      | [] => simp at hq
      | [x] => exact Or.inl (by cases pk; cases k; cases x; cases r; rfl)
      | [x, x'] => exact Or.inr (by cases pk; cases k; cases x; cases x'; cases r; rfl)
      | _ :: _ :: _ :: _ => simp at hq
    · simp at hq
  calc QueryCache.enncard (twoEntryCache p) = (((twoEntryCache p).toSet.encard : ℕ∞) : ENNReal) :=
        rfl
    _ ≤ ((2 : ℕ∞) : ENNReal) := by
        refine ENat.toENNReal_le.mpr ((Set.encard_mono hsub).trans ?_)
        exact (Set.encard_insert_le _ _).trans (by simp only [Set.encard_singleton,
          one_add_one_eq_two, le_refl])
    _ = 2 := by simp

/-- **The unconditional height bound is false**, so the distinctness hypothesis of
`SLHDSA.Security.pow_le_enncard_of_forsNode?` is necessary for an arbitrary core rather than
convenient: a core whose address encoding and secret-key function are both constant settles every
height off two cache entries.  At the FIPS SHA-2 bundle the hypothesis is nonetheless discharged
from address-range facts alone (`injOn_forsLeafKey_sha2`). -/
theorem not_forall_pow_le_enncard_of_forsNode? :
    ¬ ∀ (p : Params) (core : CorePrimitives p) (c : PublicHash.Cache core)
        (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) (v : core.Y),
      forsNode? core c sk pk adrs z t = some v →
        ((2 ^ z : ℕ) : ENNReal) ≤ QueryCache.enncard c := by
  intro h
  have hle := (h FipsParameterSet.SLHDSA_SHA2_128s.params (constantCore _) (twoEntryCache _)
    () () Adrs.zero 2 0 () (forsNode?_twoEntryCache _ Adrs.zero 2 0)).trans
    (enncard_twoEntryCache_le _)
  norm_num at hle

end SLHDSA.RomKeyedTest
