/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteClash
public import HashSig.SLHDSA.Security.ByteConformance
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSig.SLHDSA.Security.LinkedHazards
public import HashSig.SLHDSA.Security.WeakKeyBound

/-!
# SLH-DSA over a single SHAKE256 random oracle: the unforgeability bound

FIPS 205 instantiates every hash function of the SHAKE parameter sets with SHAKE256 at a per-role
byte layout (§11.1). `HashSig.SLHDSA.Security.ByteModel` states that model, SLH-DSA over one random
oracle on byte strings (`shakeRomScheme`, `shakeStrongAdvantage`), and
`HashSig.SLHDSA.Security.ByteConformance` shows that answering its oracle by SHAKE256 gives
FIPS 205's SHAKE internal key generation, signing and verification
(`shakeRomScheme_map_shakeAnswer`). This module bounds the strong forging advantage in that model
(SUF-CMA): the probability of a strong forgery, a valid pair of message and signature that the
signing oracle never returned, so a second signature on a signed message counts.

## The bound

For `16 ≤ n ≤ 32`, `n ≤ m` and address fields within their FIPS 205 widths
(`CanonicalAddressBounds`), at every public seed `PK.seed`, an adversary making at most `qh`
queries of the single oracle and `qs` signing queries makes a strong forgery with probability at
most

`securityBound p |Y| 2 1 qh qs + (qs + 1) / |Y| + weakKeyMass vp PK.seed`,

with `|Y| = 256 ^ n` (`shakeStrongAdvantage_pure_le_securityBound`). The first term is the bound of
the three-oracle model (`securityTarget_two_one`). The second, charged jointly with the events of
the first in one potential, is for an honest `PRF_msg` string `SK.prf ‖ opt_rand ‖ M` that is also
the string of another query: `qs / |Y|` for the signer's `H_msg` strings that begin with `SK.prf`,
and `1 / |Y|` for `SK.prf = PK.seed`; the forger's and the verifier's `H_msg` strings that begin
with `SK.prf` are charged inside the first term. The third is the probability, over the uniform
public root, that the public key is weak (`IsWeakKey`): that the first `32` bytes of
`PK.seed ‖ PK.root` are the key of an honest address, so that an `H_msg` string can also be a
tweakable-hash string. At every `n`, a seed of weak-key mass zero has the bound without the third
term (`shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero`).

The `opt_rand` source is arbitrary, so these statements hold in hedged signing (`opt_rand`
uniform) and in deterministic signing (`opt_rand = PK.seed`) alike, with the same terms.

## The weak seeds and the uniform public seed

At `n = 32` the weak-key event is a property of the public seed, whose weak-key mass is zero or
one (`weakKeyMass_eq_zero_or_eq_one_of_n_eq_32`): at a seed that is not an honest address key it
never occurs, and the per-seed bound has no third term
(`shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32`). At every seed, the weak ones included,
`HashSig.SLHDSA.Security.LinkedHazards` bounds the strong advantage by

`ε = securityBound p |Y| 2 1 (qh + V) qs + 2 (qs + 1) / |Y|`,

with `V` the verifier's query bound, through the verification redirected at the linked points
(`shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32`). So the advantage at a seed is at most
the smaller of the two bounds (`shakeStrongAdvantage_pure_le_min_of_n_eq_32`), and, the mass being
zero or one, at most the first bound with the weak-key mass multiplied by `min 1 ε`
(`min_add_weakKeyMass_le_of_n_eq_32`). Averaged over the uniform public seed of FIPS 205
(`lintegral_add_weakKeyMass_mul_le`), the advantage is at most

`securityBound p |Y| 2 1 qh qs + (qs + 1) / |Y| + |A_hon| / 2^256 · weakSeedFactor vp ε`

with `|A_hon| = honestAdrsCount vp` and `weakSeedFactor vp ε` equal to `min 1 ε` at `n = 32` and to
`1` otherwise (`shakeStrongAdvantage_le_securityBound`;
`shakeStrongAdvantage_le_securityBound_of_n_eq_32`). At `n < 32` the last term is `|A_hon| / 2^256`;
at `n = 32` it is `|A_hon| / 2^256 · min 1 ε`, the weak seeds' share of the bound at every seed. The
factor is at most one (`weakSeedFactor_le_one`), so the averaged bound implies the one with the
weak-key term `|A_hon| / 2^256`.

## Hedged signing

A signer's `PRF_msg` string `SK.prf ‖ opt_rand ‖ M` is an `H_msg` string
`R ‖ PK.seed ‖ PK.root ‖ M'` only when its `opt_rand` is `PK.seed`. With `opt_rand` drawn
uniformly at each signature, as in FIPS 205's hedged signing, the second term becomes

`1 / |Y| + qs (qh + qs + 1) / |Y|^2`

(`shakeStrongAdvantage_pure_le_securityBound_hedged`, averaged
`shakeStrongAdvantage_le_securityBound_hedged`): a clash through a signer's `PRF_msg` string needs
both some `opt_rand` equal to `PK.seed`, of probability at most `qs / |Y|`, and, independently,
`SK.prf` equal to the randomizer of one of the at most `qh + qs + 1` `H_msg` points
(`prEvent_romSchemeRun_strongWins_or_runPrfKeyClash_le`). For any `opt_rand` source that equals the
public seed with probability at most `ε`, the second term is `1 / |Y| + qs ε (qh + qs + 1) / |Y|`
(`shakeStrongAdvantage_pure_le_securityBound_of_prEvent_optRand_le`). In hedged signing the bound at
every seed at `n = 32` is
`securityBound p |Y| 2 1 (qh + V) qs + 1 / |Y| + qs (qh + V + qs + 1) / |Y|^2 +` `(qs + 1) / |Y|`,
and the averaged hedged bound has it as `ε` in the weak seeds' factor.

## The argument

The routed adversary reads each byte string as a typed query of the three oracles and makes at most
as many typed queries (`routeAdv`, `romQueryBound_routeAdv`). The advantage is at most the
probability that its run against the three-oracle scheme wins, hits the message-`PRF` key
(`RunPrfKeyHit`) or has a weak public key
(`shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyHit_or_isWeakKey`). The first two are bounded
jointly (`prEvent_romSchemeRun_strongWins_or_runPrfKeyHit_le`); in hedged signing the hit carries
the `opt_rand = PK.seed` of the clashing `PRF_msg` string (`RunPrfKeyClash`,
`shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyClash_or_isWeakKey`) and is bounded with the
product term instead (`prEvent_romSchemeRun_strongWins_or_runPrfKeyClash_le`). The weak key is
bounded by the uniformity of the public root (`prEvent_romSchemeRun_isWeakKey_le`), and the average
over the seed by `lintegral_add_weakKeyMass_mul_le`. Every side condition of the three-oracle bound
holds for the SHAKE carriers: the byte laws, the key discipline under the FIPS 205 address widths,
and `|Y| = |SK.prf|`. The strong win enters only through the three-oracle bridge, so every term is
the one of the existential bound.

## Main statements

The right-hand sides are named: `byteBound` and `byteBoundHedged` at a public seed without the
weak-key term, `everySeedBound` and `everySeedBoundHedged` at every public seed at `n = 32`.

* `shakeStrongAdvantage_pure_le_securityBound`: the bound at a public seed.
* `shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero`: the bound at a public seed of
  weak-key mass zero, without the weak-key term.
* `shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32`: at `n = 32`, the bound at a public seed
  that is not an honest address key, without the weak-key term.
* `shakeStrongAdvantage_pure_le_min_of_n_eq_32`: at `n = 32`, at every public seed, the smaller of
  that bound and the bound at every seed.
* `shakeStrongAdvantage_le_securityBound`, `shakeStrongAdvantage_le_securityBound_of_n_eq_32`: the
  bound over the uniform public seed, with the weak seeds' factor.
* `shakeStrongAdvantage_pure_le_securityBound_validatedParams`,
  `shakeStrongAdvantage_pure_le_securityBound_add_validatedParams`,
  `shakeStrongAdvantage_le_securityBound_validatedParams`: the bound at a public seed, the bound at
  every public seed at `n = 32`, and the averaged bound at the six SHAKE parameter sets, with every
  side condition discharged. They are stated over all twelve FIPS 205 parameter sets, a SHA-2 set
  contributing only its parameters, which are those of its SHAKE twin.
* The `_hedged` forms of each: the same in hedged signing, with
  `1 / |Y| + qs (qh + qs + 1) / |Y|^2` in place of `(qs + 1) / |Y|`.
* The existential forms of the bound at a public seed, of the averaged bounds and of the bounds at
  the parameter sets, `shakeAdvantage_*` for the corresponding `shakeStrongAdvantage_*`: the
  forging advantage at the same bound, through `shakeAdvantage_le_shakeStrongAdvantage`.

## Scope

The model is that of `HashSig.SLHDSA.Security.ByteModel`: FIPS 205's internal functions, and a
SHAKE256 random oracle with `m`-byte outputs. The bound is a classical random-oracle statement.
Strong unforgeability is over the structured signatures of the internal functions; at the external
API, over byte strings, it also needs the fixed-length signature encoding to parse one-to-one,
which is not proved here. The SHA-2 parameter sets, whose hash functions are
built from SHA-256 and SHA-512 with a compressed address, `MGF1` and `HMAC`, are not covered.

## References

* NIST FIPS 205, §9 (Algorithms 18–20), §10.2 (hedged and deterministic signing), §11.1.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.Security

open Concrete

variable {vp : ValidatedParams}
  {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}

/-! ## The bounds -/

variable (vp) in
/-- The bound of the single-SHAKE256 model at a public seed, without its weak-key term:
`securityBound vp.params (256 ^ n) 2 1 qh qs + (qs + 1) / 256 ^ n`. -/
noncomputable abbrev byteBound (qh qs : ℕ) : ℝ≥0∞ :=
  securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs +
    ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : ℕ)

variable (vp) in
/-- The bound of the single-SHAKE256 model in hedged signing at a public seed, without its weak-key
term: `securityBound vp.params (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs (qh + qs + 1) / 256 ^ (2 n)`.
-/
noncomputable abbrev byteBoundHedged (qh qs : ℕ) : ℝ≥0∞ :=
  securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs + 1 / (256 ^ vp.params.n : ℕ) +
    qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) ^ 2

variable (vp) in
/-- The bound of the single-SHAKE256 model at every public seed at `n = 32`:
`securityBound vp.params (256 ^ n) 2 1 (qh + V) qs + 2 (qs + 1) / 256 ^ n`, with `V` the verifier's
query bound. -/
noncomputable abbrev everySeedBound (qh qs : ℕ) : ℝ≥0∞ :=
  securityBound vp.params (256 ^ vp.params.n) 2 1
      (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
    2 * ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : ℕ)

variable (vp) in
/-- The bound of the single-SHAKE256 model in hedged signing at every public seed at `n = 32`:
`byteBoundHedged vp (qh + V) qs + (qs + 1) / 256 ^ n`, with `V` the verifier's query bound. -/
noncomputable abbrev everySeedBoundHedged (qh qs : ℕ) : ℝ≥0∞ :=
  byteBoundHedged vp (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
    ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : ℕ)

/-! ## At a public seed -/

/-- **SLH-DSA over one SHAKE256 oracle, at a public seed.** For `16 ≤ n ≤ 32`, `n ≤ m` and address
fields within their FIPS 205 widths, an adversary against `shakeRomScheme` at the public seed
`pkSeed` making at most `qh` queries of the single oracle and `qs` signing queries makes a strong
forgery with probability at most `byteBound vp qh qs` plus the weak-key mass of `pkSeed`.
`optRand` is arbitrary: the bound holds in hedged and deterministic signing. -/
theorem shakeStrongAdvantage_pure_le_securityBound (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤ byteBound vp qh qs + weakKeyMass vp pkSeed := by
  rw [byteBound, ← natCard_shakePrimitives_y]
  exact (shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyHit_or_isWeakKey hn hnm hn16 pkSeed
    adv).trans <| (prEvent_or_le _ _ _).trans <| add_le_add
      (prEvent_romSchemeRun_strongWins_or_runPrfKeyHit_le (shakePrimitives_byteLaws vp.params)
        (keyDiscipline_shakePrimitives vp hb) le_rfl _ optRand pkSeed Function.injective_id
        pkSeed (romQueryBound_routeAdv hn hnm hadv))
      (prEvent_romSchemeRun_isWeakKey_le hb _ optRand pkSeed _)

/-- **SLH-DSA over one SHAKE256 oracle, at a seed of weak-key mass zero.** Under the hypotheses of
`shakeStrongAdvantage_pure_le_securityBound`, at a public seed of weak-key mass zero the strong
advantage is at most `byteBound vp qh qs`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero
    (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m) {pkSeed : (shakeCore vp).PkSeed}
    (hs : weakKeyMass vp pkSeed = 0)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) : shakeStrongAdvantage vp adv ≤ byteBound vp qh qs := by
  simpa [hs] using shakeStrongAdvantage_pure_le_securityBound hb hn16 hn hnm pkSeed adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, at a strong public seed.** At `n = 32`,
`n ≤ m` and address fields within their FIPS 205 widths, at a public seed that is not the key of
an honest address, an adversary making at most `qh` queries of the single oracle and `qs` signing
queries makes a strong forgery with probability at most `byteBound vp qh qs`, in hedged and
deterministic signing. -/
theorem shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32
    (hb : CanonicalAddressBounds vp.params) (hn : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m) {pkSeed : (shakeCore vp).PkSeed}
    (hs : ¬IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pkSeed : Bytes _))))
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) : shakeStrongAdvantage vp adv ≤ byteBound vp qh qs :=
  shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero hb (by omega) hn.le hnm
    ((weakKeyMass_eq_zero_iff_of_n_eq_32 hn pkSeed).2 hs) adv hadv

/-- **SLH-DSA over one SHAKE256 oracle, at a public seed, when `opt_rand` rarely equals it.** For
`16 ≤ n ≤ 32`, `n ≤ m` and address fields within their FIPS 205 widths, if `optRand pk` equals
the public seed `pkSeed` with probability at most `ε` at every public key, an adversary against
`shakeRomScheme` at `pkSeed` making at most `qh` queries of the single oracle and `qs` signing
queries makes a strong forgery with probability at most
`securityBound vp.params (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs * ε * (qh + qs + 1) / 256 ^ n`
plus the weak-key mass of `pkSeed`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_of_prEvent_optRand_le
    (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs + 1 / (256 ^ vp.params.n : ℕ) +
        qs * ε * (((qh : ℝ≥0∞) + qs + 1) / (256 ^ vp.params.n : ℕ)) + weakKeyMass vp pkSeed := by
  rw [← natCard_shakePrimitives_y]
  exact (shakeStrongAdvantage_pure_le_strongWins_or_runPrfKeyClash_or_isWeakKey hn hnm hn16 pkSeed
    adv).trans <| (prEvent_or_le _ _ _).trans <| add_le_add
      (prEvent_romSchemeRun_strongWins_or_runPrfKeyClash_le (shakePrimitives_byteLaws vp.params)
        (keyDiscipline_shakePrimitives vp hb) le_rfl _ optRand pkSeed Function.injective_id
        pkSeed hε (romQueryBound_routeAdv hn hnm hadv))
      (prEvent_romSchemeRun_isWeakKey_le hb _ optRand pkSeed _)

/-- **SLH-DSA over one SHAKE256 oracle with hedged signing, at a public seed.** For `16 ≤ n ≤ 32`,
`n ≤ m` and address fields within their FIPS 205 widths, with `opt_rand` drawn uniformly at each
signature, an adversary against `shakeRomScheme` at the public seed `pkSeed` making at most `qh`
queries of the single oracle and `qs` signing queries makes a strong forgery with probability at
most `byteBoundHedged vp qh qs` plus the weak-key mass of `pkSeed`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_hedged (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤ byteBoundHedged vp qh qs + weakKeyMass vp pkSeed := by
  refine (shakeStrongAdvantage_pure_le_securityBound_of_prEvent_optRand_le hb hn16 hn hnm pkSeed
    (ε := (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
    (fun _ ↦ (SampleableType.prEvent_uniformSample_eq_singleton_natCard _).le) adv hadv).trans
    (le_of_eq ?_)
  rw [natCard_shakePrimitives_y]
  simp only [byteBoundHedged, ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
  ring

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32` with hedged signing, at a strong public seed.**
At `n = 32`, `n ≤ m` and address fields within their FIPS 205 widths, with `opt_rand` drawn
uniformly at each signature, at a public seed that is not the key of an honest address, the strong
advantage of an adversary making at most `qh` queries of the single oracle and `qs` signing
queries is at most `byteBoundHedged vp qh qs`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_hedged_of_n_eq_32
    (hb : CanonicalAddressBounds vp.params) (hn : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m) {pkSeed : (shakeCore vp).PkSeed}
    (hs : ¬IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pkSeed : Bytes _))))
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤ byteBoundHedged vp qh qs := by
  simpa [weakKeyMass_eq_zero_of_n_eq_32 hn hs] using
    shakeStrongAdvantage_pure_le_securityBound_hedged hb (by omega) hn.le hnm pkSeed adv hadv

/-! ## The weak seeds at `n = 32` -/

variable (vp) in
/-- The factor of the weak public seeds in the averaged bound: `min 1 ε` at `n = 32`, where `ε` is
a bound at every public seed, and `1` otherwise. -/
noncomputable def weakSeedFactor (ε : ℝ≥0∞) : ℝ≥0∞ :=
  if vp.params.n = 32 then min 1 ε else 1

/-- The factor of the weak seeds is at most one. -/
theorem weakSeedFactor_le_one (ε : ℝ≥0∞) : weakSeedFactor vp ε ≤ 1 := by
  unfold weakSeedFactor
  split_ifs <;> simp

/-- At `n = 32`, the factor of the weak seeds is `min 1 ε`. -/
theorem weakSeedFactor_of_n_eq_32 (hn : vp.params.n = 32) (ε : ℝ≥0∞) :
    weakSeedFactor vp ε = min 1 ε := by
  simp only [weakSeedFactor, hn, reduceIte]

/-- At `n ≠ 32`, the factor of the weak seeds is one. -/
theorem weakSeedFactor_of_ne (hn : vp.params.n ≠ 32) (ε : ℝ≥0∞) : weakSeedFactor vp ε = 1 := by
  simp only [weakSeedFactor, hn, reduceIte]

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, at a public seed: the smaller bound.** At
`n = 32`, `n ≤ m` and address fields within their FIPS 205 widths, an adversary against
`shakeRomScheme` at the public seed `pkSeed` making at most `qh` queries of the single oracle and
`qs` signing queries makes a strong forgery with probability at most the smaller of
`byteBound vp qh qs` plus the weak-key mass of `pkSeed` and `everySeedBound vp qh qs`. `optRand`
is arbitrary: the bound holds in hedged and deterministic signing. -/
theorem shakeStrongAdvantage_pure_le_min_of_n_eq_32 (hb : CanonicalAddressBounds vp.params)
    (hn : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤
      min (byteBound vp qh qs + weakKeyMass vp pkSeed) (everySeedBound vp qh qs) := by
  refine le_min (shakeStrongAdvantage_pure_le_securityBound hb (by omega) hn.le hnm pkSeed adv hadv)
    ((shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32 hb hn hnm adv hadv).trans_eq ?_)
  rw [natCard_shakePrimitives_y]
  simp only [everySeedBound, ENNReal.div_eq_inv_mul]
  ring

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32` with hedged signing, at a public seed: the
smaller bound.** At `n = 32`, `n ≤ m` and address fields within their FIPS 205 widths, with
`opt_rand` drawn uniformly at each signature, the strong advantage at the public seed `pkSeed` of
an adversary making at most `qh` queries of the single oracle and `qs` signing queries is at most
the smaller of `byteBoundHedged vp qh qs` plus the weak-key mass of `pkSeed` and
`everySeedBoundHedged vp qh qs`. -/
theorem shakeStrongAdvantage_pure_le_min_hedged_of_n_eq_32 (hb : CanonicalAddressBounds vp.params)
    (hn : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤
      min (byteBoundHedged vp qh qs + weakKeyMass vp pkSeed) (everySeedBoundHedged vp qh qs) := by
  refine le_min (shakeStrongAdvantage_pure_le_securityBound_hedged hb (by omega) hn.le hnm pkSeed
    adv hadv) ((shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32_hedged hb hn hnm adv hadv
      (ε := (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
      (fun _ ↦ (SampleableType.prEvent_uniformSample_eq_singleton_natCard _).le)).trans_eq ?_)
  rw [natCard_shakePrimitives_y]
  simp only [everySeedBoundHedged, byteBoundHedged, ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
  ring

/-- **SLH-DSA over one SHAKE256 oracle, at a public seed, with the weak seeds' factor.** For
`16 ≤ n ≤ 32`, `n ≤ m` and address fields within their FIPS 205 widths, the strong advantage at
the public seed `pkSeed` of an adversary making at most `qh` queries of the single oracle and `qs`
signing queries is at most `byteBound vp qh qs` plus the weak-key mass of `pkSeed` times
`weakSeedFactor vp (everySeedBound vp qh qs)`. `optRand` is arbitrary. -/
theorem shakeStrongAdvantage_pure_le_securityBound_add_weakKeyMass_mul
    (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤
      byteBound vp qh qs + weakKeyMass vp pkSeed * weakSeedFactor vp (everySeedBound vp qh qs) := by
  by_cases h32 : vp.params.n = 32
  · rw [weakSeedFactor_of_n_eq_32 h32]
    exact (shakeStrongAdvantage_pure_le_min_of_n_eq_32 hb h32 hnm pkSeed adv hadv).trans
      (min_add_weakKeyMass_le_of_n_eq_32 h32 pkSeed _ _)
  · rw [weakSeedFactor_of_ne h32, mul_one]
    exact shakeStrongAdvantage_pure_le_securityBound hb hn16 hn hnm pkSeed adv hadv

/-- **SLH-DSA over one SHAKE256 oracle with hedged signing, at a public seed, with the weak
seeds' factor.** For `16 ≤ n ≤ 32`, `n ≤ m` and address fields within their FIPS 205 widths, with
`opt_rand` drawn uniformly at each signature, the strong advantage at the public seed `pkSeed` is
at most `byteBoundHedged vp qh qs` plus the weak-key mass of `pkSeed` times
`weakSeedFactor vp (everySeedBoundHedged vp qh qs)`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_hedged_add_weakKeyMass_mul
    (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32)
    (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤ byteBoundHedged vp qh qs +
      weakKeyMass vp pkSeed * weakSeedFactor vp (everySeedBoundHedged vp qh qs) := by
  by_cases h32 : vp.params.n = 32
  · rw [weakSeedFactor_of_n_eq_32 h32]
    exact (shakeStrongAdvantage_pure_le_min_hedged_of_n_eq_32 hb h32 hnm pkSeed adv hadv).trans
      (min_add_weakKeyMass_le_of_n_eq_32 h32 pkSeed _ _)
  · rw [weakSeedFactor_of_ne h32, mul_one]
    exact shakeStrongAdvantage_pure_le_securityBound_hedged hb hn16 hn hnm pkSeed adv hadv

/-! ## Over the uniform public seed -/

/-- **SLH-DSA over one SHAKE256 oracle.** For `16 ≤ n ≤ 32`, `n ≤ m` and address fields within
their FIPS 205 widths, an adversary against `shakeRomScheme` with the public seed drawn uniformly,
as FIPS 205 prescribes, making at most `qh` queries of the single oracle and `qs` signing queries
makes a strong forgery with probability at most
`byteBound vp qh qs + |A_hon| / 2^256 · weakSeedFactor vp (everySeedBound vp qh qs)`, with
`|A_hon| = honestAdrsCount vp` bounding the honest addresses. The factor is at most one, and
`min 1 (everySeedBound vp qh qs)` at `n = 32`. `optRand` is arbitrary: the bound holds in hedged
and deterministic signing. -/
theorem shakeStrongAdvantage_le_securityBound (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤ byteBound vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBound vp qh qs) := by
  let _ : MeasurableSpace (shakeCore vp).PkSeed := ⊤
  have _ : DiscreteMeasurableSpace (shakeCore vp).PkSeed := ⟨fun _ => trivial⟩
  exact (shakeStrongAdvantage_le_lintegral _ _ (fun pkSeed _ hadv' =>
    shakeStrongAdvantage_pure_le_securityBound_add_weakKeyMass_mul hb hn16 hn hnm pkSeed _ hadv')
      adv hadv).trans (lintegral_add_weakKeyMass_mul_le hn16 _ _)

/-- **SLH-DSA over one SHAKE256 oracle with hedged signing.** For `16 ≤ n ≤ 32`, `n ≤ m` and
address fields within their FIPS 205 widths, with `opt_rand` drawn uniformly at each signature
and the public seed drawn uniformly, as FIPS 205 prescribes, the strong advantage of an adversary
making at most `qh` queries of the single oracle and `qs` signing queries is at most
`byteBoundHedged vp qh qs + |A_hon| / 2^256 · weakSeedFactor vp (everySeedBoundHedged vp qh qs)`,
with `|A_hon| = honestAdrsCount vp` bounding the honest addresses. -/
theorem shakeStrongAdvantage_le_securityBound_hedged (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y)
      ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤ byteBoundHedged vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBoundHedged vp qh qs) := by
  let _ : MeasurableSpace (shakeCore vp).PkSeed := ⊤
  have _ : DiscreteMeasurableSpace (shakeCore vp).PkSeed := ⟨fun _ => trivial⟩
  exact (shakeStrongAdvantage_le_lintegral _ _ (fun pkSeed _ hadv' =>
    shakeStrongAdvantage_pure_le_securityBound_hedged_add_weakKeyMass_mul hb hn16 hn hnm pkSeed _
      hadv') adv hadv).trans (lintegral_add_weakKeyMass_mul_le hn16 _ _)

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`.** At `n = 32`, `n ≤ m` and address fields
within their FIPS 205 widths, the strong advantage of an adversary against `shakeRomScheme` with
the public seed drawn uniformly, making at most `qh` queries of the single oracle and `qs` signing
queries, is at most
`byteBound vp qh qs + |A_hon| / 2^256 · min 1 (everySeedBound vp qh qs)`, with
`|A_hon| = honestAdrsCount vp`. `optRand` is arbitrary. -/
theorem shakeStrongAdvantage_le_securityBound_of_n_eq_32 (hb : CanonicalAddressBounds vp.params)
    (hn : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤
      byteBound vp qh qs + honestAdrsCount vp / 2 ^ 256 * min 1 (everySeedBound vp qh qs) := by
  rw [← weakSeedFactor_of_n_eq_32 hn]
  exact shakeStrongAdvantage_le_securityBound hb (by omega) hn.le hnm adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32` with hedged signing.** At `n = 32`, `n ≤ m` and
address fields within their FIPS 205 widths, with `opt_rand` drawn uniformly at each signature
and the public seed drawn uniformly, the strong advantage of an adversary making at most `qh`
queries of the single oracle and `qs` signing queries is at most
`byteBoundHedged vp qh qs + |A_hon| / 2^256 · min 1 (everySeedBoundHedged vp qh qs)`, with
`|A_hon| = honestAdrsCount vp`. -/
theorem shakeStrongAdvantage_le_securityBound_hedged_of_n_eq_32
    (hb : CanonicalAddressBounds vp.params) (hn : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y)
      ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤ byteBoundHedged vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * min 1 (everySeedBoundHedged vp qh qs) := by
  rw [← weakSeedFactor_of_n_eq_32 hn]
  exact shakeStrongAdvantage_le_securityBound_hedged hb (by omega) hn.le hnm adv hadv

/-! ## At the FIPS 205 parameter sets

Each statement depends on the parameter set only through its parameters, which each SHA-2 set
shares with its SHAKE twin: the SHAKE parameter sets are what they cover. -/

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets, at a public seed.** At the
parameters of every FIPS 205 parameter set, the strong advantage of an adversary against
`shakeRomScheme` at the public seed `pkSeed` making at most `qh` queries of the single oracle and
`qs` signing queries is at most `byteBound p qh qs` plus the weak-key mass of `pkSeed`, in hedged
and deterministic signing. -/
theorem shakeStrongAdvantage_pure_le_securityBound_validatedParams (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤
      byteBound set.validatedParams qh qs + weakKeyMass set.validatedParams pkSeed :=
  shakeStrongAdvantage_pure_le_securityBound
    (fipsApprovedAddressBounds set).toCanonicalAddressBounds
    set.sixteen_le_n set.n_le_32 set.n_le_m pkSeed adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets with hedged signing, at a
public seed.** At the parameters of every FIPS 205 parameter set, with `opt_rand` drawn uniformly
at each signature, the strong advantage at the public seed `pkSeed` is at most
`byteBoundHedged p qh qs` plus the weak-key mass of `pkSeed`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams (set : FipsParameterSet)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤
      byteBoundHedged set.validatedParams qh qs + weakKeyMass set.validatedParams pkSeed :=
  shakeStrongAdvantage_pure_le_securityBound_hedged
    (fipsApprovedAddressBounds set).toCanonicalAddressBounds set.sixteen_le_n set.n_le_32
    set.n_le_m pkSeed adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets with `n = 32`, at every
public seed.** At the parameters of every FIPS 205 parameter set with `n = 32`, the strong
advantage at any public seed `pkSeed` is at most `everySeedBound p qh qs`, in hedged and
deterministic signing. -/
theorem shakeStrongAdvantage_pure_le_securityBound_add_validatedParams (set : FipsParameterSet)
    (hn : set.validatedParams.params.n = 32)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤ everySeedBound set.validatedParams qh qs :=
  (shakeStrongAdvantage_pure_le_min_of_n_eq_32
    (fipsApprovedAddressBounds set).toCanonicalAddressBounds
    hn set.n_le_m pkSeed adv hadv).trans (min_le_right _ _)

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets with `n = 32` and hedged
signing, at every public seed.** At the parameters of every FIPS 205 parameter set with `n = 32`,
with `opt_rand` drawn uniformly at each signature, the strong advantage at any public seed
`pkSeed` is at most `everySeedBoundHedged p qh qs`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams
    (set : FipsParameterSet) (hn : set.validatedParams.params.n = 32)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤ everySeedBoundHedged set.validatedParams qh qs :=
  (shakeStrongAdvantage_pure_le_min_hedged_of_n_eq_32
    (fipsApprovedAddressBounds set).toCanonicalAddressBounds hn set.n_le_m pkSeed adv
    hadv).trans (min_le_right _ _)

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets.** At the parameters of
every FIPS 205 parameter set, the strong advantage of an adversary against `shakeRomScheme` with
the public seed drawn uniformly, making at most `qh` queries of the single oracle and `qs` signing
queries, is at most `byteBound p qh qs + |A_hon| / 2^256 · weakSeedFactor (everySeedBound p qh qs)`,
in hedged and deterministic signing. The factor is one at `n ≠ 32` and `min 1 ε` at `n = 32`. -/
theorem shakeStrongAdvantage_le_securityBound_validatedParams (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams optRand
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤ byteBound set.validatedParams qh qs +
      honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBound set.validatedParams qh qs) :=
  shakeStrongAdvantage_le_securityBound (fipsApprovedAddressBounds set).toCanonicalAddressBounds
    set.sixteen_le_n set.n_le_32 set.n_le_m adv hadv

/-- **SLH-DSA over one SHAKE256 oracle at the FIPS 205 parameter sets with hedged signing.** At
the parameters of every FIPS 205 parameter set, with `opt_rand` drawn uniformly at each signature
and the public seed drawn uniformly, the strong advantage of an adversary making at most `qh`
queries of the single oracle and `qs` signing queries is at most
`byteBoundHedged p qh qs + |A_hon| / 2^256 · weakSeedFactor (everySeedBoundHedged p qh qs)`. The
factor is one at `n ≠ 32` and `min 1 ε` at `n = 32`. -/
theorem shakeStrongAdvantage_le_securityBound_hedged_validatedParams (set : FipsParameterSet)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤ byteBoundHedged set.validatedParams qh qs +
      honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBoundHedged set.validatedParams qh qs) :=
  shakeStrongAdvantage_le_securityBound_hedged
    (fipsApprovedAddressBounds set).toCanonicalAddressBounds
    set.sixteen_le_n set.n_le_32 set.n_le_m adv hadv

/-! ## Existential unforgeability

The forging advantage, a valid signature on a message never signed, is at most the strong one of
the same program (`shakeAdvantage_le_shakeStrongAdvantage`), so each strong bound above is also an
existential one. These are the existential forms of the averaged bounds and of the bounds at the
FIPS 205 parameter sets. -/

/-- The existential form of `shakeStrongAdvantage_pure_le_securityBound`. -/
theorem shakeAdvantage_pure_le_securityBound (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤ byteBound vp qh qs + weakKeyMass vp pkSeed :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound hb hn16 hn hnm pkSeed ⟨adv.main⟩ hadv)

/-- The existential form of `shakeStrongAdvantage_le_securityBound`. -/
theorem shakeAdvantage_le_securityBound (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤ byteBound vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBound vp qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound hb hn16 hn hnm ⟨adv.main⟩ hadv)

/-- The existential form of `shakeStrongAdvantage_le_securityBound_hedged`. -/
theorem shakeAdvantage_le_securityBound_hedged (hb : CanonicalAddressBounds vp.params)
    (hn16 : 16 ≤ vp.params.n) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y)
      ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤ byteBoundHedged vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBoundHedged vp qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound_hedged hb hn16 hn hnm ⟨adv.main⟩ hadv)

/-- The existential form of `shakeStrongAdvantage_pure_le_securityBound_validatedParams`. -/
theorem shakeAdvantage_pure_le_securityBound_validatedParams (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      byteBound set.validatedParams qh qs + weakKeyMass set.validatedParams pkSeed :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_validatedParams set pkSeed ⟨adv.main⟩ hadv)

/-- The existential form of `shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams`. -/
theorem shakeAdvantage_pure_le_securityBound_hedged_validatedParams (set : FipsParameterSet)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      byteBoundHedged set.validatedParams qh qs + weakKeyMass set.validatedParams pkSeed :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams set pkSeed ⟨adv.main⟩ hadv)

/-- The existential form of `shakeStrongAdvantage_pure_le_securityBound_add_validatedParams`. -/
theorem shakeAdvantage_pure_le_securityBound_add_validatedParams (set : FipsParameterSet)
    (hn : set.validatedParams.params.n = 32)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ everySeedBound set.validatedParams qh qs :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_add_validatedParams set hn pkSeed ⟨adv.main⟩ hadv)

/-- The existential form of
`shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams`. -/
theorem shakeAdvantage_pure_le_securityBound_add_hedged_validatedParams (set : FipsParameterSet)
    (hn : set.validatedParams.params.n = 32) (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ everySeedBoundHedged set.validatedParams qh qs :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams set hn pkSeed
      ⟨adv.main⟩ hadv)

/-- The existential form of `shakeStrongAdvantage_le_securityBound_validatedParams`. -/
theorem shakeAdvantage_le_securityBound_validatedParams (set : FipsParameterSet)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ byteBound set.validatedParams qh qs +
      honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBound set.validatedParams qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound_validatedParams set ⟨adv.main⟩ hadv)

/-- The existential form of `shakeStrongAdvantage_le_securityBound_hedged_validatedParams`. -/
theorem shakeAdvantage_le_securityBound_hedged_validatedParams (set : FipsParameterSet)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ byteBoundHedged set.validatedParams qh qs +
      honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBoundHedged set.validatedParams qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound_hedged_validatedParams set ⟨adv.main⟩ hadv)

end SLHDSA.Security
