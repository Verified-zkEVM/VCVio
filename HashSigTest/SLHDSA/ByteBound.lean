/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteBound
public import HashSigTest.SLHDSA.LinkedHazards
public import HashSigTest.SLHDSA.Target
public import HashSigTest.SLHDSA.WeakKeyBound

/-!
# The single-SHAKE256 bound, checked

`HashSig.SLHDSA.Security.ByteBound` bounds the forging advantage against SLH-DSA over one SHAKE256
random oracle on byte strings. This file instantiates it at the parameters of FIPS 205.

* **At the parameters of all 12 sets (the six SHAKE sets)**, for every `opt_rand` source: the
  bound at a public seed and the bound over the uniform public seed, with only the adversary's
  budget as a hypothesis. A SHA-2 set contributes only its parameters, those of its SHAKE twin.
  The averaged bound weights the weak seeds by `|A_hon| / 2^256` times the factor
  `weakSeedFactor`, which is at most one, so it implies the bound with the weak-key term
  `|A_hon| / 2^256` (`add_mul_weakSeedFactor_le`), in both signing modes.
* **Both signing modes** at SLH-DSA-SHAKE-128s (deterministic, `opt_rand = PK.seed`), where the
  factor is one, and SLH-DSA-SHAKE-256f (hedged, `opt_rand` uniform), where it is `min 1 ε`, over
  the uniform public seed, with `honestAdrsCount` evaluated from its closed form.
* **At `n = 32`, a strong public seed**: at SLH-DSA-SHAKE-256s, at the type-`7` seed, which is the
  key of no honest address, the bound at that seed has no weak-key term.
* **At `n = 32`, a weak public seed**: at the all-zero seed of SLH-DSA-SHAKE-256s, the weak-key
  term of the per-seed bound is one, and the bound at every public seed applies instead.
* **Non-vacuity**: with `qh = qs = 2^64`, the right-hand side of the averaged bound is below one at
  SLH-DSA-SHAKE-128s (`byteRhs_128s_lt_one`) and at SLH-DSA-SHAKE-256s and SLH-DSA-SHAKE-256f
  (`averagedByteRhs_256s_lt_one`, `averagedByteRhs_256f_lt_one`, with the sets' numbers in
  `shakeStrongAdvantage_le_256s`, `shakeStrongAdvantage_le_256f`). At those two sets the bound at
  every seed is below one (`everySeedRhs_256s_lt_one`, `everySeedRhs_256f_lt_one`), so the averaged
  right-hand side is strictly below the one with the weak-key term `|A_hon| / 2^256`
  (`averagedByteRhs_256s_lt_byteRhs_256s`, `averagedByteRhs_256f_lt_byteRhs_256f`).
* **Negative control**: the pointwise step behind the factor fails at a weak-key mass of `1 / 2`
  (`not_min_add_le_of_mass_half`), so it needs the mass to be `0` or `1`, as at `n = 32`.
* **Hedged signing** (`opt_rand` uniform): the hedged bounds at a public seed and over the uniform
  public seed at the parameters of all 12 sets (the six SHAKE sets), at SLH-DSA-SHAKE-128s with
  the weak-key term evaluated, and at the strong type-`7` seed of SLH-DSA-SHAKE-256s; the
  averaged hedged right-hand side at SLH-DSA-SHAKE-128s with `qh = qs = 2^64` is below one
  (`hedgedByteRhs_128s_lt_one`), and its honest-signer terms are below those of the bound for
  every `opt_rand` source (`hedged_signerTerms_128s_lt`).
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.ByteBoundTest

open Concrete Security WeakKeyBoundTest

/-! ## At the parameters of all 12 FIPS 205 parameter sets (the six SHAKE sets) -/

/-- The bound at a public seed, at every parameter set and every `opt_rand` source. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ set.validatedParams.params.n : ℕ) +
        weakKeyMass set.validatedParams pkSeed :=
  shakeStrongAdvantage_pure_le_securityBound_validatedParams set pkSeed adv hadv

/-- The weak seeds' share is at most the weak-key term `|A_hon| / 2^256`: the factor of the weak
seeds is at most one. -/
theorem add_mul_weakSeedFactor_le {vp : ValidatedParams} (C w ε : ℝ≥0∞) :
    C + w * weakSeedFactor vp ε ≤ C + w := by
  gcongr
  exact mul_le_of_le_one_right' (weakSeedFactor_le_one ε)

/-- The bound over the uniform public seed, at every parameter set and every `opt_rand` source:
the weak seeds' share is `|A_hon| / 2^256` times the factor of the weak seeds. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams optRand
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ set.validatedParams.params.n : ℕ) +
        honestAdrsCount set.validatedParams / 2 ^ 256 * weakSeedFactor set.validatedParams
          (securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1
              (qh + GeneralScheme.verifyInternalQueryBound set.validatedParams.params) qs +
            2 * ((qs : ℝ≥0∞) + 1) / (256 ^ set.validatedParams.params.n : ℕ)) :=
  shakeStrongAdvantage_le_securityBound_validatedParams set adv hadv

/-- The bound over the uniform public seed implies the bound with the weak-key term
`|A_hon| / 2^256`, at every parameter set and every `opt_rand` source. -/
example (set : FipsParameterSet)
    (optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams optRand
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ set.validatedParams.params.n : ℕ) +
        honestAdrsCount set.validatedParams / 2 ^ 256 :=
  (shakeStrongAdvantage_le_securityBound_validatedParams set adv hadv).trans
    (add_mul_weakSeedFactor_le _ _ _)

/-- The same implication for every validated parameter bundle, in either signing mode. -/
example {vp : ValidatedParams} (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs +
        ((qs : ℝ≥0∞) + 1) / (256 ^ vp.params.n : ℕ) + honestAdrsCount vp / 2 ^ 256 :=
  (shakeStrongAdvantage_le_securityBound hb hn16 hn hnm adv hadv).trans
    (add_mul_weakSeedFactor_le _ _ _)

/-- The hedged implication for every validated parameter bundle. -/
example {vp : ValidatedParams} (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y)
      ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs + 1 / (256 ^ vp.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) ^ 2 +
        honestAdrsCount vp / 2 ^ 256 :=
  (shakeStrongAdvantage_le_securityBound_hedged hb hn16 hn hnm adv hadv).trans
    (add_mul_weakSeedFactor_le _ _ _)

/-! ## Both signing modes, with the weak-key term evaluated -/

/-- SLH-DSA-SHAKE-128s in deterministic signing (`opt_rand = PK.seed`) over the uniform public
seed: `|Y| = 256 ^ 16` and `|A_hon| = 1591788895347057694892543 ≈ 2^80.40`. -/
example (adv : StrongUnforgeableAdversary (shakeRomScheme vp128s
      (fun pk => pure (shakeRandomizerOfPkSeed _ pk.pkSeed)) ($ᵗ (shakeCore vp128s).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp128s adv ≤
      securityBound vp128s.params (256 ^ 16) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / (256 ^ 16 : ℕ) +
        (1591788895347057694892543 : ℕ) / 2 ^ 256 := by
  have h := shakeStrongAdvantage_le_securityBound_validatedParams .SLHDSA_SHAKE_128s adv hadv
  rwa [weakSeedFactor_of_ne (by decide), mul_one, show honestAdrsCount vp128s =
    1591788895347057694892543 by rw [honestAdrsCount_eq]; decide] at h

/-- SLH-DSA-SHAKE-256f in hedged signing (`opt_rand` uniform) over the uniform public seed, by
the bound for every `opt_rand` source: `|Y| = 256 ^ 32`, `V = 17522` and
`|A_hon| = 16195218117312364562383887 ≈ 2^83.74`, the weak seeds weighted by `min 1 ε`. -/
example (adv : StrongUnforgeableAdversary (shakeRomScheme vp256f
      (fun _ => $ᵗ (shakeCore vp256f).Y) ($ᵗ (shakeCore vp256f).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp256f adv ≤
      securityBound vp256f.params (256 ^ 32) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) +
        (16195218117312364562383887 : ℕ) / 2 ^ 256 *
          min 1 (securityBound vp256f.params (256 ^ 32) 2 1 (qh + 17522) qs +
            2 * ((qs : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ)) := by
  have h := shakeStrongAdvantage_le_securityBound_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256f).toCanonicalAddressBounds rfl (by decide) adv
    hadv
  simp only [byteBound, everySeedBound, show vp256f.params.n = 32 from rfl] at h
  rwa [LinkedHazardsTest.verifyInternalQueryBound_256f, show honestAdrsCount vp256f =
    16195218117312364562383887 by rw [honestAdrsCount_eq]; decide] at h

/-! ## At `n = 32`: a strong and a weak public seed -/

/-- **A strong seed.** At SLH-DSA-SHAKE-256s, at the type-`7` public seed, which is the key of no
honest address, the bound has no weak-key term, in either signing mode. -/
example (optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s optRand (pure typeSevenSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp256s adv ≤
      securityBound vp256s.params (256 ^ 32) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) :=
  shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl
    FipsParameterSet.SLHDSA_SHAKE_256s.n_le_m not_isHonestKey_typeSevenSeed adv hadv

/-- **A weak seed.** At SLH-DSA-SHAKE-256s, the weak-key term of the bound at the all-zero public
seed is one: at a weak seed the bound at that seed is trivial. -/
example (optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s optRand (pure zeroSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp256s adv ≤
      securityBound vp256s.params (256 ^ 32) 2 1 qh qs + ((qs : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) +
        1 := by
  have h := shakeStrongAdvantage_pure_le_securityBound_validatedParams .SLHDSA_SHAKE_256s zeroSeed
    adv hadv
  have h1 : weakKeyMass vp256s zeroSeed = 1 :=
    (SampleableType.prEvent_uniformSample_eq_one_iff _).2 isWeakKey_zeroSeed
  simp only [byteBound, show vp256s.params.n = 32 from rfl] at h
  rwa [h1] at h

/-- **A weak seed, bounded.** At SLH-DSA-SHAKE-256s, at the all-zero public seed, the bound at
every public seed applies, with `V = 8444`, in either signing mode. -/
example (optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s optRand (pure zeroSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp256s adv ≤
      securityBound vp256s.params (256 ^ 32) 2 1 (qh + 8444) qs +
        2 * ((qs : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) := by
  have h := shakeStrongAdvantage_pure_le_securityBound_add_validatedParams .SLHDSA_SHAKE_256s rfl
    zeroSeed adv hadv
  simp only [everySeedBound, show vp256s.params.n = 32 from rfl] at h
  rwa [LinkedHazardsTest.verifyInternalQueryBound_256s] at h

/-- The factor of the weak seeds is one at SLH-DSA-SHAKE-128s and `min 1 ε` at
SLH-DSA-SHAKE-256s. -/
example (ε : ℝ≥0∞) : weakSeedFactor vp128s ε = 1 ∧ weakSeedFactor vp256s ε = min 1 ε :=
  ⟨weakSeedFactor_of_ne (by decide) ε, weakSeedFactor_of_n_eq_32 rfl ε⟩

/-- **The pointwise step needs `n = 32`.** At a weak-key mass of `1 / 2`, the smaller of `C` plus
the mass and `D` can exceed `C` plus the mass times `min 1 D`. -/
theorem not_min_add_le_of_mass_half :
    ¬ ∀ C w D : ℝ≥0∞, w ≤ 1 → min (C + w) D ≤ C + w * min 1 D := by
  intro h
  have := h 0 2⁻¹ 2⁻¹ (ENNReal.inv_le_one.2 one_le_two)
  rw [zero_add, zero_add, min_self, min_eq_right (ENNReal.inv_le_one.2 one_le_two)] at this
  have h4 : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ < 2⁻¹ := by
    simpa [ENNReal.div_eq_inv_mul] using ENNReal.half_lt_self (a := 2⁻¹) (by simp) (by simp)
  exact absurd this (not_le.2 h4)

/-- **The averaged bound at SLH-DSA-SHAKE-256s**, at `qh = qs = 2 ^ 64`, with `V = 8444` and
`|A_hon| = 19966778066156452796772607 ≈ 2^84.05`, in either signing mode. -/
theorem shakeStrongAdvantage_le_256s
    {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp256s optRand ($ᵗ (shakeCore vp256s).PkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp256s adv ≤
      securityBound vp256s.params (256 ^ 32) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) +
        (19966778066156452796772607 : ℕ) / 2 ^ 256 *
          min 1 (securityBound vp256s.params (256 ^ 32) 2 1 (2 ^ 64 + 8444) (2 ^ 64) +
            2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ)) := by
  have h := shakeStrongAdvantage_le_securityBound_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv
    hadv
  simp only [byteBound, everySeedBound, show vp256s.params.n = 32 from rfl] at h
  rwa [LinkedHazardsTest.verifyInternalQueryBound_256s, show honestAdrsCount vp256s =
    19966778066156452796772607 by rw [honestAdrsCount_eq]; decide] at h

/-- **The averaged bound at SLH-DSA-SHAKE-256f**, at `qh = qs = 2 ^ 64`, with `V = 17522` and
`|A_hon| = 16195218117312364562383887 ≈ 2^83.74`, in either signing mode. -/
theorem shakeStrongAdvantage_le_256f
    {optRand : PublicKeyCore (shakeCore vp256f) → ProbComp (shakeCore vp256f).Y}
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp256f optRand ($ᵗ (shakeCore vp256f).PkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp256f adv ≤
      securityBound vp256f.params (256 ^ 32) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ) +
        (16195218117312364562383887 : ℕ) / 2 ^ 256 *
          min 1 (securityBound vp256f.params (256 ^ 32) 2 1 (2 ^ 64 + 17522) (2 ^ 64) +
            2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / (256 ^ 32 : ℕ)) := by
  have h := shakeStrongAdvantage_le_securityBound_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256f).toCanonicalAddressBounds rfl (by decide) adv
    hadv
  simp only [byteBound, everySeedBound, show vp256f.params.n = 32 from rfl] at h
  rwa [LinkedHazardsTest.verifyInternalQueryBound_256f, show honestAdrsCount vp256f =
    16195218117312364562383887 by rw [honestAdrsCount_eq]; decide] at h

/-! ## Non-vacuity -/

open TargetTest KeyedHash.Covering in
/-- At SLH-DSA-SHAKE-128s with `qh = qs = 2^64`, the right-hand side of the bound over the uniform
public seed is below one. -/
theorem byteRhs_128s_lt_one :
    securityBound vp128s.params (2 ^ 128) 2 1 (2 ^ 64) (2 ^ 64) +
        ((2 ^ 64 : ℝ≥0∞) + 1) / (2 ^ 128 : ℕ) +
        (honestAdrsCount vp128s : ℝ≥0∞) / 2 ^ 256 < 1 := by
  have hp : vp128s.params.h = 63 ∧ vp128s.params.a = 12 ∧ vp128s.params.k = 14 := by decide
  have hV : GeneralScheme.verifyInternalQueryBound vp128s.params = 3929 := by decide
  have hA : honestAdrsCount vp128s = 1591788895347057694892543 := by
    rw [honestAdrsCount_eq]; decide
  rw [securityBound, hp.1, hp.2.1, hp.2.2, hV, hA]
  have hN : (∑ r ∈ Finset.range 15, ((r + 1) * 2 ^ r * r ^ 14 : ℕ)) < 2 ^ 72 := by decide
  have hw : ((2 ^ 64 : ℕ) : ℝ≥0∞) * (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) ≤ 1 := by
    rw [← mul_div_assoc, ← Nat.cast_mul, ← pow_add]
    exact (ENNReal.div_self (by simp) (by simp)).le
  have hI : weightedTargetCoverBound 63 12 14 (2 ^ 64) (2 ^ 64)
      (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) ≤
        ((2 ^ 72 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 168)⁻¹ := by
    refine (weightedTargetCoverBound_le _ _ _ _ _ _ Nat.one_le_two_pow hw).trans ?_
    simp_rw [term_128s, ← Finset.sum_mul, ← Nat.cast_sum]
    gcongr
  have key : ((2 ^ 64 : ℕ) + 1 : ℝ≥0∞) * (((2 ^ 72 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 168)⁻¹) +
      ((2 : ℕ) * ((2 ^ 64 : ℕ) : ℝ≥0∞) + (((1 + 1) * 3929 : ℕ) : ℝ≥0∞)) *
        (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
      ((2 ^ 64 : ℝ≥0∞) + 1) / (2 ^ 128 : ℕ) +
      ((1591788895347057694892543 : ℕ) : ℝ≥0∞) / 2 ^ 256 < 1 := by
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    norm_num
  refine lt_of_le_of_lt ?_ key
  gcongr

/-- With the bound at every seed below one, the weak seeds' share weighted by it is below the
share in full. -/
theorem add_mul_min_lt_add {F w ε : ℝ≥0∞} (hF : F ≠ ⊤) (hw0 : w ≠ 0) (hwt : w ≠ ⊤)
    (hε : ε < 1) : F + w * min 1 ε < F + w := by
  refine ENNReal.add_lt_add_left hF ?_
  rw [min_eq_right hε.le]
  calc w * ε = ε * w := mul_comm _ _
    _ < 1 * w := ENNReal.mul_lt_mul_left hw0 hwt hε
    _ = w := one_mul w

open TargetTest LinkedHazardsTest KeyedHash.Covering in
/-- At SLH-DSA-SHAKE-256s with `qh = qs = 2^64`, the averaged bound with the weak seeds' share
`|A_hon| / 2^256` in full is below one. -/
theorem byteRhs_256s_lt_one :
    securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((19966778066156452796772607 : ℕ) : ℝ≥0∞)) / 2 ^ 256 < 1 := by
  have hp : vp256s.params.h = 64 ∧ vp256s.params.a = 14 ∧ vp256s.params.k = 22 := by decide
  rw [securityBound, hp.1, hp.2.1, hp.2.2, LinkedHazardsTest.verifyInternalQueryBound_256s]
  have hN : (∑ r ∈ Finset.range 23, (r + 1) * r ^ 22 : ℕ) < 2 ^ 104 := by decide
  have hw : ((2 ^ 64 : ℕ) : ℝ≥0∞) * (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) ≤ 1 := by
    rw [← mul_div_assoc, ← Nat.cast_mul]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast (by norm_num))
  have hI := weightedTargetCoverBound_le_of_le_h (h := 64) (a := 14) (k := 22) le_rfl hw
  have key : ((2 ^ 64 : ℕ) + 1 : ℝ≥0∞) * (((2 ^ 104 : ℕ) : ℝ≥0∞) *
        (((2 : ℝ≥0∞) ^ 14)⁻¹) ^ 22) +
      ((2 : ℕ) * ((2 ^ 64 : ℕ) : ℝ≥0∞) + (((1 + 1) * 8444 : ℕ) : ℝ≥0∞)) *
        (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
      ((19966778066156452796772607 : ℕ) : ℝ≥0∞) / 2 ^ 256 < 1 := by
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    norm_num
  refine lt_of_le_of_lt ?_ key
  gcongr
  exact hI.trans (by gcongr)

open LinkedHazardsTest in
/-- At SLH-DSA-SHAKE-256s with `qh = qs = 2^64`, the bound at every public seed is below one. -/
theorem everySeedRhs_256s_lt_one :
    securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64 + 8444) (2 ^ 64) +
      2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) < 1 := by
  rw [two_mul, ENNReal.add_div, ← add_assoc]
  exact rhs_256s_lt_one

/-- At SLH-DSA-SHAKE-256s with `qh = qs = 2^64`, the right-hand side of the averaged bound is
below that of the bound with the weak seeds' share `|A_hon| / 2^256` in full: the factor of the
weak seeds is the bound at every seed, which is below one. -/
theorem averagedByteRhs_256s_lt_byteRhs_256s :
    securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((19966778066156452796772607 : ℕ) : ℝ≥0∞)) / 2 ^ 256 *
          min 1 (securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64 + 8444) (2 ^ 64) +
            2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) <
      securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((19966778066156452796772607 : ℕ) : ℝ≥0∞)) / 2 ^ 256 :=
  add_mul_min_lt_add (lt_of_le_of_lt le_self_add byteRhs_256s_lt_one).ne_top (by simp)
    (by finiteness) everySeedRhs_256s_lt_one

/-- At SLH-DSA-SHAKE-256s with `qh = qs = 2^64`, the right-hand side of the averaged bound is
below one. -/
theorem averagedByteRhs_256s_lt_one :
    securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((19966778066156452796772607 : ℕ) : ℝ≥0∞)) / 2 ^ 256 *
          min 1 (securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64 + 8444) (2 ^ 64) +
            2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) < 1 :=
  averagedByteRhs_256s_lt_byteRhs_256s.trans byteRhs_256s_lt_one

/-- **The advantage at SLH-DSA-SHAKE-256s over the uniform public seed is below one**, for
`2 ^ 64` hash and `2 ^ 64` signing queries. -/
theorem shakeStrongAdvantage_lt_one_256s_averaged
    {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp256s optRand ($ᵗ (shakeCore vp256s).PkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) : shakeStrongAdvantage vp256s adv < 1 := by
  have h := shakeStrongAdvantage_le_256s adv hadv
  rw [show (256 ^ 32 : ℕ) = 2 ^ 256 by norm_num] at h
  exact lt_of_le_of_lt h averagedByteRhs_256s_lt_one

open TargetTest LinkedHazardsTest KeyedHash.Covering in
/-- At SLH-DSA-SHAKE-256f with `qh = qs = 2^64`, the averaged bound with the weak seeds' share
`|A_hon| / 2^256` in full is below one. -/
theorem byteRhs_256f_lt_one :
    securityBound vp256f.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((16195218117312364562383887 : ℕ) : ℝ≥0∞)) / 2 ^ 256 < 1 := by
  have hp : vp256f.params.h = 68 ∧ vp256f.params.a = 9 ∧ vp256f.params.k = 35 := by decide
  rw [securityBound, hp.1, hp.2.1, hp.2.2, LinkedHazardsTest.verifyInternalQueryBound_256f]
  have hN : (∑ r ∈ Finset.range 36, (r + 1) * r ^ 35 : ℕ) < 2 ^ 186 := by decide
  have hw : ((2 ^ 64 : ℕ) : ℝ≥0∞) * (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) ≤ 1 := by
    rw [← mul_div_assoc, ← Nat.cast_mul]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast (by norm_num))
  have hI := weightedTargetCoverBound_le_of_le_h (h := 68) (a := 9) (k := 35) (by norm_num) hw
  have key : ((2 ^ 64 : ℕ) + 1 : ℝ≥0∞) * (((2 ^ 186 : ℕ) : ℝ≥0∞) *
        (((2 : ℝ≥0∞) ^ 9)⁻¹) ^ 35) +
      ((2 : ℕ) * ((2 ^ 64 : ℕ) : ℝ≥0∞) + (((1 + 1) * 17522 : ℕ) : ℝ≥0∞)) *
        (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
      ((16195218117312364562383887 : ℕ) : ℝ≥0∞) / 2 ^ 256 < 1 := by
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    norm_num
  refine lt_of_le_of_lt ?_ key
  gcongr
  exact hI.trans (by gcongr)

open LinkedHazardsTest in
/-- At SLH-DSA-SHAKE-256f with `qh = qs = 2^64`, the bound at every public seed is below one. -/
theorem everySeedRhs_256f_lt_one :
    securityBound vp256f.params (2 ^ 256) 2 1 (2 ^ 64 + 17522) (2 ^ 64) +
      2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) < 1 := by
  rw [two_mul, ENNReal.add_div, ← add_assoc]
  exact rhs_256f_lt_one

/-- At SLH-DSA-SHAKE-256f with `qh = qs = 2^64`, the right-hand side of the averaged bound is
below that of the bound with the weak seeds' share `|A_hon| / 2^256` in full: the factor of the
weak seeds is the bound at every seed, which is below one. -/
theorem averagedByteRhs_256f_lt_byteRhs_256f :
    securityBound vp256f.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((16195218117312364562383887 : ℕ) : ℝ≥0∞)) / 2 ^ 256 *
          min 1 (securityBound vp256f.params (2 ^ 256) 2 1 (2 ^ 64 + 17522) (2 ^ 64) +
            2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) <
      securityBound vp256f.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((16195218117312364562383887 : ℕ) : ℝ≥0∞)) / 2 ^ 256 :=
  add_mul_min_lt_add (lt_of_le_of_lt le_self_add byteRhs_256f_lt_one).ne_top (by simp)
    (by finiteness) everySeedRhs_256f_lt_one

/-- At SLH-DSA-SHAKE-256f with `qh = qs = 2^64`, the right-hand side of the averaged bound is
below one. -/
theorem averagedByteRhs_256f_lt_one :
    securityBound vp256f.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) +
          (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
        (((16195218117312364562383887 : ℕ) : ℝ≥0∞)) / 2 ^ 256 *
          min 1 (securityBound vp256f.params (2 ^ 256) 2 1 (2 ^ 64 + 17522) (2 ^ 64) +
            2 * (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) < 1 :=
  averagedByteRhs_256f_lt_byteRhs_256f.trans byteRhs_256f_lt_one

/-- **The advantage at SLH-DSA-SHAKE-256f over the uniform public seed is below one**, for
`2 ^ 64` hash and `2 ^ 64` signing queries. -/
theorem shakeStrongAdvantage_lt_one_256f_averaged
    {optRand : PublicKeyCore (shakeCore vp256f) → ProbComp (shakeCore vp256f).Y}
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp256f optRand ($ᵗ (shakeCore vp256f).PkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) : shakeStrongAdvantage vp256f adv < 1 := by
  have h := shakeStrongAdvantage_le_256f adv hadv
  rw [show (256 ^ 32 : ℕ) = 2 ^ 256 by norm_num] at h
  exact lt_of_le_of_lt h averagedByteRhs_256f_lt_one

/-! ## Hedged signing -/

/-- The hedged bound at a public seed, at every parameter set. -/
example (set : FipsParameterSet) (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ => $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        1 / (256 ^ set.validatedParams.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ set.validatedParams.params.n : ℕ) : ℝ≥0∞) ^ 2 +
        weakKeyMass set.validatedParams pkSeed :=
  shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams set pkSeed adv hadv

/-- The hedged bound over the uniform public seed, at every parameter set, implies the hedged
bound with the weak-key term `|A_hon| / 2^256`. -/
example (set : FipsParameterSet)
    (adv : StrongUnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ => $ᵗ (shakeCore set.validatedParams).Y) ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage set.validatedParams adv ≤
      securityBound set.validatedParams.params (256 ^ set.validatedParams.params.n) 2 1 qh qs +
        1 / (256 ^ set.validatedParams.params.n : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ set.validatedParams.params.n : ℕ) : ℝ≥0∞) ^ 2 +
        honestAdrsCount set.validatedParams / 2 ^ 256 :=
  (shakeStrongAdvantage_le_securityBound_hedged_validatedParams set adv hadv).trans
    (add_mul_weakSeedFactor_le _ _ _)

/-- SLH-DSA-SHAKE-128s in hedged signing over the uniform public seed, with the weak-key term
evaluated: `|Y| = 256 ^ 16`. -/
example (adv : StrongUnforgeableAdversary (shakeRomScheme vp128s
      (fun _ => $ᵗ (shakeCore vp128s).Y) ($ᵗ (shakeCore vp128s).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp128s adv ≤
      securityBound vp128s.params (256 ^ 16) 2 1 qh qs + 1 / (256 ^ 16 : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ 16 : ℕ) : ℝ≥0∞) ^ 2 +
        (1591788895347057694892543 : ℕ) / 2 ^ 256 := by
  have h := shakeStrongAdvantage_le_securityBound_hedged_validatedParams .SLHDSA_SHAKE_128s adv hadv
  rwa [weakSeedFactor_of_ne (by decide), mul_one, show honestAdrsCount vp128s =
    1591788895347057694892543 by rw [honestAdrsCount_eq]; decide] at h

/-- **A strong seed in hedged signing.** At SLH-DSA-SHAKE-256s, at the type-`7` public seed, the
hedged bound has no weak-key term. -/
example (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s
      (fun _ => $ᵗ (shakeCore vp256s).Y) (pure typeSevenSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp256s adv ≤
      securityBound vp256s.params (256 ^ 32) 2 1 qh qs + 1 / (256 ^ 32 : ℕ) +
        qs * ((qh : ℝ≥0∞) + qs + 1) / ((256 ^ 32 : ℕ) : ℝ≥0∞) ^ 2 :=
  shakeStrongAdvantage_pure_le_securityBound_hedged_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl
    FipsParameterSet.SLHDSA_SHAKE_256s.n_le_m not_isHonestKey_typeSevenSeed adv hadv

/-- At `qh = qs = 2^64` and `|Y| = 2^128`, the honest-signer terms of the hedged bound,
`1 / |Y| + qs (qh + qs + 1) / |Y|^2`, are below the `(qs + 1) / |Y|` of the bound for every
`opt_rand` source. -/
theorem hedged_signerTerms_128s_lt :
    1 / (2 ^ 128 : ℕ) + (2 ^ 64 : ℝ≥0∞) * ((2 ^ 64 : ℝ≥0∞) + 2 ^ 64 + 1) /
        ((2 ^ 128 : ℕ) : ℝ≥0∞) ^ 2 <
      ((2 ^ 64 : ℝ≥0∞) + 1) / (2 ^ 128 : ℕ) := by
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_add,
    ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow,
    Nat.cast_ofNat, ne_eq, ENNReal.pow_eq_top_iff, ENNReal.ofNat_ne_top, false_and,
    not_false_eq_true, ENNReal.add_eq_top, ENNReal.one_ne_top, or_self]
  norm_num

open TargetTest KeyedHash.Covering in
/-- At SLH-DSA-SHAKE-128s with `qh = qs = 2^64`, the right-hand side of the hedged bound over the
uniform public seed is below one. -/
theorem hedgedByteRhs_128s_lt_one :
    securityBound vp128s.params (2 ^ 128) 2 1 (2 ^ 64) (2 ^ 64) + 1 / (2 ^ 128 : ℕ) +
        (2 ^ 64 : ℝ≥0∞) * ((2 ^ 64 : ℝ≥0∞) + 2 ^ 64 + 1) / ((2 ^ 128 : ℕ) : ℝ≥0∞) ^ 2 +
        (honestAdrsCount vp128s : ℝ≥0∞) / 2 ^ 256 < 1 := by
  refine lt_of_le_of_lt ?_ byteRhs_128s_lt_one
  gcongr ?_ + _
  rw [add_assoc]
  exact add_le_add le_rfl hedged_signerTerms_128s_lt.le

end SLHDSA.ByteBoundTest
