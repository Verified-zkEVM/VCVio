/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSigTest.SLHDSA.ByteBound
public import HashSigTest.SLHDSA.ByteLinkedBound
public import HashSigTest.SLHDSA.CoverageBound

/-!
# Strong unforgeability of SLH-DSA, checked

The headline bounds of `HashSig.SLHDSA.Security.CoverageBound` and
`HashSig.SLHDSA.Security.ByteBound` bound the strong forging advantage: a forgery is a valid pair
of message and signature that the signing oracle never returned. This file checks them.

* **Non-vacuity.** Every strong headline is instantiated at a FIPS 205 parameter set with
  `qh = qs = 2^64`, and its right-hand side is below one: the typed per-seed and averaged bounds
  and the security target at SLH-DSA-SHAKE-128s; the byte-level bounds per seed at the strong
  type-`7` seed of SLH-DSA-SHAKE-256s (weak-key mass zero), in both signing modes; the bound at
  every seed and the smaller of the two at SLH-DSA-SHAKE-256s; and the averaged bounds at
  SLH-DSA-SHAKE-128s, SLH-DSA-SHAKE-256s and SLH-DSA-SHAKE-256f.

* **The existential forms.** Each existential headline is re-derived from its strong form through
  `unforgeableAdvantage_le_strongUnforgeableAdvantage` or `shakeAdvantage_le_shakeStrongAdvantage`,
  at the same right-hand side.
* **Negative control.** A transcript whose forged pair is a logged pair is no strong win, whatever
  its verdict; one whose message is logged with another signature is a strong win and no
  existential win.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.StrongUnforgeabilityTest

open Concrete Security WeakKeyBoundTest TargetTest LinkedHazardsTest ByteBoundTest

/-! ## Arithmetic at the parameter sets -/

theorem natCard_Y_vp128s : Nat.card (shakeCore vp128s).Y = 2 ^ 128 := by
  rw [natCard_shakePrimitives_y]
  change 256 ^ 16 = 2 ^ 128
  norm_num

/-- At SLH-DSA-SHAKE-128s, `securityBound` with `qh = qs = 2^64` is below one. -/
theorem securityBound_vp128s_lt_one :
    securityBound vp128s.params (2 ^ 128) 2 1 (2 ^ 64) (2 ^ 64) < 1 :=
  lt_of_le_of_lt (le_self_add.trans le_self_add) byteRhs_128s_lt_one

/-- The hedged signer terms at `n = 32` and `qh = qs = 2^64` are below the deterministic ones. -/
theorem hedged_signerTerms_256_le {qh : ℕ} (hqh : qh ≤ 2 ^ 65) :
    1 / (2 ^ 256 : ℕ) + ((2 ^ 64 : ℕ) : ℝ≥0∞) * ((qh : ℝ≥0∞) + ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) /
        ((2 ^ 256 : ℕ) : ℝ≥0∞) ^ 2 ≤
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
  have hq : (qh : ℝ≥0∞) ≤ 2 ^ 65 := by exact_mod_cast hqh
  calc 1 / (2 ^ 256 : ℕ) + ((2 ^ 64 : ℕ) : ℝ≥0∞) * ((qh : ℝ≥0∞) + ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) /
        ((2 ^ 256 : ℕ) : ℝ≥0∞) ^ 2
      ≤ 1 / (2 ^ 256 : ℕ) + ((2 ^ 64 : ℕ) : ℝ≥0∞) * (2 ^ 65 + ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) /
        ((2 ^ 256 : ℕ) : ℝ≥0∞) ^ 2 := by gcongr
    _ ≤ (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_add,
        ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow,
        Nat.cast_ofNat, ne_eq, ENNReal.pow_eq_top_iff, ENNReal.ofNat_ne_top, false_and,
        not_false_eq_true, ENNReal.add_eq_top, ENNReal.one_ne_top, or_self]
      norm_num

/-! ## The three-oracle model -/

section Typed

variable (e : (shakeCore vp128s).SkSeed ≃ (shakeCore vp128s).Y)
  (optRand : PublicKeyCore (shakeCore vp128s) → ProbComp (shakeCore vp128s).Y)

/-- **The typed strong bound per seed at SLH-DSA-SHAKE-128s is below one.** -/
theorem strongUnforgeableAdvantage_pure_lt_one_128s (pkSeed : (shakeCore vp128s).PkSeed)
    {adv : StrongUnforgeableAdversary (romScheme (shakeCore vp128s) e optRand (pure pkSeed))}
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec (shakeCore vp128s))) adv < 1 := by
  have h := strongUnforgeableAdvantage_romScheme_pure_le_securityBound
    (shakePrimitives_byteLaws _) (keyDiscipline_shakePrimitives _
      (fipsApprovedAddressBounds .SLHDSA_SHAKE_128s).toCanonicalAddressBounds) le_rfl e optRand
    pkSeed hadv
  rw [natCard_Y_vp128s] at h
  exact h.trans_lt securityBound_vp128s_lt_one

/-- **The typed strong bound averaged over the uniform public seed at SLH-DSA-SHAKE-128s is below
one.** -/
theorem strongUnforgeableAdvantage_lt_one_128s
    (adv : StrongUnforgeableAdversary
      (romScheme (shakeCore vp128s) e optRand ($ᵗ (shakeCore vp128s).PkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec (shakeCore vp128s))) adv < 1 := by
  have h := strongUnforgeableAdvantage_romScheme_le_securityBound
    (shakePrimitives_byteLaws _) (keyDiscipline_shakePrimitives _
      (fipsApprovedAddressBounds .SLHDSA_SHAKE_128s).toCanonicalAddressBounds) le_rfl e optRand
    _ adv hadv
  rw [natCard_Y_vp128s] at h
  exact h.trans_lt securityBound_vp128s_lt_one

/-- **The security target at SLH-DSA-SHAKE-128s bounds the strong advantage below one.** -/
example (pkSeed : (shakeCore vp128s).PkSeed)
    (adv : StrongUnforgeableAdversary (romScheme (shakeCore vp128s) e optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec (shakeCore vp128s))) adv < 1 := by
  have h := CoverageBoundTest.securityTarget_shake_fips .SLHDSA_SHAKE_128s e optRand pkSeed adv
    _ _ hadv
  rw [natCard_Y_vp128s] at h
  exact h.trans_lt securityBound_vp128s_lt_one

end Typed

/-! ## One SHAKE256 oracle, per public seed -/

section PerSeed

variable {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}

theorem n_vp256s : vp256s.params.n = 32 := rfl

theorem weakKeyMass_typeSevenSeed : weakKeyMass vp256s typeSevenSeed = 0 :=
  weakKeyMass_eq_zero_of_n_eq_32 rfl not_isHonestKey_typeSevenSeed

/-- The deterministic per-seed right-hand side at SLH-DSA-SHAKE-256s is below one. -/
theorem pureRhs_256s_lt_one :
    securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) +
      (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) < 1 :=
  lt_of_le_of_lt le_self_add byteRhs_256s_lt_one

/-- The hedged per-seed right-hand side at SLH-DSA-SHAKE-256s is below one. -/
theorem hedgedPureRhs_256s_lt_one :
    securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64) (2 ^ 64) + 1 / (2 ^ 256 : ℕ) +
      ((2 ^ 64 : ℕ) : ℝ≥0∞) * (((2 ^ 64 : ℕ) : ℝ≥0∞) + ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) /
        ((2 ^ 256 : ℕ) : ℝ≥0∞) ^ 2 < 1 :=
  lt_of_le_of_lt (by
    rw [add_assoc]
    gcongr
    exact hedged_signerTerms_256_le (by norm_num)) pureRhs_256s_lt_one

/-- **Per seed, the strong bound at the type-`7` seed of SLH-DSA-SHAKE-256s is below one**, by the
bound at a public seed, at a seed of weak-key mass zero, at a strong seed and at the parameter set,
in both signing modes. -/
example (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s optRand (pure typeSevenSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp256s adv < 1 ∧ shakeStrongAdvantage vp256s adv < 1 ∧
      shakeStrongAdvantage vp256s adv < 1 ∧ shakeStrongAdvantage vp256s adv < 1 := by
  have hb := (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds
  have h₁ := shakeStrongAdvantage_pure_le_securityBound hb (by decide) (by decide) (by decide)
    typeSevenSeed adv hadv
  have h₂ := shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero hb (by decide)
    (by decide) (by decide) weakKeyMass_typeSevenSeed adv hadv
  have h₃ := shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32 hb rfl (by decide)
    not_isHonestKey_typeSevenSeed adv hadv
  have h₄ := shakeStrongAdvantage_pure_le_securityBound_validatedParams .SLHDSA_SHAKE_256s
    typeSevenSeed adv hadv
  simp only [byteBound, show vp256s.params.n = 32 from rfl] at h₁ h₂ h₃ h₄
  rw [weakKeyMass_typeSevenSeed, add_zero] at h₁ h₄
  simp only [show (256 ^ 32 : ℕ) = 2 ^ 256 by norm_num] at h₁ h₂ h₃ h₄
  exact ⟨h₁.trans_lt pureRhs_256s_lt_one, h₂.trans_lt pureRhs_256s_lt_one,
    h₃.trans_lt pureRhs_256s_lt_one, h₄.trans_lt pureRhs_256s_lt_one⟩

/-- **Per seed, in hedged signing, the strong bound at the type-`7` seed of SLH-DSA-SHAKE-256s is
below one**, by the bound for an `opt_rand` source that rarely equals the seed, the hedged bound at
a public seed, at a strong seed and at the parameter set. -/
example (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp256s (fun _ ↦ $ᵗ (shakeCore vp256s).Y) (pure typeSevenSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp256s adv < 1 ∧ shakeStrongAdvantage vp256s adv < 1 ∧
      shakeStrongAdvantage vp256s adv < 1 ∧ shakeStrongAdvantage vp256s adv < 1 := by
  have hb := (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds
  have h₁ := shakeStrongAdvantage_pure_le_securityBound_of_prEvent_optRand_le hb (by decide)
    (by decide) (by decide) typeSevenSeed (ε := (Nat.card (shakeCore vp256s).Y : ℝ≥0∞)⁻¹)
    (fun _ ↦ (SampleableType.prEvent_uniformSample_eq_singleton_natCard _).le) adv hadv
  have h₂ := shakeStrongAdvantage_pure_le_securityBound_hedged hb (by decide) (by decide)
    (by decide) typeSevenSeed adv hadv
  have h₃ := shakeStrongAdvantage_pure_le_securityBound_hedged_of_n_eq_32 hb rfl (by decide)
    not_isHonestKey_typeSevenSeed adv hadv
  have h₄ := shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams .SLHDSA_SHAKE_256s
    typeSevenSeed adv hadv
  rw [weakKeyMass_typeSevenSeed, add_zero] at h₁ h₂ h₄
  rw [ByteLinkedBoundTest.natCard_Y_vp256s] at h₁
  simp only [n_vp256s, show (256 ^ 32 : ℕ) = 2 ^ 256 by norm_num] at h₁ h₂ h₃ h₄
  refine ⟨h₁.trans_lt (lt_of_le_of_lt (le_of_eq ?_) hedgedPureRhs_256s_lt_one),
    h₂.trans_lt hedgedPureRhs_256s_lt_one, h₃.trans_lt hedgedPureRhs_256s_lt_one,
    h₄.trans_lt hedgedPureRhs_256s_lt_one⟩
  simp only [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
  push_cast
  ring

/-- **Per seed, with the weak seeds' factor, the strong bound at the type-`7` seed of
SLH-DSA-SHAKE-256s is below one**, in both signing modes. -/
example (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s optRand (pure typeSevenSeed)))
    (adv' : StrongUnforgeableAdversary
      (shakeRomScheme vp256s (fun _ ↦ $ᵗ (shakeCore vp256s).Y) (pure typeSevenSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) (hadv' : adv'.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp256s adv < 1 ∧ shakeStrongAdvantage vp256s adv' < 1 := by
  have hb := (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds
  have h₁ := shakeStrongAdvantage_pure_le_securityBound_add_weakKeyMass_mul hb (by decide)
    (by decide) (by decide) typeSevenSeed adv hadv
  have h₂ := shakeStrongAdvantage_pure_le_securityBound_hedged_add_weakKeyMass_mul hb (by decide)
    (by decide) (by decide) typeSevenSeed adv' hadv'
  simp only [byteBound, byteBoundHedged, everySeedBound, everySeedBoundHedged,
    show vp256s.params.n = 32 from rfl] at h₁ h₂
  rw [weakKeyMass_typeSevenSeed, zero_mul, add_zero] at h₁ h₂
  simp only [show (256 ^ 32 : ℕ) = 2 ^ 256 by norm_num] at h₁ h₂
  exact ⟨h₁.trans_lt pureRhs_256s_lt_one, h₂.trans_lt hedgedPureRhs_256s_lt_one⟩

end PerSeed

/-! ## One SHAKE256 oracle at every public seed, `n = 32` -/

section EverySeed

/-- The hedged every-seed right-hand side at SLH-DSA-SHAKE-256s is below one. -/
theorem hedgedEverySeedRhs_256s_lt_one :
    securityBound vp256s.params (2 ^ 256) 2 1 (2 ^ 64 + 8444) (2 ^ 64) + 1 / (2 ^ 256 : ℕ) +
        ((2 ^ 64 : ℕ) : ℝ≥0∞) * (((2 ^ 64 + 8444 : ℕ) : ℝ≥0∞) + ((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) /
          ((2 ^ 256 : ℕ) : ℝ≥0∞) ^ 2 +
        (((2 ^ 64 : ℕ) : ℝ≥0∞) + 1) / ((2 ^ 256 : ℕ) : ℝ≥0∞) < 1 :=
  lt_of_le_of_lt (by
    rw [add_assoc (securityBound _ _ _ _ _ _)]
    gcongr
    exact hedged_signerTerms_256_le (by norm_num)) rhs_256s_lt_one

/-- **At every public seed, the strong bound at SLH-DSA-SHAKE-256s is below one**, by the bound at
every seed and the smaller of the two bounds, in deterministic signing, and at the weak all-zero
seed in particular. -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    (pkSeed : (shakeCore vp256s).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp256s optRand (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp256s adv < 1 ∧ shakeStrongAdvantage vp256s adv < 1 ∧
      shakeStrongAdvantage vp256s adv < 1 := by
  have hb := (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds
  have h₁ := shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32 hb rfl (by decide) adv hadv
  have h₂ := shakeStrongAdvantage_pure_le_securityBound_add_validatedParams .SLHDSA_SHAKE_256s rfl
    pkSeed adv hadv
  have h₃ := (shakeStrongAdvantage_pure_le_min_of_n_eq_32 hb rfl (by decide) pkSeed adv
    hadv).trans (min_le_right _ _)
  simp only [everySeedBound, show vp256s.params.n = 32 from rfl] at h₂ h₃
  rw [ByteLinkedBoundTest.natCard_Y_vp256s, verifyInternalQueryBound_256s] at h₁
  rw [verifyInternalQueryBound_256s] at h₂ h₃
  simp only [show (256 ^ 32 : ℕ) = 2 ^ 256 by norm_num] at h₂ h₃
  exact ⟨h₁.trans_lt rhs_256s_lt_one, h₂.trans_lt everySeedRhs_256s_lt_one,
    h₃.trans_lt everySeedRhs_256s_lt_one⟩

/-- **At every public seed, in hedged signing, the strong bound at SLH-DSA-SHAKE-256s is below
one**, by the hedged bound at every seed, at the parameter set and the smaller of the two. -/
example (pkSeed : (shakeCore vp256s).PkSeed)
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp256s (fun _ ↦ $ᵗ (shakeCore vp256s).Y) (pure pkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp256s adv < 1 ∧ shakeStrongAdvantage vp256s adv < 1 ∧
      shakeStrongAdvantage vp256s adv < 1 := by
  have hb := (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds
  have h₁ := shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32_hedged hb rfl (by decide)
    adv hadv (ε := (Nat.card (shakeCore vp256s).Y : ℝ≥0∞)⁻¹)
    (fun _ ↦ (SampleableType.prEvent_uniformSample_eq_singleton_natCard _).le)
  have h₂ := shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams
    .SLHDSA_SHAKE_256s rfl pkSeed adv hadv
  have h₃ := (shakeStrongAdvantage_pure_le_min_hedged_of_n_eq_32 hb rfl (by decide) pkSeed adv
    hadv).trans (min_le_right _ _)
  simp only [byteBoundHedged, everySeedBoundHedged, show vp256s.params.n = 32 from rfl] at h₂ h₃
  rw [ByteLinkedBoundTest.natCard_Y_vp256s, verifyInternalQueryBound_256s] at h₁
  rw [verifyInternalQueryBound_256s] at h₂ h₃
  simp only [show (256 ^ 32 : ℕ) = 2 ^ 256 by norm_num] at h₂ h₃
  refine ⟨h₁.trans_lt (lt_of_le_of_lt (le_of_eq ?_) hedgedEverySeedRhs_256s_lt_one),
    h₂.trans_lt hedgedEverySeedRhs_256s_lt_one, h₃.trans_lt hedgedEverySeedRhs_256s_lt_one⟩
  simp only [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
  ring

end EverySeed

/-! ## One SHAKE256 oracle over the uniform public seed -/

section Averaged

/-- **Over the uniform public seed, the strong bound at SLH-DSA-SHAKE-128s is below one**, by the
averaged bound and the averaged bound at the parameter set, in both signing modes. -/
example {optRand : PublicKeyCore (shakeCore vp128s) → ProbComp (shakeCore vp128s).Y}
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp128s optRand ($ᵗ (shakeCore vp128s).PkSeed)))
    (adv' : StrongUnforgeableAdversary (shakeRomScheme vp128s (fun _ ↦ $ᵗ (shakeCore vp128s).Y)
      ($ᵗ (shakeCore vp128s).PkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) (hadv' : adv'.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp128s adv < 1 ∧ shakeStrongAdvantage vp128s adv < 1 ∧
      shakeStrongAdvantage vp128s adv' < 1 ∧ shakeStrongAdvantage vp128s adv' < 1 := by
  have hb := (fipsApprovedAddressBounds .SLHDSA_SHAKE_128s).toCanonicalAddressBounds
  have h₁ := (shakeStrongAdvantage_le_securityBound hb (by decide) (by decide) (by decide) adv
    hadv).trans (add_mul_weakSeedFactor_le _ _ _)
  have h₂ := (shakeStrongAdvantage_le_securityBound_validatedParams .SLHDSA_SHAKE_128s adv
    hadv).trans (add_mul_weakSeedFactor_le _ _ _)
  have h₃ := (shakeStrongAdvantage_le_securityBound_hedged hb (by decide) (by decide) (by decide)
    adv' hadv').trans (add_mul_weakSeedFactor_le _ _ _)
  have h₄ := (shakeStrongAdvantage_le_securityBound_hedged_validatedParams .SLHDSA_SHAKE_128s
    adv' hadv').trans (add_mul_weakSeedFactor_le _ _ _)
  have hd := byteRhs_128s_lt_one
  have hh := hedgedByteRhs_128s_lt_one
  simp only [byteBound, byteBoundHedged] at h₁ h₂ h₃ h₄
  simp only [show vp128s.params.n = 16 from rfl, show (256 ^ 16 : ℕ) = 2 ^ 128 by norm_num,
    Nat.cast_pow, Nat.cast_ofNat] at h₁ h₂ h₃ h₄ hd hh
  exact ⟨h₁.trans_lt hd, h₂.trans_lt hd, h₃.trans_lt hh, h₄.trans_lt hh⟩

/-- **Over the uniform public seed, the strong bound at `n = 32` is below one**, at
SLH-DSA-SHAKE-256s and SLH-DSA-SHAKE-256f, and in hedged signing at SLH-DSA-SHAKE-256s. -/
example {optRand : PublicKeyCore (shakeCore vp256s) → ProbComp (shakeCore vp256s).Y}
    {optRand' : PublicKeyCore (shakeCore vp256f) → ProbComp (shakeCore vp256f).Y}
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp256s optRand ($ᵗ (shakeCore vp256s).PkSeed)))
    (adv' : StrongUnforgeableAdversary
      (shakeRomScheme vp256f optRand' ($ᵗ (shakeCore vp256f).PkSeed)))
    (adv'' : StrongUnforgeableAdversary (shakeRomScheme vp256s (fun _ ↦ $ᵗ (shakeCore vp256s).Y)
      ($ᵗ (shakeCore vp256s).PkSeed)))
    (hadv : adv.RomQueryBound (2 ^ 64) (2 ^ 64)) (hadv' : adv'.RomQueryBound (2 ^ 64) (2 ^ 64))
    (hadv'' : adv''.RomQueryBound (2 ^ 64) (2 ^ 64)) :
    shakeStrongAdvantage vp256s adv < 1 ∧ shakeStrongAdvantage vp256f adv' < 1 ∧
      shakeStrongAdvantage vp256s adv'' < 1 := by
  have h₁ := shakeStrongAdvantage_le_securityBound_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv
    hadv
  have h₂ := shakeStrongAdvantage_le_securityBound_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256f).toCanonicalAddressBounds rfl (by decide) adv'
    hadv'
  have h₃ := shakeStrongAdvantage_le_securityBound_hedged_of_n_eq_32
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds rfl (by decide) adv''
    hadv''
  simp only [byteBound, byteBoundHedged, everySeedBound, everySeedBoundHedged,
    show vp256s.params.n = 32 from rfl, show vp256f.params.n = 32 from rfl] at h₁ h₂ h₃
  rw [verifyInternalQueryBound_256s, show honestAdrsCount vp256s =
    19966778066156452796772607 by rw [honestAdrsCount_eq]; decide] at h₁ h₃
  rw [LinkedHazardsTest.verifyInternalQueryBound_256f, show honestAdrsCount vp256f =
    16195218117312364562383887 by rw [honestAdrsCount_eq]; decide] at h₂
  simp only [show (256 ^ 32 : ℕ) = 2 ^ 256 by norm_num] at h₁ h₂ h₃
  refine ⟨h₁.trans_lt averagedByteRhs_256s_lt_one, h₂.trans_lt averagedByteRhs_256f_lt_one,
    h₃.trans_lt (lt_of_le_of_lt ?_ byteRhs_256s_lt_one)⟩
  rw [add_assoc (securityBound _ _ _ _ _ _)]
  gcongr
  · exact hedged_signerTerms_256_le (by norm_num)
  · exact mul_le_of_le_one_right' (min_le_left _ _)

end Averaged

/-! ## The existential forms, re-derived -/

section Existential

variable {vp : ValidatedParams}

/-- The existential averaged target at a SHAKE bundle, from the strong one. -/
example (hb : CanonicalAddressBounds vp.params) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand pkSeedDist)) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec (shakeCore vp))) adv ≤
      securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1 qh qs :=
  (unforgeableAdvantage_le_strongUnforgeableAdvantage _ adv).trans
    (strongUnforgeableAdvantage_romScheme_le _ (CoverageBoundTest.securityTarget_shake vp hb e
      optRand) pkSeedDist ⟨adv.main⟩ hadv)

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}

/-- The existential bound at a public seed, from the strong one. -/
example (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤ byteBound vp qh qs + weakKeyMass vp pkSeed :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound hb hn16 hn hnm pkSeed ⟨adv.main⟩ hadv)

/-- The existential averaged bound, from the strong one. -/
example (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤ byteBound vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBound vp qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound hb hn16 hn hnm ⟨adv.main⟩ hadv)

/-- The existential averaged bound in hedged signing, from the strong one. -/
example (hb : CanonicalAddressBounds vp.params) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (adv : UnforgeableAdversary (shakeRomScheme vp (fun _ ↦ $ᵗ (shakeCore vp).Y)
      ($ᵗ (shakeCore vp).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage vp adv ≤ byteBoundHedged vp qh qs +
      honestAdrsCount vp / 2 ^ 256 * weakSeedFactor vp (everySeedBoundHedged vp qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound_hedged hb hn16 hn hnm ⟨adv.main⟩ hadv)

variable (set : FipsParameterSet)

/-- The existential bound at a public seed at the parameter sets, from the strong one. -/
example {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      byteBound set.validatedParams qh qs + weakKeyMass set.validatedParams pkSeed :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_validatedParams set pkSeed ⟨adv.main⟩ hadv)

/-- The existential hedged bound at a public seed at the parameter sets, from the strong one. -/
example (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤
      byteBoundHedged set.validatedParams qh qs + weakKeyMass set.validatedParams pkSeed :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams set pkSeed ⟨adv.main⟩ hadv)

/-- The existential every-seed bound at the parameter sets with `n = 32`, from the strong one. -/
example (hn : set.validatedParams.params.n = 32)
    {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ everySeedBound set.validatedParams qh qs :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_add_validatedParams set hn pkSeed ⟨adv.main⟩ hadv)

/-- The existential hedged every-seed bound at the parameter sets with `n = 32`, from the strong
one. -/
example (hn : set.validatedParams.params.n = 32) (pkSeed : (shakeCore set.validatedParams).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) (pure pkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ everySeedBoundHedged set.validatedParams qh qs :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams set hn pkSeed
      ⟨adv.main⟩ hadv)

/-- The existential averaged bound at the parameter sets, from the strong one. -/
example {optRand : PublicKeyCore (shakeCore set.validatedParams) →
      ProbComp (shakeCore set.validatedParams).Y}
    (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams optRand
      ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ byteBound set.validatedParams qh qs +
      honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBound set.validatedParams qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound_validatedParams set ⟨adv.main⟩ hadv)

/-- The existential averaged hedged bound at the parameter sets, from the strong one. -/
example (adv : UnforgeableAdversary (shakeRomScheme set.validatedParams
      (fun _ ↦ $ᵗ (shakeCore set.validatedParams).Y) ($ᵗ (shakeCore set.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    shakeAdvantage set.validatedParams adv ≤ byteBoundHedged set.validatedParams qh qs +
      honestAdrsCount set.validatedParams / 2 ^ 256 *
        weakSeedFactor set.validatedParams (everySeedBoundHedged set.validatedParams qh qs) :=
  (shakeAdvantage_le_shakeStrongAdvantage adv).trans
    (shakeStrongAdvantage_le_securityBound_hedged_validatedParams set ⟨adv.main⟩ hadv)

end Existential

/-! ## Negative control: a replayed pair is not a strong win -/

/-- A transcript whose forged pair of message and signature is a logged pair is no strong win,
whatever its verification verdict. -/
theorem strongWins_eq_false_of_mem_log {M PK SK S : Type} (o : UnforgeableTranscript M PK SK S)
    (h : ⟨o.msg, o.sig⟩ ∈ o.log) : o.strongWins = false := by
  cases hw : o.strongWins
  · rfl
  · exact absurd h ((o.strongWins_eq_true_iff.1 hw).1)

/-- A transcript that signs message `0` as `1`. -/
def signedOnce (σ : ℕ) : UnforgeableTranscript ℕ Unit Unit ℕ :=
  ⟨(), (), [⟨0, 1⟩], 0, σ, true⟩

/-- Replaying the logged pair `(0, 1)` with an accepting verdict is not a strong win. -/
example : (signedOnce 1).strongWins = false :=
  strongWins_eq_false_of_mem_log _ (by simp [signedOnce])

/-- A second, accepted signature `2` on the logged message `0` is a strong win but no existential
win: the strong notion counts it. -/
example : (signedOnce 2).strongWins = true ∧ (signedOnce 2).wins = false := by
  refine ⟨(UnforgeableTranscript.strongWins_eq_true_iff _).2 ⟨by simp [signedOnce], rfl⟩, ?_⟩
  cases hw : (signedOnce 2).wins
  · rfl
  · exact absurd ((UnforgeableTranscript.wins_eq_true_iff _).1 hw).1 (by simp [signedOnce])

end SLHDSA.StrongUnforgeabilityTest
