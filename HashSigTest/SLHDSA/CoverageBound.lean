/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageBound
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSigTest.SLHDSA.Bundles

/-!
# The security target at the FIPS 205 bundles

At every SHAKE bundle whose address fields fit their FIPS 205 widths, and at every FIPS SHA-2
bundle whose compressed address fields fit theirs, SLH-DSA in the three-oracle random-oracle model
meets the security target at `c = 2` and `r = 1`, in both signing modes. The node type and the
message-`PRF` key type of either bundle are both `n`-byte strings, so `|Y| ≤ |SK.prf|` holds with
equality, and `|Y| = 256 ^ n`.

* `securityTarget_shake`, `securityTarget_sha2`: the target, per public seed.
* `unforgeableAdvantage_shake_le`, `unforgeableAdvantage_sha2_le`: the bound for every
  distribution of the public seed, with `|Y|` evaluated as `256 ^ n`.
* At SLH-DSA-SHAKE-128s, the bound for the uniform public seed of FIPS 205.
* At every bundle, the coverage term of the ideal hidden-seed game is bounded by the weighted
  coverage term.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.CoverageBoundTest

open Concrete Security BundleTest

/-- **The target at a SHAKE bundle.** At every SHAKE bundle whose address fields fit their widths,
SLH-DSA in the random-oracle model meets the security target at `c = 2` and `r = 1`. -/
theorem securityTarget_shake (vp : ValidatedParams) (hb : CanonicalAddressBounds vp.params)
    (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y) :
    SecurityTarget (shakeCore vp) e optRand 2 1 :=
  securityTarget_two_one (shakePrimitives_byteLaws vp.params) (keyDiscipline_shakePrimitives vp hb)
    le_rfl e optRand

/-- **The target at a FIPS SHA-2 bundle.** At every FIPS SHA-2 bundle whose address fields fit
their widths, including the two compressed widths of `ADRSc`, SLH-DSA in the random-oracle model
meets the security target at `c = 2` and `r = 1`. -/
theorem securityTarget_sha2 (vp : ValidatedParams) (hb : ApprovedAddressBounds vp.params)
    (e : (sha2Core vp).SkSeed ≃ (sha2Core vp).Y)
    (optRand : PublicKeyCore (sha2Core vp) → ProbComp (sha2Core vp).Y) :
    SecurityTarget (sha2Core vp) e optRand 2 1 :=
  securityTarget_two_one (sha2Primitives_byteLaws vp.params) (keyDiscipline_sha2Primitives vp hb)
    le_rfl e optRand

/-- At every SHAKE bundle whose address fields fit their widths, a forger making at most `qh` hash
queries and `qs` signing queries, with the public seed drawn from any distribution, forges with
probability at most `securityBound vp.params (256 ^ n) 2 1 qh qs`. -/
theorem unforgeableAdvantage_shake_le (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeedDist : ProbComp (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand pkSeedDist)) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec (shakeCore vp))) adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs := by
  rw [← natCard_shakePrimitives_y]
  exact unforgeableAdvantage_romScheme_le_securityBound (shakePrimitives_byteLaws vp.params)
    (keyDiscipline_shakePrimitives vp hb) le_rfl e optRand pkSeedDist adv hadv

/-- At every FIPS SHA-2 bundle whose address fields fit their widths, a forger making at most `qh`
hash queries and `qs` signing queries, with the public seed drawn from any distribution, forges
with probability at most `securityBound vp.params (256 ^ n) 2 1 qh qs`. -/
theorem unforgeableAdvantage_sha2_le (vp : ValidatedParams)
    (hb : ApprovedAddressBounds vp.params) (e : (sha2Core vp).SkSeed ≃ (sha2Core vp).Y)
    (optRand : PublicKeyCore (sha2Core vp) → ProbComp (sha2Core vp).Y)
    (pkSeedDist : ProbComp (sha2Core vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (sha2Core vp) e optRand pkSeedDist)) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec (sha2Core vp))) adv ≤
      securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs := by
  rw [← natCard_sha2Primitives_y]
  exact unforgeableAdvantage_romScheme_le_securityBound (sha2Primitives_byteLaws vp.params)
    (keyDiscipline_sha2Primitives vp hb) le_rfl e optRand pkSeedDist adv hadv

/-- At SLH-DSA-SHAKE-128s, with the public seed drawn uniformly as FIPS 205 prescribes, a forger
making at most `qh` hash queries and `qs` signing queries forges with probability at most
`securityBound` at `|Y| = 256 ^ 16`, `c = 2` and `r = 1`. -/
example (e : (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).SkSeed ≃
      (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).Y)
    (optRand : PublicKeyCore (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) →
      ProbComp (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).Y)
    (adv : UnforgeableAdversary (romScheme (shakeCore
      FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) e optRand
        ($ᵗ (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).PkSeed)))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec (shakeCore
        FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams))) adv ≤
      securityBound FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams.params (256 ^ 16) 2 1 qh
        qs :=
  unforgeableAdvantage_shake_le _
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_128s).toCanonicalAddressBounds e optRand _ adv hadv

/-- At every SHAKE bundle, the coverage term of the ideal hidden-seed game at a fixed public seed
is at most `(qh + 1) · weightedTargetCoverBound h a k qs qh (qs / 256 ^ n)`. -/
example (vp : ValidatedParams) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
        RunItsrCovered (shakeCore vp) (DeriveOutcome.fill (shakeCore vp) w.1 w.2.1,
          (secretEncoding (shakeCore vp) e pkSeed).merge w.1 w.2.2)] ≤
      ((qh : ℝ≥0∞) + 1) * KeyedHash.Covering.weightedTargetCoverBound vp.params.h vp.params.a
        vp.params.k qs qh ((qs : ℝ≥0∞) / ((256 ^ vp.params.n : ℕ) : ℝ≥0∞)) := by
  rw [← natCard_shakePrimitives_y]
  exact prEvent_idealDraw_runItsrCovered_le e optRand pkSeed hadv

end SLHDSA.CoverageBoundTest
