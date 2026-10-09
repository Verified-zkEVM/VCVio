/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.JointBound
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSigTest.SLHDSA.Bundles

/-!
# The joint target-collision and hidden-value bound at the FIPS 205 bundles

At every SHAKE bundle whose address fields fit their FIPS 205 widths, and so at
SLH-DSA-SHAKE-128s, and at every FIPS SHA-2 bundle whose compressed address fields fit theirs, a
forger with hash budget `qh` makes the run of SLH-DSA in the random-oracle model at a fixed public
seed fire a same-key target collision or a hidden-value hit with probability at most
`2 (qh + V) / 256 ^ n`. The node type and the message-`PRF` key type of either bundle are both
`n`-byte strings, so `|Y| ≤ |SK.prf|` holds with equality. At the SHAKE bundles the forging
advantage is then at most `2 (qh + V) / 256 ^ n` plus the probability of interleaved-target
coverage, either in the ideal hidden-seed game `idealDraw` or in the run.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.JointBoundTest

open Concrete Security BundleTest

/-- **The joint bound at a SHAKE bundle.** At every SHAKE bundle whose address fields fit their
widths, a target collision or a hidden-value hit of the run at a fixed public seed has probability
at most `2 (qh + V) / 256 ^ n` for a forger with hash budget `qh`. -/
theorem prEvent_romSchemeRun_shake_le (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun (shakeCore vp) e optRand (pure pkSeed) adv}[
      RunTargetCollision (shakeCore vp) e z ∨ RunHiddenHit (shakeCore vp) e z] ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) /
        ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) := by
  rw [← natCard_shakePrimitives_y]
  exact prEvent_romSchemeRun_runTargetCollision_or_runHiddenHit_le
    (keyDiscipline_shakePrimitives vp hb) le_rfl e optRand pkSeed hadv

/-- **The joint bound at a FIPS SHA-2 bundle.** At every FIPS SHA-2 bundle whose address fields
fit their widths, including the two compressed widths of `ADRSc`, a target collision or a
hidden-value hit of the run at a fixed public seed has probability at most `2 (qh + V) / 256 ^ n`
for a forger with hash budget `qh`. -/
theorem prEvent_romSchemeRun_sha2_le (vp : ValidatedParams)
    (hb : ApprovedAddressBounds vp.params) (e : (sha2Core vp).SkSeed ≃ (sha2Core vp).Y)
    (optRand : PublicKeyCore (sha2Core vp) → ProbComp (sha2Core vp).Y)
    (pkSeed : (sha2Core vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (sha2Core vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun (sha2Core vp) e optRand (pure pkSeed) adv}[
      RunTargetCollision (sha2Core vp) e z ∨ RunHiddenHit (sha2Core vp) e z] ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) /
        ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) := by
  rw [← natCard_sha2Primitives_y]
  exact prEvent_romSchemeRun_runTargetCollision_or_runHiddenHit_le
    (keyDiscipline_sha2Primitives vp hb) le_rfl e optRand pkSeed hadv

/-- At every SHAKE bundle whose address fields fit their widths, the forging advantage at a fixed
public seed is at most `2 (qh + V) / 256 ^ n` plus the probability of interleaved-target coverage
in the ideal hidden-seed game, read on the rebuilt transcript and the merged cache. -/
example (vp : ValidatedParams) (hb : CanonicalAddressBounds vp.params)
    (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec (shakeCore vp))) adv ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) /
        ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) +
      Pr{let w ← idealDraw e optRand pkSeed adv}[
        RunItsrCovered (shakeCore vp) (DeriveOutcome.fill (shakeCore vp) w.1 w.2.1,
          (secretEncoding (shakeCore vp) e pkSeed).merge w.1 w.2.2)] := by
  rw [← natCard_shakePrimitives_y]
  exact unforgeableAdvantage_romScheme_pure_le_add_idealDraw (shakePrimitives_byteLaws vp.params)
    (keyDiscipline_shakePrimitives vp hb) le_rfl e optRand pkSeed hadv

/-- At every SHAKE bundle whose address fields fit their widths, the forging advantage at a fixed
public seed is at most `2 (qh + V) / 256 ^ n` plus the probability of interleaved-target
coverage. -/
example (vp : ValidatedParams) (hb : CanonicalAddressBounds vp.params)
    (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec (shakeCore vp))) adv ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) /
        ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) +
      Pr{let z ← romSchemeRun (shakeCore vp) e optRand (pure pkSeed) adv}[
        RunItsrCovered (shakeCore vp) z] := by
  rw [← natCard_shakePrimitives_y]
  exact unforgeableAdvantage_romScheme_pure_le_add (shakePrimitives_byteLaws vp.params)
    (keyDiscipline_shakePrimitives vp hb) le_rfl e optRand pkSeed hadv

/-- At SLH-DSA-SHAKE-128s, a target collision or a hidden-value hit of the run at a fixed public
seed has probability at most `2 (qh + V) / 256 ^ 16` for a forger with hash budget `qh`. -/
example (e : (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).SkSeed ≃
      (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).Y)
    (optRand : PublicKeyCore (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) →
      ProbComp (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).Y)
    (pkSeed : (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore
      FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun (shakeCore FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams) e
        optRand (pure pkSeed) adv}[
      RunTargetCollision _ e z ∨ RunHiddenHit _ e z] ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound
        FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams.params) /
        ((256 ^ FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams.params.n : ℕ) : ℝ≥0∞) :=
  prEvent_romSchemeRun_shake_le _
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_128s).toCanonicalAddressBounds e optRand pkSeed hadv

end SLHDSA.JointBoundTest
