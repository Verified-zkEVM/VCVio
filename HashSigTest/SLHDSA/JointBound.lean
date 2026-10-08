/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.JointBound
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSigTest.SLHDSA.SeedCouplingBound

/-!
# The joint target-collision and hidden-value bound at the SHAKE bundles

At every SHAKE bundle whose address fields fit their FIPS 205 widths, and so at
SLH-DSA-SHAKE-128s, a forger with hash budget `qh` makes the run of SLH-DSA in the random-oracle
model at a fixed public seed fire a same-key target collision or a hidden-value hit with
probability at most `2 (qh + V) / 256 ^ n`. The node type and the message-`PRF` key type of a SHAKE
bundle are both `n`-byte strings, so `|Y| ≤ |SK.prf|` holds with equality.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.JointBoundTest

open Security SeedCouplingBoundTest

/-- The core of the SHAKE bundle at validated parameters `vp`. -/
abbrev shakeCore (vp : ValidatedParams) : CorePrimitives vp.params :=
  (Concrete.shakePrimitives vp.params).core

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
    (Concrete.keyDiscipline_shakePrimitives vp hb) le_rfl e optRand pkSeed hadv

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
