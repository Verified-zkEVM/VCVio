/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.PrfKeyBound
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSigTest.SLHDSA.Bundles

/-!
# The message-`PRF` key events at the SHAKE bundles

At every SHAKE bundle whose address fields fit their FIPS 205 widths, the node type, the
message-`PRF` key type and the public-seed type are all `n`-byte strings, so the randomizer of an
`H_msg` point is compared with `SK.prf` through the identity, the fixed key is the public seed
itself, and `|Y| = 256 ^ n`.

* The run of a forger wins strongly, caches an `H_msg` point at `SK.prf`, or has `SK.prf = PK.seed`
  with probability at most `securityBound vp.params (256 ^ n) 2 1 qh qs + (qs + 1) / 256 ^ n`.
* The joint form in the ideal hidden-seed game, at `(2 (qh + V) + qs + 1) / 256 ^ n`.
* At SLH-DSA-SHAKE-256s in deterministic signing (`opt_rand = PK.seed`), the forging bound with
  both events.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.PrfKeyBoundTest

open Concrete Security BundleTest

/-- At every SHAKE bundle whose address fields fit their widths, a forger with budgets `qh` and `qs`
wins strongly, caches an `H_msg` point at `SK.prf`, or has `SK.prf = PK.seed` with probability at
most `securityBound vp.params (256 ^ n) 2 1 qh qs + (qs + 1) / 256 ^ n`. -/
theorem prEvent_romSchemeRun_strongWins_or_runPrfKeyHit_le_shake (vp : ValidatedParams)
    (hb : CanonicalAddressBounds vp.params) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun (shakeCore vp) e optRand (pure pkSeed) adv}[
      z.1.strongWins = true ∨ RunPrfKeyHit id pkSeed z] ≤
    securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs +
      ((qs : ℝ≥0∞) + 1) / ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) := by
  rw [← natCard_shakePrimitives_y]
  exact prEvent_romSchemeRun_strongWins_or_runPrfKeyHit_le (shakePrimitives_byteLaws vp.params)
    (keyDiscipline_shakePrimitives vp hb) le_rfl e optRand pkSeed Function.injective_id pkSeed
    hadv

/-- At every SHAKE bundle whose address fields fit their widths, the ideal hidden-seed game fires
a target collision, a hidden-value hit, an `H_msg` point at `SK.prf`, `SK.prf = PK.seed`, or a
cached point encoding a derivation, with probability at most `(2 (qh + V) + qs + 1) / 256 ^ n`. -/
example (vp : ValidatedParams) (hb : CanonicalAddressBounds vp.params)
    (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let w ← idealDraw e optRand pkSeed adv}[
      ((RunTargetCollision (shakeCore vp) e (DeriveOutcome.fill (shakeCore vp) w.1 w.2.1,
          (secretEncoding (shakeCore vp) e pkSeed).merge w.1 w.2.2) ∨
        RunHiddenHit (shakeCore vp) e (DeriveOutcome.fill (shakeCore vp) w.1 w.2.1,
          (secretEncoding (shakeCore vp) e pkSeed).merge w.1 w.2.2)) ∨
        RunPrfKeyHit id pkSeed (DeriveOutcome.fill (shakeCore vp) w.1 w.2.1,
          (secretEncoding (shakeCore vp) e pkSeed).merge w.1 w.2.2)) ∨
      ∃ x, (w.2.2.1 ((secretEncoding (shakeCore vp) e pkSeed).enc w.1 x)).isSome] ≤
    (2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) + qs + 1) /
      ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) := by
  rw [← natCard_shakePrimitives_y]
  exact prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_runPrfKeyHit_or_exists_isSome_le
    (keyDiscipline_shakePrimitives vp hb) le_rfl e optRand pkSeed Function.injective_id pkSeed hadv

/-- At SLH-DSA-SHAKE-256s in deterministic signing (`opt_rand = PK.seed`), at a fixed public seed, a
forger wins strongly, caches an `H_msg` point at `SK.prf`, or has `SK.prf = PK.seed` with
probability at most `securityBound` at `|Y| = 256 ^ 32`, `c = 2` and `r = 1`, plus `(qs + 1) / 256 ^
32`. -/
example (e : (shakeCore FipsParameterSet.SLHDSA_SHAKE_256s.validatedParams).SkSeed ≃
      (shakeCore FipsParameterSet.SLHDSA_SHAKE_256s.validatedParams).Y)
    (pkSeed : (shakeCore FipsParameterSet.SLHDSA_SHAKE_256s.validatedParams).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore
      FipsParameterSet.SLHDSA_SHAKE_256s.validatedParams) e
        (fun pk => pure (shakeRandomizerOfPkSeed _ pk.pkSeed)) (pure pkSeed))}
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun (shakeCore FipsParameterSet.SLHDSA_SHAKE_256s.validatedParams) e
        (fun pk => pure (shakeRandomizerOfPkSeed _ pk.pkSeed)) (pure pkSeed) adv}[
      z.1.strongWins = true ∨ RunPrfKeyHit id pkSeed z] ≤
    securityBound FipsParameterSet.SLHDSA_SHAKE_256s.validatedParams.params (256 ^ 32) 2 1 qh qs +
      ((qs : ℝ≥0∞) + 1) / ((256 ^ 32 : ℕ) : ℝ≥0∞) :=
  prEvent_romSchemeRun_strongWins_or_runPrfKeyHit_le_shake _
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_256s).toCanonicalAddressBounds e _ pkSeed hadv

end SLHDSA.PrfKeyBoundTest
