/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.HedgedKeyBound
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSigTest.SLHDSA.Bundles

/-!
# The message-`PRF` key events under hedged signing, at the SHAKE bundles

At every SHAKE bundle whose address fields fit their FIPS 205 widths, the node type, the
message-`PRF` key type and the public-seed type are all `n`-byte strings, and a uniform `opt_rand`
equals the public seed with probability `1 / 256 ^ n`.

* With `opt_rand` uniform, the run of a forger wins strongly, or caches an `H_msg` point at `SK.prf`
  together with a `PRF_msg` point keyed by `SK.prf` at `opt_rand = PK.seed`, or has
  `SK.prf = PK.seed`, with probability at most
  `securityBound vp.params (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs (qh + qs + 1) / 256 ^ (2 n)`.
* The ideal run of a forger with `qs` signing queries draws a randomizer at `opt_rand = PK.seed`
  with probability at most `qs / 256 ^ n`.
* The secret-free experiment makes at most `qh + qs + 1` `H_msg` queries.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.HedgedKeyBoundTest

open Concrete Security BundleTest

/-- At every SHAKE bundle whose address fields fit their widths, with `opt_rand` uniform, a forger
with budgets `qh` and `qs` wins strongly or hits the message-`PRF` key at `opt_rand = PK.seed` with
probability at most
`securityBound vp.params (256 ^ n) 2 1 qh qs + 1 / 256 ^ n + qs (qh + qs + 1) / 256 ^ (2 n)`. -/
example (vp : ValidatedParams) (hb : CanonicalAddressBounds vp.params)
    (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y) (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e (fun _ => $ᵗ (shakeCore vp).Y)
      (pure pkSeed))} {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← romSchemeRun (shakeCore vp) e (fun _ => $ᵗ (shakeCore vp).Y) (pure pkSeed) adv}[
      z.1.strongWins = true ∨ RunPrfKeyClash id pkSeed pkSeed z] ≤
    securityBound vp.params (256 ^ vp.params.n) 2 1 qh qs + 1 / (256 ^ vp.params.n : ℕ) +
      qs * ((256 ^ vp.params.n : ℕ) : ℝ≥0∞)⁻¹ *
        (((qh : ℝ≥0∞) + qs + 1) / ((256 ^ vp.params.n : ℕ) : ℝ≥0∞)) := by
  rw [← natCard_shakePrimitives_y]
  exact prEvent_romSchemeRun_strongWins_or_runPrfKeyClash_le (shakePrimitives_byteLaws vp.params)
    (keyDiscipline_shakePrimitives vp hb) le_rfl e _ pkSeed Function.injective_id pkSeed
    (fun _ => (SampleableType.prEvent_uniformSample_eq_singleton_natCard _).le) hadv

/-- At every SHAKE bundle, with `opt_rand` uniform, the ideal run of a forger with `qs` signing
queries draws a randomizer derivation at `opt_rand = PK.seed` with probability at most
`qs / 256 ^ n`. -/
example (vp : ValidatedParams) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e (fun _ => $ᵗ (shakeCore vp).Y)
      (pure pkSeed))} {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (hashSpec (shakeCore vp))
        (DeriveQuery (shakeCore vp)) (shakeCore vp).Y)
      (unforgeableTranscriptExperiment (deriveAdversary (shakeCore vp) adv pkSeed))).run (∅, ∅)}[
      RandDerivedAt pkSeed z.2.2] ≤ qs * ((256 ^ vp.params.n : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [← natCard_shakePrimitives_y]
  exact prEvent_idealRun_randDerivedAt_le _ pkSeed
    (fun _ => (SampleableType.prEvent_uniformSample_eq_singleton_natCard _).le) hadv

/-- At every SHAKE bundle and every `opt_rand` source, the secret-free experiment makes at most
`qh + qs + 1` `H_msg` queries. -/
example (vp : ValidatedParams) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    IsQueryBoundP (unforgeableTranscriptExperiment (deriveAdversary (shakeCore vp) adv pkSeed))
      (Coverage.IsHmsgQuery (shakeCore vp)) (qh + qs + 1) :=
  isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary_hmsg optRand pkSeed hadv

end SLHDSA.HedgedKeyBoundTest
