/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabBudget
public import HashSig.SLHDSA.Security.KeySeparation
public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential
public import HashSigTest.SLHDSA.SeedCouplingBound

/-!
# The budget of the lab experiment at the SHAKE bundles

At every SHAKE bundle the budget `two_mul_encard_keyEntries_div_add_seedCharge_le` holds with key
separation discharged by `Concrete.keySeparated_shakePrimitives`, and it is the pathwise budget of
`CanonicalGraph.NodeKeys.prEvent_deferredFillDraw_le_of_budget` at the hazard charge `seedCharge`:
the deferred game of the lab experiment, its end fill and a uniform draw of the secret seeds fire a
conflict, a target collision at a node key, or a cached encoding of a derivation under the drawn
seeds, with probability at most `2 (qh + V) / 256 ^ n`.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.LabBudgetTest

open Security SeedCouplingBoundTest

/-- The core of the SHAKE bundle at validated parameters `vp`. -/
abbrev shakeCore (vp : ValidatedParams) : CorePrimitives vp.params :=
  (Concrete.shakePrimitives vp.params).core

/-- The budget at a SHAKE bundle, on every deferred run of the lab experiment. -/
example (vp : ValidatedParams) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) {z}
    (hz : z ∈ support ((simulateQ (slhGraph (shakeCore vp) pkSeed).deferredImpl
      (labExperiment (shakeCore vp) adv pkSeed)).run ((∅, ∅), []))) :
    2 * (((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1).encard : ℝ≥0∞) /
        ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) + seedCharge (shakeCore vp) pkSeed z.2.1.1 ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) /
        ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) := by
  rw [← natCard_shakePrimitives_y]
  exact two_mul_encard_keyEntries_div_add_seedCharge_le pkSeed
    (Concrete.keySeparated_shakePrimitives vp.params) hadv hz

/-- **The joint potential over the lab experiment at a SHAKE bundle.** The deferred game of the
lab experiment, the end fill and a uniform draw of the secret seeds fire a conflict, a target
collision at a node key, or a cached encoding of a derivation under the drawn seeds, with
probability at most `2 (qh + V) / 256 ^ n`. -/
example (vp : ValidatedParams) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    Pr{let w ← (slhGraph (shakeCore vp) pkSeed).deferredFillDraw
        ($ᵗ ((shakeCore vp).SkSeed × (shakeCore vp).SkPrf))
        (labExperiment (shakeCore vp) adv pkSeed)}[
      (slhGraph (shakeCore vp) pkSeed).Conflict w.2.1 ∨
        (slhNodeKeys (shakeCore vp) pkSeed).TCHazard w.2.1 ∨
        ∃ x, (w.2.1.1 ((secretEncoding (shakeCore vp) e pkSeed).enc w.2.2 x)).isSome] ≤
      2 * ((qh : ℝ≥0∞) + GeneralScheme.verifyInternalQueryBound vp.params) /
        ((256 ^ vp.params.n : ℕ) : ℝ≥0∞) := by
  rw [← natCard_shakePrimitives_y]
  refine (slhNodeKeys (shakeCore vp) pkSeed).prEvent_deferredFillDraw_le_of_budget _
    (fun s C => ∃ x, (C ((secretEncoding (shakeCore vp) e pkSeed).enc s x)).isSome)
    (seedCharge (shakeCore vp) pkSeed)
    (prEvent_exists_isSome_apply_secretEncoding_enc_le_seedCharge e pkSeed le_rfl) _ _ ?_
    fun z hz => two_mul_encard_keyEntries_div_add_seedCharge_le pkSeed
      (Concrete.keySeparated_shakePrimitives vp.params) hadv hz
  rw [natCard_shakePrimitives_y]
  exact ENNReal.div_ne_top (by finiteness) (by positivity)

end SLHDSA.LabBudgetTest
