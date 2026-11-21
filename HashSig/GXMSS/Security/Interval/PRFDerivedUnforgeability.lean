/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Unforgeability
public import HashSig.GXMSS.Security.Interval.Auxiliary.PRFDerivedIdealization

/-!
# PRF-derived interval strong unforgeability

Whole-interaction idealization yields one named PRF advantage plus the ten-term original-domain
interval bound. The core encoding premise is pointwise; response laws retain the native seed law.
-/

public section
namespace GXMSS.Interval.PRFDerived.Unforgeability
open OracleComp OracleSpec IncomparableEncoding ENNReal GXMSS GXMSS.IntervalMerkle
open ProbabilityTheory MeasureTheory
open PRFScheme.QuerySimulation
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

private theorem adaptive_strong_prf_bound [DecidableEq H]
    [DecidableEq M] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    (SyncSignatureUnforgeability.strongUnforgeableExp
      (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget I)
      ProbCompRuntime.probComp adv).boolDist
      𝒟[PRFScheme.prfIdealExperiment
        (randgenPRFReduction hash enc projection budget I adv)] ≤
      prf.prfAdvantage (randgenPRFReduction hash enc projection budget I adv) := by
  unfold SyncSignatureUnforgeability.strongUnforgeableExp
    SyncSignatureUnforgeability.outputMeasure
  rw [← randgenPRFReduction_real_strong hash enc prf projection budget I adv]
  rfl

/-- Projection laws at queried coordinates identify the whole native ideal strong game
with the direct interval scheme. -/
theorem ideal_adaptive_strong_correspondence_of_used_frontier [SampleableType H]
    [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash projection)
    (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) (hfiller : UsedFillerSamplingLaw I projection) :
    𝒟[PRFScheme.prfIdealExperiment
      (randgenPRFReduction hash enc projection budget I adv)] =
    SyncSignatureUnforgeability.strongUnforgeableExp
      (GXMSS.Interval.scheme hash enc budget I) ProbCompRuntime.probComp adv := by
  let : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
    (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
  have hcorr := ideal_interaction_correspondence_of_used_frontier hash enc projection budget I adv
    hseed hstart hretry hfiller
  have hfull := EvalDistEq.of_evalDist_eq
    (show 𝒟[(simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      (adaptiveInteraction hash enc projection budget I adv)).run' ∅] =
      𝒟[SyncSignatureUnforgeability.interaction
        (GXMSS.Interval.scheme hash enc budget I) adv] from hcorr)
  have hvalid : SyncSignatureUnforgeability.strongValid
      (oracleScheme hash enc projection budget I) =
      SyncSignatureUnforgeability.strongValid
        (GXMSS.Interval.scheme hash enc budget I) := by
    funext result
    rfl
  unfold SyncSignatureUnforgeability.strongUnforgeableExp
    SyncSignatureUnforgeability.outputMeasure randgenPRFReduction
    PRFScheme.prfIdealExperiment
  rw [ProbCompRuntime.probComp_evalDist]
  change 𝒟[(simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
      ((SyncSignatureUnforgeability.strongValid
        (oracleScheme hash enc projection budget I)) <$>
        adaptiveInteraction hash enc projection budget I adv)).run' ∅] = _
  rw [simulateQ_map, state_run'_map]
  change 𝒟[(SyncSignatureUnforgeability.strongValid
      (oracleScheme hash enc projection budget I)) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.Interval.PRFDerived.Query PP M h v) (R := Response))
        (adaptiveInteraction hash enc projection budget I adv)).run' ∅] =
    𝒟[(SyncSignatureUnforgeability.strongValid
      (GXMSS.Interval.scheme hash enc budget I)) <$>
      SyncSignatureUnforgeability.interaction
        (GXMSS.Interval.scheme hash enc budget I) adv]
  rw [hvalid]
  exact (hfull.map (SyncSignatureUnforgeability.strongValid
    (GXMSS.Interval.scheme hash enc budget I))).evalDist_eq

/-- Four global projection laws give the native ideal strong-game correspondence. -/
theorem ideal_adaptive_strong_correspondence [SampleableType H]
    [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash projection)
    (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) (hfiller : FillerSamplingLaw projection) :
    𝒟[PRFScheme.prfIdealExperiment
      (randgenPRFReduction hash enc projection budget I adv)] =
    SyncSignatureUnforgeability.strongUnforgeableExp
      (GXMSS.Interval.scheme hash enc budget I) ProbCompRuntime.probComp adv := by
  exact ideal_adaptive_strong_correspondence_of_used_frontier hash enc projection budget I adv
    hseed hstart hretry (fun _ => hfiller)

/-- The shared-response PRF cost adds to the direct strong interval game. The
Boolean measures retain returned failure and missing mass. -/
theorem adaptive_strong_additive_bound
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash projection)
    (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) (hfiller : FillerSamplingLaw projection) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget I)
      ProbCompRuntime.probComp adv ≤
    prf.prfAdvantage (randgenPRFReduction hash enc projection budget I adv) +
      SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.Interval.scheme hash enc budget I) ProbCompRuntime.probComp adv := by
  let source := SyncSignatureUnforgeability.strongUnforgeableExp
    (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget I)
    ProbCompRuntime.probComp adv
  let ideal := 𝒟[PRFScheme.prfIdealExperiment
    (randgenPRFReduction hash enc projection budget I adv)]
  have hhop := adaptive_strong_prf_bound hash enc prf projection budget I adv
  have hcorr := ideal_adaptive_strong_correspondence hash enc projection budget I
    adv hseed hstart hretry hfiller
  change source {true} ≤ _
  calc
    source {true} ≤ ideal {true} + source.boolDist ideal :=
      Measure.apply_true_le_add_boolDist source ideal
    _ ≤ ideal {true} +
      prf.prfAdvantage (randgenPRFReduction hash enc projection budget I adv) :=
      add_le_add_right hhop _
    _ = prf.prfAdvantage
      (randgenPRFReduction hash enc projection budget I adv) +
      SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.Interval.scheme hash enc budget I) ProbCompRuntime.probComp adv := by
      dsimp [ideal]
      rw [hcorr]
      exact add_comm _ _

/-- The named adaptive PRF advantage plus the original-domain ten-term interval bound. -/
@[expose] noncomputable def strongUnforgeabilityBound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ) (I : Interval h) (hv : 0 < v) (hw : 0 < w)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) : ℝ≥0∞ :=
  prf.prfAdvantage (randgenPRFReduction hash enc projection budget I adv) +
    GXMSS.Interval.Unforgeability.strongUnforgeabilityBound hash enc budget qs I hv hw adv

/-- The named PRF advantage adds to the original-domain ten-term interval bound. -/
theorem strong_unforgeability_reduction_bound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ) (I : Interval h) (hv : 0 < v) (hw : 0 < w)
    (hnonmax : enc.NoMaximumOutput)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hqueries : SyncSignatureUnforgeability.SigningQueryBound qs adv)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) (hfiller : FillerSamplingLaw projection) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget I)
      ProbCompRuntime.probComp adv ≤
      strongUnforgeabilityBound hash enc prf projection budget qs I hv hw adv := by
  unfold strongUnforgeabilityBound
  have hhop := adaptive_strong_additive_bound hash enc prf projection budget I adv
    hseed hstart hretry hfiller
  have hgeneric :=
    GXMSS.Interval.Unforgeability.strong_unforgeability_reduction_bound
      hash enc budget qs I hv hw hnonmax adv hqueries
  exact hhop.trans (add_le_add_right hgeneric _)

/-- Two global codewords derive the geometry and pointwise encoding premise for the PRF bound. -/
theorem strong_unforgeability_reduction_bound_of_two_codewords
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ) (I : Interval h)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hqueries : SyncSignatureUnforgeability.SigningQueryBound qs adv)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) (hfiller : FillerSamplingLaw projection) :
    let hv : 0 < v := by
      have := enc.two_le_length_of_two_codewords htwo
      omega
    let hw : 0 < w := by
      by_contra hz
      have hw0 : w = 0 := by omega
      have hr := enc.two_le_radix_of_two_codewords htwo
      simp [hw0] at hr
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget I)
      ProbCompRuntime.probComp adv ≤
      strongUnforgeabilityBound hash enc prf projection budget qs I hv hw adv := by
  have hv : 0 < v := by
    have := enc.two_le_length_of_two_codewords htwo
    omega
  have hw : 0 < w := by
    by_contra hz
    have hw0 : w = 0 := by omega
    have hr := enc.two_le_radix_of_two_codewords htwo
    simp [hw0] at hr
  exact strong_unforgeability_reduction_bound hash enc prf projection budget qs I hv hw
    (enc.noMaximumOutput_of_two_codewords htwo) adv hqueries hseed hstart hretry hfiller

end GXMSS.Interval.PRFDerived.Unforgeability
