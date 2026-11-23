/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedIdealization
public import HashSig.GXMSS.Security.Interval.PRFDerivedUnforgeability
public import HashSig.GXMSS.Security.Unforgeability

/-!
# Three-family PRF-derived complete strong unforgeability

Native real and ideal experiments on the original PRF domain give one PRF advantage plus the
full-range direct bound. Only the seed, chain-start and retry projection laws are required.
-/

public section
namespace GXMSS.PRFDerived.Unforgeability
open OracleComp OracleSpec IncomparableEncoding ENNReal GXMSS GXMSS.IntervalMerkle
open MeasureTheory
open GXMSS.Interval.PRFDerived.Unforgeability
  (ideal_adaptive_strong_correspondence_of_used_frontier usedFillerSamplingLaw_full)
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- The original three-family native ideal strong game equals the direct complete game. -/
theorem ideal_adaptive_strong_correspondence [SampleableType H] [SampleableType R]
    [SampleableType Response] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) :
    𝒟[PRFScheme.prfIdealExperiment (randgenPRFReduction hash enc p budget adv)] =
      SyncSignatureUnforgeability.strongUnforgeableExp
        (GXMSS.scheme hash enc budget) ProbCompRuntime.probComp adv := by
  classical
  rw [randgenPRFReduction_ideal_fullRange]
  exact (ideal_adaptive_strong_correspondence_of_used_frontier hash enc
    (intervalProjection p) budget (Interval.full h) adv hseed hstart hretry
    (usedFillerSamplingLaw_full _)).trans (GXMSS.Interval.strongUnforgeableExp_full _ _ _ _ _)

/-- The actual-keygen complete game is bounded by its native PRF hop and the direct game. -/
theorem adaptive_strong_additive_bound [SampleableType H] [SampleableType R]
    [SampleableType Response] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval p budget)
      ProbCompRuntime.probComp adv ≤
    prf.prfAdvantage (randgenPRFReduction hash enc p budget adv) +
      SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash enc budget) ProbCompRuntime.probComp adv := by
  let source := SyncSignatureUnforgeability.strongUnforgeableExp
    (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval p budget)
    ProbCompRuntime.probComp adv
  let ideal := 𝒟[PRFScheme.prfIdealExperiment (randgenPRFReduction hash enc p budget adv)]
  have hhop : source.boolDist ideal =
      prf.prfAdvantage (randgenPRFReduction hash enc p budget adv) := by
    unfold source SyncSignatureUnforgeability.strongUnforgeableExp
      SyncSignatureUnforgeability.outputMeasure
    rw [← randgenPRFReduction_real_strong]
    rfl
  have hcorr := ideal_adaptive_strong_correspondence hash enc p budget adv hseed hstart hretry
  change source {true} ≤ _
  calc
    source {true} ≤ ideal {true} + source.boolDist ideal :=
      Measure.apply_true_le_add_boolDist source ideal
    _ = prf.prfAdvantage (randgenPRFReduction hash enc p budget adv) +
        SyncSignatureUnforgeability.strongAdvantage
          (GXMSS.scheme hash enc budget) ProbCompRuntime.probComp adv := by
      rw [hhop]
      dsimp [ideal]
      rw [hcorr]
      exact add_comm _ _

/-- The native original-domain PRF advantage plus the sharp full-range direct bound. -/
@[expose] noncomputable def strongUnforgeabilityBound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) : ℝ≥0∞ :=
  prf.prfAdvantage (randgenPRFReduction hash enc p budget adv) +
    GXMSS.Interval.Unforgeability.strongUnforgeabilityBound
      hash enc budget qs (Interval.full h) hv hw adv

/-- The native original-domain PRF advantage plus the relaxed full-range direct bound. -/
@[expose] noncomputable def powerOfTwoStrongUnforgeabilityBound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) : ℝ≥0∞ :=
  prf.prfAdvantage (randgenPRFReduction hash enc p budget adv) +
    GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound
      hash enc budget qs (Interval.full h) hv hw adv

/-- Complete strong unforgeability under a pointwise nonmaximum-output encoding premise. -/
theorem strong_unforgeability_reduction_bound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (hnonmax : enc.NoMaximumOutput)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hqueries : SyncSignatureUnforgeability.SigningQueryBound qs adv)
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval p budget)
      ProbCompRuntime.probComp adv ≤
      strongUnforgeabilityBound hash enc prf p budget qs hv hw adv := by
  have hbase := GXMSS.Interval.Unforgeability.strong_unforgeability_reduction_bound
    hash enc budget qs (Interval.full h) hv hw hnonmax adv hqueries
  have hcomplete : SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc budget)
      ProbCompRuntime.probComp adv ≤
      GXMSS.Interval.Unforgeability.strongUnforgeabilityBound
        hash enc budget qs (Interval.full h) hv hw adv := by
    simpa only [SyncSignatureUnforgeability.strongAdvantage,
      GXMSS.Interval.strongUnforgeableExp_full] using hbase
  exact (adaptive_strong_additive_bound hash enc prf p budget adv hseed hstart hretry).trans
    (add_le_add_right hcomplete _)

/-- The complete endpoint with relaxed power-of-two coefficients and the same native PRF hop. -/
theorem strong_unforgeability_power_of_two_reduction_bound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)] [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (hnonmax : enc.NoMaximumOutput)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hqueries : SyncSignatureUnforgeability.SigningQueryBound qs adv)
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval p budget)
      ProbCompRuntime.probComp adv ≤
      powerOfTwoStrongUnforgeabilityBound hash enc prf p budget qs hv hw adv := by
  have hbase := GXMSS.Interval.Unforgeability.strong_unforgeability_power_of_two_reduction_bound
    hash enc budget qs (Interval.full h) hv hw hnonmax adv hqueries
  have hcomplete : SyncSignatureUnforgeability.strongAdvantage (GXMSS.scheme hash enc budget)
      ProbCompRuntime.probComp adv ≤
      GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound
        hash enc budget qs (Interval.full h) hv hw adv := by
    simpa only [SyncSignatureUnforgeability.strongAdvantage,
      GXMSS.Interval.strongUnforgeableExp_full] using hbase
  exact (adaptive_strong_additive_bound hash enc prf p budget adv hseed hstart hretry).trans
    (add_le_add_right hcomplete _)

/-- Two distinct global codewords derive all complete sharp-bound encoding premises. -/
theorem strong_unforgeability_reduction_bound_of_two_codewords
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hqueries : SyncSignatureUnforgeability.SigningQueryBound qs adv)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    let hv : 0 < v := by
      have := enc.two_le_length_of_two_codewords htwo
      omega
    let hw : 0 < w := by
      by_contra hz
      have hw0 : w = 0 := by omega
      have hr := enc.two_le_radix_of_two_codewords htwo
      simp [hw0] at hr
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget)
      ProbCompRuntime.probComp adv ≤
      strongUnforgeabilityBound hash enc prf projection budget qs hv hw adv := by
  have hv : 0 < v := by
    have := enc.two_le_length_of_two_codewords htwo
    omega
  have hw : 0 < w := by
    by_contra hz
    have hw0 : w = 0 := by omega
    have hr := enc.two_le_radix_of_two_codewords htwo
    simp [hw0] at hr
  exact strong_unforgeability_reduction_bound hash enc prf projection budget qs hv hw
    (enc.noMaximumOutput_of_two_codewords htwo) adv hqueries hseed hstart hretry

/-- Two distinct global codewords also give the relaxed complete PRF endpoint. -/
theorem strong_unforgeability_power_of_two_reduction_bound_of_two_codewords
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hqueries : SyncSignatureUnforgeability.SigningQueryBound qs adv)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    let hv : 0 < v := by
      have := enc.two_le_length_of_two_codewords htwo
      omega
    let hw : 0 < w := by
      by_contra hz
      have hw0 : w = 0 := by omega
      have hr := enc.two_le_radix_of_two_codewords htwo
      simp [hw0] at hr
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget)
      ProbCompRuntime.probComp adv ≤
      powerOfTwoStrongUnforgeabilityBound hash enc prf projection budget qs hv hw adv := by
  have hv : 0 < v := by
    have := enc.two_le_length_of_two_codewords htwo
    omega
  have hw : 0 < w := by
    by_contra hz
    have hw0 : w = 0 := by omega
    have hr := enc.two_le_radix_of_two_codewords htwo
    simp [hw0] at hr
  exact strong_unforgeability_power_of_two_reduction_bound hash enc prf projection budget qs hv hw
    (enc.noMaximumOutput_of_two_codewords htwo) adv hqueries hseed hstart hretry

end GXMSS.PRFDerived.Unforgeability
