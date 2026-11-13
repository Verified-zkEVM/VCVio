/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerivedUnforgeability

/-!
# Three-law full-range interval PRF security

The actual interval evaluator and its captured key sampler transport to the original complete
domain. No frontier coordinate is queried, so no filler projection law is required.
-/

public section
namespace GXMSS.Interval.PRFDerived.Unforgeability
open OracleComp OracleSpec IncomparableEncoding GXMSS GXMSS.IntervalMerkle ENNReal
open PRFScheme.DomainTransport
open GXMSS.PRFDerived.Unforgeability
  (randgenPRFReduction_fullRange_projection randgenPRFReduction_advantage_fullRange_projection)
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- The entire native real program agrees after restricting the actual evaluator's domain. -/
theorem fullRangeRealCorrespondence [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    prf.prfRealExperiment (randgenPRFReduction hash enc p budget (Interval.full h) adv) =
      (pullback prf GXMSS.Interval.PRFDerived.Query.ofComplete).prfRealExperiment
        (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete budget adv) := by
  rw [← randgenPRFReduction_fullRange_projection]
  exact real_experiment _ _ _

/-- The entire native ideal program agrees on the original three-family domain. -/
theorem fullRangeIdealCorrespondence [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)] [SampleableType Response]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    PRFScheme.prfIdealExperiment (randgenPRFReduction hash enc p budget (Interval.full h) adv) =
      PRFScheme.prfIdealExperiment
        (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete budget adv) := by
  rw [← randgenPRFReduction_fullRange_projection]
  exact ideal_experiment _ GXMSS.Interval.PRFDerived.Query.ofComplete_injective _

/-- Full-range seed-only schemes have equal entire strong-experiment measures. -/
theorem fullRangeStrongExperiment [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (runtime : ProbCompRuntime ProbComp)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    SyncSignatureUnforgeability.strongUnforgeableExp
        (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval p budget (Interval.full h))
        runtime adv =
      SyncSignatureUnforgeability.strongUnforgeableExp
        (GXMSS.PRFDerived.scheme prf.keygen hash enc
          (pullback prf GXMSS.Interval.PRFDerived.Query.ofComplete).eval p.toComplete budget)
        runtime adv := by
  rw [GXMSS.Interval.PRFDerived.scheme_full]
  rfl

/-- The native full-range interval PRF advantage plus its sharp direct bound. -/
@[expose] noncomputable def fullRangeStrongUnforgeabilityBound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) : ℝ≥0∞ :=
  prf.prfAdvantage (randgenPRFReduction hash enc p budget (Interval.full h) adv) +
    GXMSS.Interval.Unforgeability.strongUnforgeabilityBound hash enc budget qs
      (Interval.full h) hv hw adv

/-- The sharp displayed bound is identical on the two native domains. -/
theorem fullRangeDisplayedBound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    fullRangeStrongUnforgeabilityBound hash enc prf p budget qs hv hw adv =
      GXMSS.PRFDerived.Unforgeability.strongUnforgeabilityBound hash enc
        (pullback prf GXMSS.Interval.PRFDerived.Query.ofComplete) p.toComplete
        budget qs hv hw adv := by
  unfold fullRangeStrongUnforgeabilityBound
    GXMSS.PRFDerived.Unforgeability.strongUnforgeabilityBound
  rw [randgenPRFReduction_advantage_fullRange_projection]

/-- Three-law full-range interval security under a pointwise nonmaximum-output premise. -/
theorem fullRangeStrongReductionBound
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (hnonmax : enc.NoMaximumOutput)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hqueries : SyncSignatureUnforgeability.SigningQueryBound qs adv)
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval p budget (Interval.full h))
      ProbCompRuntime.probComp adv ≤
      fullRangeStrongUnforgeabilityBound hash enc prf p budget qs hv hw adv := by
  classical
  unfold SyncSignatureUnforgeability.strongAdvantage
  rw [fullRangeStrongExperiment, fullRangeDisplayedBound]
  exact GXMSS.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound hash enc
    (pullback prf GXMSS.Interval.PRFDerived.Query.ofComplete) p.toComplete budget qs hv hw
    hnonmax adv hqueries hseed hstart hretry

/-- Two global codewords derive all full-range interval encoding premises. -/
theorem fullRangeStrongReductionBound_of_two_codewords
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : PRFScheme Key (GXMSS.Interval.PRFDerived.Query PP M h v) Response)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
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
      (GXMSS.Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection budget
        (Interval.full h))
      ProbCompRuntime.probComp adv ≤
      fullRangeStrongUnforgeabilityBound hash enc prf projection budget qs hv hw adv := by
  have hv : 0 < v := by
    have := enc.two_le_length_of_two_codewords htwo
    omega
  have hw : 0 < w := by
    by_contra hz
    have hw0 : w = 0 := by omega
    have hr := enc.two_le_radix_of_two_codewords htwo
    simp [hw0] at hr
  exact fullRangeStrongReductionBound hash enc prf projection budget qs hv hw
    (enc.noMaximumOutput_of_two_codewords htwo) adv hqueries hseed hstart hretry

end GXMSS.Interval.PRFDerived.Unforgeability
