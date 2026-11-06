/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.PRFDerived.Scheme
public import HashSig.GXMSS.Security.PRFDerived.FullRange.Transport
public import HashSig.GXMSS.Security.PRFDerived.FullRange.Unforgeability
public import HashSig.GXMSS.Security.PRFDerived.Interval.Idealization
public import HashSig.GXMSS.Security.PRFDerived.Interval.OracleInteraction
public import HashSig.GXMSS.Security.PRFDerived.Interval.Unforgeability
public import HashSig.GXMSS.Security.PRFDerived.ResponseCache
public import HashSig.GXMSS.Security.PRFDerived.RetrySampling
public import HashSig.GXMSS.Security.PRFDerived.SigningSimulation

/-!
# Interval PRF security compiler audit

The separate `TrustAudit` checks every PRF module origin, including shared private helpers and
inductive/generated declarations, with nonzero coverage and transitive axiom checks. Named completed
  endpoints are theorems;
full-range real and cached-ideal transports discharge their named proposition definitions.
-/

public section
open GXMSS.Interval.PRFDerived.Unforgeability

#check @randgenPRFReduction_real_strong
#check @randgenPRFReduction_functionQuery_bound
#check @ideal_fixed_interaction_correspondence
#check @ideal_interaction_correspondence
#check @ideal_adaptive_strong_correspondence
#check @adaptive_strong_additive_bound
#check @strong_reduction_bound_of_two_codewords
#check @fillerQueries_full_bound
#check @FullRangeSchemeCorrespondence
#check @FullRangeRealCorrespondence
#check @FullRangeIdealCorrespondence

#check @GXMSS.Interval.PRFDerived.run_zero
#check @GXMSS.Interval.PRFDerived.run_inactive
#check @GXMSS.Interval.PRFDerived.scheme_full
#check @fullRangeSchemeCorrespondence
#check @fullRangeRealCorrespondence
#check @fullRangeIdealCorrespondence
#check @fullRangeStrongExperiment
#check @fullRangeDisplayedBound
#check @fullRangeStrongReductionBound
#check @fullRangePRFAdvantage

open GXMSS GXMSS.Encoding GXMSS.IntervalMerkle

example {Key PP T X H M R Response : Type} {h w v : ℕ}
    [SampleableType Key] [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ) (I : Interval h) (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hqueries : GXMSS.Unforgeability.SigningQueryBound qs adv) (keyLaw : prf.UniformKey)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) (hfiller : FillerSamplingLaw projection) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.Interval.PRFDerived.scheme hash enc prf.eval projection budget I)
      ProbCompRuntime.probComp adv ≤
      prf.prfAdvantage (randgenPRFReduction hash enc projection budget I adv) +
        GXMSS.Interval.Unforgeability.strongUnforgeabilityBound hash enc budget qs I hv hw adv :=
  strong_reduction_bound_of_two_codewords hash enc prf projection budget qs I hv hw htwo adv
    hqueries keyLaw hseed hstart hretry hfiller

example {Key PP T X H M R Response : Type} {h w v : ℕ}
    [SampleableType Key] [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv) (keyLaw : prf.UniformKey)
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.Interval.PRFDerived.scheme hash enc prf.eval p K (Interval.full h))
      ProbCompRuntime.probComp adv ≤
      prf.prfAdvantage (randgenPRFReduction hash enc p K (Interval.full h) adv) +
        GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound hash enc K qs
          (Interval.full h) hv hw adv :=
  fullRangeStrongReductionBound hash enc prf p K qs hv hw htwo adv hbound keyLaw
    hseed hstart hretry
