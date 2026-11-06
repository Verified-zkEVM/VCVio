/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerived.Unforgeability
public import HashSig.GXMSS.Security.PRFDerived.Interval.Unforgeability
public import HashSig.GXMSS.Security.PRFDerived.FullRange.Transport
public import HashSig.GXMSS.Security.PRFDerived.FullRange.DisplayedBound
public import HashSig.GXMSS.Security.PRFDerived.FullRange.Unforgeability

/-! # PRF-derived GXMSS public endpoint applications

Ordinary consumers apply the complete three-law and interval four-law PRF bounds, query
budgets, and whole-experiment full-range transports using the public API.
-/

public section

open GXMSS GXMSS.Encoding GXMSS.IntervalMerkle
open OracleComp OracleSpec TweakableHash SyncSignatureUnforgeability ENNReal

variable {Key PP T X H M R Response : Type} {h w v : ℕ}
section

open GXMSS.PRFDerived.Unforgeability

example [SampleableType Key] [DecidableEq H]
    [DecidableEq M] [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) (keyLaw : prf.UniformKey) :
    prf.prfRealExperiment (randgenPRFReduction hash enc projection budget adv) =
      SyncSignatureUnforgeability.strongValid
        (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget) <$>
      SyncSignatureUnforgeability.interaction
        (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget) adv :=
  GXMSS.PRFDerived.Unforgeability.randgenPRFReduction_real_strong hash enc prf projection budget adv
    keyLaw

example [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv) :
    IsQueryBoundP (randgenPRFReduction hash enc projection budget adv)
      (fun query => query.isRight = true)
      (1 + 2 ^ h * v + qs * budget) :=
  GXMSS.PRFDerived.Unforgeability.randgenPRFReduction_functionQuery_bound hash enc projection budget
    qs adv hbound

example [SampleableType H]
    [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    𝒟[PRFScheme.prfIdealExperiment
      (randgenPRFReduction hash enc projection budget adv)] =
    SyncSignatureUnforgeability.strongUnforgeableExp
      (GXMSS.scheme hash enc budget) ProbCompRuntime.probComp adv :=
  GXMSS.PRFDerived.Unforgeability.ideal_adaptive_strong_correspondence hash enc projection budget
    adv hseed hstart hretry

example
    [SampleableType Key] [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y) (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv) (keyLaw : prf.UniformKey)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget)
      ProbCompRuntime.probComp adv ≤
    prf.prfAdvantage (randgenPRFReduction hash enc projection budget adv) +
      (SM_DT_TCR_Advantage
        (GXMSS.Reductions.merkleTargetCollisionReduction hash enc budget hv adv) +
      Encoding.TargetCollisionResistance.advantage
        (GXMSS.Reductions.encodingTargetCollisionReduction hash enc qs budget adv) +
      SM_DT_TCR_Advantage
        (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc budget adv) +
      SM_DT_TCR_Advantage
        (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc budget adv) +
      (↑((2 ^ h) * v * (2 ^ w)) : ℝ≥0∞) *
        ((↑(2 ^ w) : ℝ≥0∞) * SM_DT_UD_Advantage
          (GXMSS.Reductions.jointUndetectabilityReduction
            hash enc budget hv hw adv) +
          SM_DT_PRE_Advantage
            (GXMSS.Reductions.jointPreimageReduction hash enc budget hv hw adv))) :=
  GXMSS.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound hash enc prf projection
    budget qs hv hw htwo adv hbound keyLaw hseed hstart hretry

end

section

open GXMSS.Interval.PRFDerived.Unforgeability

example [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.Interval.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ) (I : Interval h)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv) :
    IsQueryBoundP (randgenPRFReduction hash enc projection budget I adv)
      (fun query => query.isRight = true)
      (1 + (I.last.val - I.first.val + 1) * v +
        Fintype.card (Subtree.FrontierNode I) + qs * budget) :=
  GXMSS.Interval.PRFDerived.Unforgeability.randgenPRFReduction_functionQuery_bound hash enc
    projection budget qs I adv hbound

example [SampleableType H]
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
      (GXMSS.Interval.scheme hash enc budget I) ProbCompRuntime.probComp adv :=
  GXMSS.Interval.PRFDerived.Unforgeability.ideal_adaptive_strong_correspondence hash enc projection
    budget I adv hseed hstart hretry hfiller

example
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
  GXMSS.Interval.PRFDerived.Unforgeability.strong_reduction_bound_of_two_codewords hash enc prf
    projection budget qs I hv hw htwo adv hqueries keyLaw hseed hstart hretry hfiller

example
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    IsTotalQueryBound (fillerQueries (M := M) (v := v) (Interval.full h) p pp) 0 :=
  GXMSS.Interval.PRFDerived.Unforgeability.fillerQueries_full_bound p pp

example [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    𝒟[prf.prfRealExperiment (randgenPRFReduction hash enc p K (Interval.full h) adv)] =
      𝒟[(restrictPRF prf).prfRealExperiment
        (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv)] :=
  GXMSS.Interval.PRFDerived.Unforgeability.fullRangeRealCorrespondence hash enc prf p K adv

example [SampleableType Response]
    [DecidableEq H] [DecidableEq M] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    𝒟[PRFScheme.prfIdealExperiment
      (randgenPRFReduction hash enc p K (Interval.full h) adv)] =
      𝒟[PRFScheme.prfIdealExperiment
        (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv)] :=
  GXMSS.Interval.PRFDerived.Unforgeability.fullRangeIdealCorrespondence hash enc p K adv

example [SampleableType Response] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    prf.prfAdvantage (randgenPRFReduction hash enc p K (Interval.full h) adv) =
      (restrictPRF prf).prfAdvantage
        (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv) :=
  GXMSS.Interval.PRFDerived.Unforgeability.fullRangePRFAdvantage hash enc prf p K adv

example
    [SampleableType H] [SampleableType R] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.Interval.PRFDerived.Query PP M h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    prf.prfAdvantage (randgenPRFReduction hash enc p K (Interval.full h) adv) +
      GXMSS.Interval.Unforgeability.powerOfTwoStrongUnforgeabilityBound hash enc K qs
        (Interval.full h) hv hw adv =
      (restrictPRF prf).prfAdvantage
        (GXMSS.PRFDerived.Unforgeability.randgenPRFReduction hash enc p.toComplete K adv) +
        (TweakableHash.SM_DT_TCR_Advantage
          (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv adv) +
        Encoding.TargetCollisionResistance.advantage
          (GXMSS.Reductions.encodingTargetCollisionReduction hash enc qs K adv) +
        TweakableHash.SM_DT_TCR_Advantage
          (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K adv) +
        TweakableHash.SM_DT_TCR_Advantage
          (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K adv) +
        (((2 ^ h) * v * 2 ^ w : ℕ) : ℝ≥0∞) *
          (((2 ^ w : ℕ) : ℝ≥0∞) * TweakableHash.SM_DT_UD_Advantage
            (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw adv) +
          TweakableHash.SM_DT_PRE_Advantage
            (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw adv))) :=
  GXMSS.Interval.PRFDerived.Unforgeability.fullRangeDisplayedBound hash enc prf p K qs hv hw adv

example
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
  GXMSS.Interval.PRFDerived.Unforgeability.fullRangeStrongReductionBound hash enc prf p K qs hv hw
    htwo adv hbound keyLaw hseed hstart hretry

example [SampleableType Key] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (p : GXMSS.Interval.PRFDerived.Interpretation PP H R Response) (K : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    SyncSignatureUnforgeability.strongUnforgeableExp
      (GXMSS.Interval.PRFDerived.scheme hash enc prf.eval p K (Interval.full h))
      ProbCompRuntime.probComp adv = SyncSignatureUnforgeability.strongUnforgeableExp
        (GXMSS.PRFDerived.scheme hash enc (restrictPRF prf).eval p.toComplete K)
        ProbCompRuntime.probComp adv :=
  GXMSS.Interval.PRFDerived.Unforgeability.fullRangeStrongExperiment hash enc prf p K adv

end
