/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.PRFDerivedOracleInteraction
public import HashSig.GXMSS.Security.Interval.Auxiliary.PRFDerivedIdealization
public import HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction

/-!
# Complete PRF idealization with three projection laws

Injective cache transport and the absence of frontier calls identify the original three-family
interaction with the direct complete scheme, retaining its entire returned view.
-/

public section
namespace GXMSS.PRFDerived.Unforgeability
open OracleComp OracleSpec GXMSS GXMSS.IntervalMerkle MeasureTheory
open PRFScheme.DomainTransport
open GXMSS.Interval.PRFDerived.Unforgeability
  (ideal_interaction_correspondence_of_used_frontier usedFillerSamplingLaw_full)
variable {PP T X H M R Response : Type} {h w v : ℕ}

/-- The whole-view idealization property on the original three-family oracle domain. -/
@[expose] def IdealInteractionCorrespondence [SampleableType H] [SampleableType R]
    [SampleableType Response] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) : Prop :=
  let : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
    (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
  𝒟[(simulateQ PRFScheme.prfIdealQueryImpl
    (adaptiveInteraction hash enc p budget adv)).run' ∅] =
    𝒟[SyncSignatureUnforgeability.interaction (GXMSS.scheme hash enc budget) adv]

/-- Three sampling laws suffice on the original domain; the filler premise is vacuous. -/
theorem ideal_interaction_correspondence [SampleableType H] [SampleableType R]
    [SampleableType Response] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash p) (hstart : ChainStartSamplingLaw p)
    (hretry : RetrySamplingLaw p) :
    IdealInteractionCorrespondence hash enc p budget adv := by
  classical
  let : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
    (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
  have htransport := ideal_run' GXMSS.Interval.PRFDerived.Query.ofComplete
    GXMSS.Interval.PRFDerived.Query.ofComplete_injective
    (adaptiveInteraction hash enc p budget adv) ∅
  rw [adaptiveInteraction_fullRange, pullbackCache_empty] at htransport
  have hcorr := ideal_interaction_correspondence_of_used_frontier hash enc (intervalProjection p)
      budget (Interval.full h) adv hseed hstart hretry
      (GXMSS.Interval.PRFDerived.Unforgeability.usedFillerSamplingLaw_full _)
  dsimp only [GXMSS.Interval.PRFDerived.Unforgeability.IdealInteractionCorrespondence] at hcorr
  change 𝒟[(simulateQ PRFScheme.prfIdealQueryImpl
    (adaptiveInteraction hash enc p budget adv)).run' ∅] = _
  rw [← htransport]
  simpa only [GXMSS.Interval.interaction_full] using hcorr

end GXMSS.PRFDerived.Unforgeability
