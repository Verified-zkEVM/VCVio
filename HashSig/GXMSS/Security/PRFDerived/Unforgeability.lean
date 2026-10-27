/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerived.PRFOracleInteraction
import all HashSig.GXMSS.Security.PRFDerived.KeyGeneration
import all HashSig.GXMSS.Security.PRFDerived.Signing
import all HashSig.GXMSS.Security.PRFDerived.PRFOracleInteraction

/-!
# PRF-derived GXMSS strong unforgeability

The named full-interaction PRF distinguisher has a pathwise function-query bound. Its ideal
correspondence and additive PRF bound compose with generic GXMSS strong unforgeability.
The real-oracle correspondence is provided by `randgenPRFReduction_real_strong`.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- The actual full-interaction distinguisher has a pathwise function-query bound.
The source bound charges every signing request; duplicate epochs only lower the cost. -/
theorem randgenPRFReduction_functionQuery_bound [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv) :
    IsQueryBoundP (randgenPRFReduction hash enc projection budget adv)
      (fun query => query.isRight = true)
      (1 + 2 ^ h * v + qs * budget) := by
  unfold randgenPRFReduction
  apply (isQueryBoundP_map_iff _ _ _).mpr
  rw [adaptiveInteraction_from_material]
  apply isQueryBoundP_bind
    (p := fun query => query.isRight = true)
    (keyMaterialQueries_bound (M := M) projection).isQueryBoundP
  intro material _
  let pair := GXMSS.keys hash material.1 material.2
  have hrun : IsQueryBoundP
      ((simulateQ (adaptiveHandler hash enc projection budget pair.2)
        (adv.forge pair.1)).run
        SyncSignatureUnforgeability.emptyHistory)
      (fun query => query.isRight = true)
      (qs * budget) := by
    apply isQueryBoundP_simulateQ_run_weighted
      (p := fun query => query.isRight = true)
      (q := fun query => query.isRight = true)
      (adaptiveHandler hash enc projection budget pair.2)
      budget
    · intro query hp history
      change query.isRight = true at hp
      simpa only [hp, ite_true] using
        adaptiveHandler_query_bound hash enc projection budget pair.2 query history
    · intro query hp history
      change ¬ query.isRight = true at hp
      simpa only [ite_eq_right hp] using
        adaptiveHandler_query_bound hash enc projection budget pair.2 query history
    · exact hbound pair.1
  have hresult : IsQueryBoundP
      (do
        let result ← (simulateQ (adaptiveHandler hash enc projection budget pair.2)
          (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
        pure (pair.1, result.1, result.2))
      (fun query => query.isRight = true)
      (qs * budget) := by
    simpa only [Nat.add_zero] using isQueryBoundP_bind hrun
      (fun result _ => (show IsQueryBoundP
        (pure (pair.1, result.1, result.2) : OracleComp
          (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response) _)
        (fun query => query.isRight = true) 0 from trivial))
  exact hresult

/-- The strong pair-fresh adaptive game has the same one-cache PRF hop. -/
private theorem adaptive_strong_prf_bound [SampleableType Key] [DecidableEq H]
    [DecidableEq M] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (keyLaw : prf.UniformKey) :
    (SyncSignatureUnforgeability.strongUnforgeableExp
      (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget)
      ProbCompRuntime.probComp adv).boolDist
      𝒟[PRFScheme.prfIdealExperiment
        (randgenPRFReduction hash enc projection budget adv)] ≤
      prf.prfAdvantage (randgenPRFReduction hash enc projection budget adv) := by
  unfold SyncSignatureUnforgeability.strongUnforgeableExp
    SyncSignatureUnforgeability.outputMeasure
  rw [← randgenPRFReduction_real_strong hash enc prf projection budget adv keyLaw]
  rfl

/-- The ideal full-interaction strong game is generic GXMSS strong
unforgeability under the local seed, start and retry projection laws. -/
theorem ideal_adaptive_strong_correspondence [SampleableType H]
    [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash projection)
    (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    𝒟[PRFScheme.prfIdealExperiment
      (randgenPRFReduction hash enc projection budget adv)] =
    SyncSignatureUnforgeability.strongUnforgeableExp
      (GXMSS.scheme hash enc budget) ProbCompRuntime.probComp adv := by
  let : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
    (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
  have hfull := EvalDistEq.of_evalDist_eq
    (ideal_adaptive_interaction_correspondence hash enc projection budget adv
      hseed hstart hretry)
  have hvalid : SyncSignatureUnforgeability.strongValid
      (oracleScheme hash enc projection budget) =
      SyncSignatureUnforgeability.strongValid
        (GXMSS.scheme hash enc budget) := by
    funext result
    rfl
  unfold SyncSignatureUnforgeability.strongUnforgeableExp
    SyncSignatureUnforgeability.outputMeasure randgenPRFReduction
    PRFScheme.prfIdealExperiment
  rw [ProbCompRuntime.probComp_evalDist]
  change 𝒟[(simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      ((SyncSignatureUnforgeability.strongValid
        (oracleScheme hash enc projection budget)) <$>
        adaptiveInteraction hash enc projection budget adv)).run' ∅] = _
  rw [simulateQ_map, state_run'_map]
  change 𝒟[(SyncSignatureUnforgeability.strongValid
      (oracleScheme hash enc projection budget)) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        (adaptiveInteraction hash enc projection budget adv)).run' ∅] =
    𝒟[(SyncSignatureUnforgeability.strongValid
      (GXMSS.scheme hash enc budget)) <$>
      SyncSignatureUnforgeability.interaction
        (GXMSS.scheme hash enc budget) adv]
  rw [hvalid]
  exact (hfull.map (SyncSignatureUnforgeability.strongValid
    (GXMSS.scheme hash enc budget))).evalDist_eq

set_option maxHeartbeats 1600000 in
-- Elaborating both complete adaptive game measures in the additive inequality
-- exceeds the default heartbeat limit; the proof is a short measure bound.
/-- The shared-response PRF cost adds to the generic strong GXMSS game. The
Boolean measures retain returned failure and missing mass. -/
theorem adaptive_strong_additive_bound [SampleableType Key]
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (keyLaw : prf.UniformKey)
    (hseed : PublicSeedSamplingLaw hash projection)
    (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    SyncSignatureUnforgeability.strongAdvantage
      (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget)
      ProbCompRuntime.probComp adv ≤
    prf.prfAdvantage (randgenPRFReduction hash enc projection budget adv) +
      SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash enc budget) ProbCompRuntime.probComp adv := by
  let source := SyncSignatureUnforgeability.strongUnforgeableExp
    (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget)
    ProbCompRuntime.probComp adv
  let ideal := 𝒟[PRFScheme.prfIdealExperiment
    (randgenPRFReduction hash enc projection budget adv)]
  have hhop := adaptive_strong_prf_bound hash enc prf projection budget adv keyLaw
  have hcorr := ideal_adaptive_strong_correspondence hash enc projection budget
    adv hseed hstart hretry
  change source {true} ≤ _
  calc
    source {true} ≤ ideal {true} + source.boolDist ideal :=
      Measure.apply_true_le_add_boolDist source ideal
    _ ≤ ideal {true} +
      prf.prfAdvantage (randgenPRFReduction hash enc projection budget adv) :=
      add_le_add_right hhop _
    _ = prf.prfAdvantage
      (randgenPRFReduction hash enc projection budget adv) +
      SyncSignatureUnforgeability.strongAdvantage
        (GXMSS.scheme hash enc budget) ProbCompRuntime.probComp adv := by
      dsimp [ideal]
      rw [hcorr]
      exact add_comm _ _

set_option maxHeartbeats 1600000 in
-- The six concrete reduction adversaries and their target counts make the
-- composed statement expensive to elaborate under the default limit.
/-- Strong unforgeability of the shared-response PRF-derived scheme follows
from the named adaptive PRF advantage and the proved two-codeword generic
reduction. Each hardness term keeps the exact reduction adversary and target
count from the generic theorem. -/
theorem strong_reduction_bound
    [SampleableType Key] [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (Signature R H h v)]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (htwo : ∃ x y : Codeword v (2 ^ w),
      x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hbound : GXMSS.Unforgeability.SigningQueryBound qs adv)
    (keyLaw : prf.UniformKey)
    (hseed : PublicSeedSamplingLaw hash projection)
    (hstart : ChainStartSamplingLaw projection)
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
            (GXMSS.Reductions.jointPreimageReduction hash enc budget hv hw adv))) := by
  have hhop := adaptive_strong_additive_bound hash enc prf projection budget adv
    keyLaw hseed hstart hretry
  have hgeneric := (GXMSS.Unforgeability.strong_unforgeability_reduction_bound
    hash enc budget qs hv hw htwo adv) hbound
  exact hhop.trans (add_le_add_right hgeneric _)


end GXMSS.PRFDerived.Unforgeability
