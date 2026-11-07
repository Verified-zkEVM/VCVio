/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.PRFDerivedScheme
import all HashSig.GXMSS.PRFDerivedScheme
public import HashSig.GXMSS.Security.Auxiliary.SigningQueries
import all HashSig.GXMSS.Security.Auxiliary.SigningQueries
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedKeyGeneration
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedKeyGeneration
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedKeyMaterial
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedKeyMaterial
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedOracleQueries
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedOracleQueries
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedRetrySampling
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedRetrySampling
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigning
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigning
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningCoordinates
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningCoordinates
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# Adaptive complete-tree PRF idealization

The complete adaptive signing history is simulated with a persistent full-response cache.
Real/ideal experiment laws, function-query bounds and the three-law additive hop are proved here.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.RetrySampling
open GXMSS.PRFDerived.SigningSimulation

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- Ambient sampling makes no function calls; an eligible signing query makes
exactly its retry budget, including all prefetched draws. -/
private theorem adaptiveHandler_query_bound [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain) (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) :
    IsQueryBoundP ((adaptiveHandler hash enc projection budget core query).run history)
      (fun q => q.isRight = true)
      (if query.isRight then budget else 0) := by
  exact GXMSS.PRFDerived.SigningSimulation.signingHandler_query_bound
    (oracleScheme hash enc projection budget) core budget
    (oracleSign_bound hash enc projection budget core) query history

/-- The ideal function cache and synchronized signing history as one state machine. -/
private abbrev idealAdaptiveHandler [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT ((SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v)) ×
        ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) ProbComp)  :=
  GXMSS.PRFDerived.SigningSimulation.idealHandler (oracleScheme hash enc projection budget) core

/-- The generic GXMSS signing handler for one fixed key. -/
private abbrev genericFixedHandler [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (budget : ℕ) (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v)) ProbComp)  :=
  GXMSS.PRFDerived.SigningSimulation.fixedHandler (GXMSS.scheme hash enc budget) sk

/-- Cache states are related to a generic signing state when their consumed-epoch
histories agree and unused epochs have no retry responses. -/
private def CacheRelated
    (pp : PP) (left : (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) ×
      ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (right : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) : Prop :=
  left.1 = right ∧ RetryFresh (H := H) (R := R) pp left.1 left.2

/-- For any adaptive source program, the cached ideal function and generic signer
give the same forgery and first-request history from related states. -/
private theorem idealAdaptiveRun_projected {A : Type}
    [SampleableType H] [SampleableType R] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (hretry : RetrySamplingLaw projection) (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (program : OracleComp
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v)) A) (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp history cache) :
    (Prod.map id Prod.fst <$>
      (simulateQ (idealAdaptiveHandler hash enc projection budget
        (GXMSS.keys hash pp starts).2) program).run
        (history, cache)) =ᵈ
      (simulateQ (genericFixedHandler hash enc budget (GXMSS.keys hash pp starts).2)
        program).run history := by
  apply GXMSS.PRFDerived.SigningSimulation.signingRun_projected
    (oracleScheme hash enc projection budget) (GXMSS.scheme hash enc budget)
    (GXMSS.keys hash pp starts).2 (GXMSS.keys hash pp starts).2 (RetryFresh pp)
    ?_ ?_ program history cache hcache
  · intro epoch message hist table hfresh hunused
    change (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (oracleSign hash enc projection budget (GXMSS.keys hash pp starts).2
        epoch message)).run' table =ᵈ _
    rw [oracleSign_ideal_output hash enc projection budget epoch message
      pp starts hist table hfresh hunused]
    let : MeasurableSpace (Option (Signature R H h v)) := ⊤
    exact EvalDistEq.of_evalDist_eq (retry_sampling_sign hash enc projection budget hretry
      (GXMSS.keys hash pp starts).2 epoch message)
  · intro epoch message hist table hfresh _ result hresult
    exact oracleSign_ideal_preserves hash enc projection budget epoch message
      pp starts hist table hfresh result hresult

/-- Two-stage cached-ideal interpretation is the same combined handler. -/
private theorem idealAdaptiveHandler_compose {A : Type} [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (core : GXMSS.SecretKey PP H h v) (program : OracleComp
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v)) A) (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      ((simulateQ (adaptiveHandler hash enc projection budget core) program).run
        history)).run cache =
    (fun result : A × _ × _ =>
      let next := result.2
      ((result.1, next.1), next.2)) <$>
      (simulateQ (idealAdaptiveHandler hash enc projection budget core) program).run
        (history, cache) := by
  exact simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
    (adaptiveHandler hash enc projection budget core) program history cache

/-- One full adaptive interaction under the shared function oracle. -/
@[expose] def adaptiveInteraction [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response)
      (SyncSignatureUnforgeability.ExperimentResult
        (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := do
  let pp ← publicSeedQuery projection
  let starts ← startQueries projection pp
  let pair := GXMSS.keys hash pp starts
  let pk := pair.1
  let (forgery, history) ←
    (simulateQ (adaptiveHandler hash enc projection budget pair.2) (adv.forge pk)).run
      SyncSignatureUnforgeability.emptyHistory
  pure (pk, forgery, history)

/-- The reduction key generator retains its complete signing core locally. -/
private theorem adaptiveInteraction_from_material [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    adaptiveInteraction hash enc projection budget adv = (do
      let material ← keyMaterialQueries projection
      let pair := GXMSS.keys hash material.1 material.2
      let outcome ←
        (simulateQ (adaptiveHandler hash enc projection budget pair.2)
          (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
      pure (pair.1, outcome.1, outcome.2)) := by
  simp [adaptiveInteraction, keyMaterialQueries, bind_assoc]

/-- A Boolean observation of the full shared-oracle interaction. -/
@[expose] def randgenPRFReduction [DecidableEq H] [DecidableEq M] [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    : PRFScheme.PRFAdversary (GXMSS.PRFDerived.Query PP M h v) Response :=
  let alg := oracleScheme hash enc projection budget
  let run := adaptiveInteraction hash enc projection budget adv
  run.map (SyncSignatureUnforgeability.strongValid alg)

/-- Expose the initial ideal key material and retained cache before running the
adversary's complete adaptive signing interaction. -/
private theorem ideal_adaptive_interaction_setup [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (adaptiveInteraction hash enc projection budget adv)).run' ∅ =
    (do
      let initial ← (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        (keyMaterialQueries projection)).run ∅
      let material := initial.1
      let pk := (GXMSS.keys hash material.1 material.2).1
      let outcome ← (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        ((simulateQ (adaptiveHandler hash enc projection budget
          (GXMSS.keys hash material.1 material.2).2)
          (adv.forge pk)).run SyncSignatureUnforgeability.emptyHistory)).run'
          initial.2
      pure (pk, outcome)) := by
  rw [adaptiveInteraction_from_material]
  rw [simulateQ_bind, StateT.run'_bind']
  apply bind_congr
  intro initial
  rcases initial with ⟨⟨pp, starts⟩, cache⟩
  simp only [Prod.mk.eta, simulateQ_bind, StateT.run'_eq,
    StateT.run_bind, map_bind, bind_map_left]
  apply bind_congr
  intro result
  rfl

/-- A related initial cache lets the full ideal adaptive run project to one
generic GXMSS signing history. -/
private theorem ideal_adaptive_fixed_coupling
    [SampleableType H] [SampleableType R] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (hretry : RetrySamplingLaw projection) (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp
      SyncSignatureUnforgeability.emptyHistory cache)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      ((simulateQ (adaptiveHandler hash enc projection budget
        (GXMSS.keys hash pp starts).2)
        (adv.forge (GXMSS.keys hash pp starts).1)).run
          SyncSignatureUnforgeability.emptyHistory)).run' cache =ᵈ
    (simulateQ (genericFixedHandler hash enc budget
      (GXMSS.keys hash pp starts).2)
      (adv.forge (GXMSS.keys hash pp starts).1)).run
        SyncSignatureUnforgeability.emptyHistory := by
  rw [StateT.run'_eq]
  rw [idealAdaptiveHandler_compose]
  have hbridge := idealAdaptiveRun_projected hash enc projection budget hretry
    pp starts (adv.forge (GXMSS.keys hash pp starts).1)
    SyncSignatureUnforgeability.emptyHistory cache hcache
  simp only [Functor.map_map]
  convert hbridge using 1
  congr 1

/-- Generic key generation exposes the same seed/start material before the
synchronized adversary and signer run. -/
private theorem generic_interaction_material [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (budget : ℕ) (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    SyncSignatureUnforgeability.interaction (GXMSS.scheme hash enc budget) adv =
    (do
      let pp ← hash.thf.seedGen
      let starts ← GXMSS.sampleStarts H h v
      let pair := GXMSS.keys hash pp starts
      let outcome ← (simulateQ (genericFixedHandler hash enc budget pair.2)
        (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
      pure (pair.1, outcome)) := by
  unfold SyncSignatureUnforgeability.interaction GXMSS.scheme GXMSS.keygen
  simp only [bind_assoc, pure_bind]
  rfl

/-- The one-cache ideal PRF experiment and generic GXMSS have the same full
adaptive interaction law, including the forgery and consumed-epoch history. -/
private theorem ideal_adaptive_interaction_correspondence [SampleableType H]
    [SampleableType R] [DecidableEq H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v))
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
    (hretry : RetrySamplingLaw projection) :
    letI : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
    𝒟[(simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (adaptiveInteraction hash enc projection budget adv)).run' ∅] =
    𝒟[SyncSignatureUnforgeability.interaction
      (GXMSS.scheme hash enc budget) adv] := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (PP × (Fin (2 ^ h) → Fin v → H)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.ExperimentResult
    (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) := ⊤
  let setup := (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (keyMaterialQueries projection)).run
  let follow : (PP × (Fin (2 ^ h) → Fin v → H)) →
      ProbComp (SyncSignatureUnforgeability.ExperimentResult
        (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :=
    fun material => do
      let pair := GXMSS.keys hash material.1 material.2
      let outcome ← (simulateQ (genericFixedHandler hash enc budget pair.2)
        (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
      pure (pair.1, outcome)
  rw [ideal_adaptive_interaction_setup, generic_interaction_material]
  calc
    _ = 𝒟[do
      let initial ← setup ∅
      follow initial.1] := by
        apply OracleComp.evalDist_bind_congr_of_support
        intro initial hinitial
        rcases initial with ⟨⟨pp, starts⟩, cache⟩
        have hcache := keyMaterial_ideal_cache projection
          ((pp, starts), cache) hinitial
        have hfixed := ideal_adaptive_fixed_coupling hash enc projection budget
          hretry pp starts cache hcache adv
        convert (hfixed.map fun outcome =>
          (show SyncSignatureUnforgeability.ExperimentResult
            (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v) from
            ((GXMSS.keys hash pp starts).1, outcome))).evalDist_eq using 1 <;>
          (unfold SyncSignatureUnforgeability.ExperimentResult at *
           simp [follow, StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]
           rfl)
    _ = 𝒟[do
      let material ← (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        (keyMaterialQueries projection)).run' ∅
      follow material] := by
        change 𝒟[setup ∅ >>= fun initial => follow initial.1] =
          𝒟[(Prod.fst <$> setup ∅) >>= follow]
        rw [bind_map_left]
    _ = 𝒟[do
      let material ← (do
        let pp ← hash.thf.seedGen
        let starts ← GXMSS.sampleStarts H h v
        pure (pp, starts))
      follow material] := by
        rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
          keyMaterial_ideal_sampling hash projection hseed hstart]
    _ = _ := by
      simp [follow, bind_assoc]

/-- The real PRF handler supplies precisely the deterministic retry sequence. -/
private theorem retryQueries_real (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (key : Key) (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    simulateQ (prf.prfRealQueryImpl key)
      (retryQueries projection budget pp epoch message) =
    pure (GXMSS.PRFDerived.retryRandomizers budget prf.eval projection
      key pp epoch message) := by
  exact responseQueries_real prf projection.retryRandomizer budget
    (fun attempt => GXMSS.PRFDerived.Query.retry pp epoch message attempt.val) key

/-- Real oracle signing from the reduction's retained core agrees with
recomputation by the seed-only scheme for the same evaluator key. -/
private theorem oracleSign_real (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (key : Key) (budget : ℕ) (epoch : Fin (2 ^ h)) (message : M) :
    simulateQ (prf.prfRealQueryImpl key)
      (oracleSign hash enc projection budget
        (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
        epoch message) =
    GXMSS.PRFDerived.sign budget prf.eval projection hash enc key epoch message := by
  unfold oracleSign
  rw [simulateQ_bind]
  rw [retryQueries_real]
  rfl

/-- The source scheme with its sampled evaluator key fixed for one interaction. -/
private def fixedKeyScheme [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ) (key : Key) :
    SyncSignatureAlg ProbComp M (PublicKey PP H) Key
      (Signature R H h v) (Fin (2 ^ h)) where
  keygen := pure (GXMSS.PRFDerived.keys hash prf.eval projection key)
  sign := GXMSS.PRFDerived.sign budget prf.eval projection hash enc
  verify := GXMSS.verify hash enc

/-- The ordinary synchronized source handler for a fixed evaluator key. -/
private def fixedKeyHandler [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ) (key : Key) :
    QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
        (Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (Signature R H h v)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) ProbComp) +
    SyncSignatureUnforgeability.signingOracle
      (fixedKeyScheme hash enc prf projection budget key) key

/-- Per-query real simulation preserves the synchronized history, including failed
answers and already consumed epochs. -/
private theorem adaptiveHandler_real [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ) (key : Key)
    (query : (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (Signature R H h v)).Domain) (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) :
    simulateQ (prf.prfRealQueryImpl key)
      ((adaptiveHandler hash enc projection budget
        (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
        query).run history) =
    (fixedKeyHandler hash enc prf projection budget key query).run history := by
  cases query with
  | inl q =>
      simp [adaptiveHandler, fixedKeyHandler, PRFScheme.prfRealQueryImpl,
        QueryImpl.passthrough_add, QueryImpl.add_apply_inl]
  | inr q =>
      rcases q with ⟨epoch, message⟩
      cases hused : history epoch with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          simp only [adaptiveHandler, fixedKeyHandler, QueryImpl.add_apply_inr]
          change simulateQ (prf.prfRealQueryImpl key)
              (SyncSignatureUnforgeability.signingOracle
                (oracleScheme hash enc projection budget)
                  (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
                  (epoch, message) history) =
            SyncSignatureUnforgeability.signingOracle
              (fixedKeyScheme hash enc prf projection budget key) key
              (epoch, message) history
          rw [SyncSignatureUnforgeability.signingOracle_used (h := hused),
            SyncSignatureUnforgeability.signingOracle_used (h := hused)]
          simp
      | none =>
          simp only [adaptiveHandler, fixedKeyHandler, QueryImpl.add_apply_inr]
          change simulateQ (prf.prfRealQueryImpl key)
              (SyncSignatureUnforgeability.signingOracle
                (oracleScheme hash enc projection budget)
                  (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
                  (epoch, message) history) =
            SyncSignatureUnforgeability.signingOracle
              (fixedKeyScheme hash enc prf projection budget key) key
              (epoch, message) history
          rw [SyncSignatureUnforgeability.signingOracle_unused (h := hused),
            SyncSignatureUnforgeability.signingOracle_unused (h := hused)]
          simp only [simulateQ_bind, simulateQ_pure]
          change (do
            let answer ← simulateQ (prf.prfRealQueryImpl key)
              (oracleSign hash enc projection budget
                (GXMSS.PRFDerived.transientCore hash prf.eval projection key)
                epoch message)
            pure (answer, Function.update history epoch (some (message, answer)))) =
            (do
              let answer ← GXMSS.PRFDerived.sign budget prf.eval projection
                hash enc key epoch message
              pure (answer, Function.update history epoch (some (message, answer))))
          rw [oracleSign_real]

/-- The real oracle program has exactly the fixed-key synchronized interaction,
including its complete returned-failure and freshness observation. -/
private theorem adaptiveInteraction_real [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ) (key : Key)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) :
    simulateQ (prf.prfRealQueryImpl key)
      (adaptiveInteraction hash enc projection budget adv) =
    SyncSignatureUnforgeability.interaction
      (fixedKeyScheme hash enc prf projection budget key) adv := by
  unfold adaptiveInteraction
  rw [simulateQ_bind]
  simp only [publicSeedQuery, simulateQ_map,
    PRFScheme.simulateQ_prfRealQueryImpl_functionQuery, map_pure, pure_bind]
  rw [simulateQ_bind, startQueries_real]
  simp only [pure_bind]
  rw [simulateQ_bind]
  have hcomp := simulateQ_StateT_compose
    (adaptiveHandler hash enc projection budget
      (GXMSS.PRFDerived.transientCore hash prf.eval projection key)) (prf.prfRealQueryImpl key)
    (fixedKeyHandler hash enc prf projection budget key)
    (adaptiveHandler_real hash enc prf projection budget key)
    (adv.forge (GXMSS.PRFDerived.keys hash prf.eval projection key).1)
    SyncSignatureUnforgeability.emptyHistory
  dsimp [GXMSS.PRFDerived.transientCore, GXMSS.PRFDerived.keys,
    GXMSS.PRFDerived.publicSeed, GXMSS.PRFDerived.starts] at hcomp
  unfold GXMSS.PRFDerived.starts at hcomp
  rw [hcomp]
  rfl

/-- The real PRF distinguisher observes the complete strong synchronized game.
The same runtime interpretation therefore preserves missing mass as well as returned failure. -/
theorem randgenPRFReduction_real_strong [SampleableType Key] [DecidableEq H]
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
        (GXMSS.PRFDerived.scheme hash enc prf.eval projection budget) adv := by
  unfold PRFScheme.prfRealExperiment randgenPRFReduction
  rw [keyLaw]
  change (do
    let key ← $ᵗ Key
    simulateQ (prf.prfRealQueryImpl key)
      ((SyncSignatureUnforgeability.strongValid
        (oracleScheme hash enc projection budget)) <$>
        adaptiveInteraction hash enc projection budget adv)) = _
  simp only [simulateQ_map, adaptiveInteraction_real]
  unfold SyncSignatureUnforgeability.interaction GXMSS.PRFDerived.scheme
    GXMSS.PRFDerived.keygen
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply bind_congr
  intro key
  rfl

/-- The actual full-interaction distinguisher has a pathwise function-query bound.
The source bound charges every signing request; duplicate epochs only lower the cost. -/
theorem randgenPRFReduction_functionQuery_bound [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H h v)]
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget qs : ℕ)
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
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) (keyLaw : prf.UniformKey) :
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
    (hash : HashInstance PP T X H h w v) (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec
      (PublicKey PP H) (Fin (2 ^ h)) M (Signature R H h v)) (keyLaw : prf.UniformKey)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection)
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


end GXMSS.PRFDerived.Unforgeability
