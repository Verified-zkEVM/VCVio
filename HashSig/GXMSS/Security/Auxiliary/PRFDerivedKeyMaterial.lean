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
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedOracleQueries
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedOracleQueries
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedRetrySampling
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedRetrySampling
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningCoordinates
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningCoordinates
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# PRF key material and signing queries

The seed and chain-start query programs establish the complete-tree setup law and query budget.
The oracle signer returns the original optional signature observation.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.RetrySampling
open GXMSS.PRFDerived.SigningSimulation

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- The common seed and all reached starts, with the cache retained for signing. -/
private def keyMaterialQueries
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response)
      (PP × (Fin (2 ^ h) → Fin v → H)) := do
  let pp ← publicSeedQuery projection
  let starts ← startQueries projection pp
  pure (pp, starts)

private theorem keyMaterialQueries_bound
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) :
    IsTotalQueryBound (keyMaterialQueries (M := M) (h := h) (v := v) projection)
      (1 + 2 ^ h * v) := by
  unfold keyMaterialQueries
  apply isTotalQueryBound_bind (publicSeedQuery_bound (M := M) (h := h) (v := v) projection)
  intro pp
  have hrest := isTotalQueryBound_bind (n₂ := 0) (startQueries_bound (M := M) projection pp)
    (fun starts => (show IsTotalQueryBound
      (pure (pp, starts) : OracleComp
        (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response) _)
      0 from trivial))
  simpa using hrest

/-- The initial cached ideal samples its key material from independent response
coordinates, including the full matrix of reached starts. -/
private theorem keyMaterial_ideal_projected
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (keyMaterialQueries projection)).run' ∅ =
    (do
      let response ← ($ᵗ Response)
      let starts ← projectedStarts (h := h) (v := v) projection
      pure (projection.publicParameter response, starts)) := by
  unfold keyMaterialQueries
  rw [simulateQ_bind, StateT.run'_bind']
  simp only [publicSeedQuery, simulateQ_map,
    PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery, StateT.run_map]
  unfold OracleSpec.randomOracle
  rw [QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)]
  simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc,
    Function.comp_apply, pure_bind]
  apply bind_congr
  intro response
  rw [simulateQ_bind, StateT.run'_bind']
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  calc
    _ = (fun starts => (projection.publicParameter response, starts)) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        (startQueries projection (projection.publicParameter response))).run'
          ((∅ : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache).cacheQuery
            .publicSeed response) := by
          simp [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]
    _ = _ := by
      rw [startQueries_ideal]
      simp only [map_eq_bind_pure_comp]
      rfl

/-- Key material in the ideal game has exactly the generic key generator's law. -/
private theorem keyMaterial_ideal_sampling [SampleableType H]
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (hseed : PublicSeedSamplingLaw hash projection) (hstart : ChainStartSamplingLaw projection) :
    letI : MeasurableSpace (PP × (Fin (2 ^ h) → Fin v → H)) := ⊤
    𝒟[(simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (keyMaterialQueries projection)).run' ∅] =
      𝒟[do
        let pp ← hash.thf.seedGen
        let starts ← GXMSS.sampleStarts H h v
        pure (pp, starts)] := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (PP × (Fin (2 ^ h) → Fin v → H)) := ⊤
  rw [keyMaterial_ideal_projected]
  have hstarts := projectedStarts_sampling (h := h) (v := v) projection hstart
  have hreplace (pp : PP) :
      𝒟[(fun starts => (pp, starts)) <$>
        projectedStarts (h := h) (v := v) projection] =
      𝒟[(fun starts => (pp, starts)) <$> GXMSS.sampleStarts H h v] := by
    rw [evalDist_map _ Measurable.of_discrete, evalDist_map _ Measurable.of_discrete, hstarts]
  calc
    _ = 𝒟[do
      let response ← ($ᵗ Response)
      let starts ← GXMSS.sampleStarts H h v
      pure (projection.publicParameter response, starts)] := by
        apply evalDist_bind_congr
        intro response
        simpa [map_eq_bind_pure_comp] using
          hreplace (projection.publicParameter response)
    _ = 𝒟[do
      let pp ← projection.publicParameter <$> ($ᵗ Response)
      let starts ← GXMSS.sampleStarts H h v
      pure (pp, starts)] := by
        simp [map_eq_bind_pure_comp, bind_assoc]
    _ = _ := by
      unfold PublicSeedSamplingLaw at hseed
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, hseed]

/-- Every result of ideal key generation carries the cache invariant required
for the full adaptive interaction. -/
private theorem keyMaterial_ideal_cache
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (result : (PP × (Fin (2 ^ h) → Fin v → H)) ×
      ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (keyMaterialQueries projection)).run ∅)) :
    let material := result.1
    RetryFresh (H := H) (R := R) material.1
      SyncSignatureUnforgeability.emptyHistory result.2 := by
  unfold keyMaterialQueries at hresult
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨seedResult, hseedResult, htail⟩ := hresult
  unfold publicSeedQuery at hseedResult
  rw [simulateQ_map, StateT.run_map,
    PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery] at hseedResult
  unfold OracleSpec.randomOracle at hseedResult
  rw [QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _),
    support_map] at hseedResult
  obtain ⟨sampledSeed, hsampledSeed, hseedEq⟩ := hseedResult
  rw [support_map] at hsampledSeed
  obtain ⟨seedResponse, _, hsampledEq⟩ := hsampledSeed
  subst sampledSeed
  subst seedResult
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at htail
  obtain ⟨startResult, hstartResult, hpure⟩ := htail
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hpure
  subst result
  exact initial_retry_fresh projection
    (projection.publicParameter seedResponse) seedResponse
    startResult hstartResult

/-- A signing answer uses the key material retained by the reduction. Every
eligible call still requests its full retry budget, including draws after the
first successful encoding. -/
@[expose] def oracleSign (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (core : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response)
      (Option (Signature R H h v)) := do
  let randomizers ← retryQueries projection budget core.seed epoch message
  pure (GXMSS.PRFDerived.signResult hash enc core epoch message randomizers).output

end GXMSS.PRFDerived.Unforgeability
