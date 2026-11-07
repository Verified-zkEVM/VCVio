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
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedOracleQueries
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedOracleQueries
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedRetrySampling
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedRetrySampling
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# PRF setup sampling laws

Finite setup queries preserve repeated-coordinate cache behavior and the projected independent
start distribution. Retry queries retain every prefetched response.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.RetrySampling
open GXMSS.PRFDerived.SigningSimulation

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- One public-seed response consumes one PRF-function query. -/
private theorem publicSeedQuery_bound
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) :
    IsTotalQueryBound (publicSeedQuery (M := M) (h := h) (v := v) projection) 1 := by
  unfold publicSeedQuery
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (functionQuery_bound (S := Response)
      (GXMSS.PRFDerived.Query.publicSeed :
        GXMSS.PRFDerived.Query PP M h v))

/-- One start response consumes one PRF-function query. -/
private theorem startQuery_bound
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (pp : PP)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    IsTotalQueryBound (startQuery (M := M) projection pp epoch chain) 1 := by
  unfold startQuery
  exact (isQueryBound_map_iff _ _ _ _ _).mpr
    (functionQuery_bound (S := Response)
      (GXMSS.PRFDerived.Query.start pp epoch chain :
        GXMSS.PRFDerived.Query PP M h v))

/-- Root construction reaches every start: at most `2^h * v` function calls. -/
private theorem startQueries_bound
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (pp : PP) :
    IsTotalQueryBound (startQueries (M := M) (h := h) (v := v) projection pp)
      (2 ^ h * v) := by
  unfold startQueries
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  have hflat : IsTotalQueryBound
      (Fin.mOfFn (2 ^ h * v) fun index =>
        startQuery (M := M) projection pp (Fin.divNat index) (Fin.modNat index))
      ((2 ^ h * v) * 1) :=
    query_bound_fin_mOfFn _ fun index =>
      startQuery_bound projection pp (Fin.divNat index) (Fin.modNat index)
  simpa only [Nat.mul_one, IsTotalQueryBound] using hflat

private theorem startQueries_real (prf : SharedPRF Key PP M Response h v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (key : Key) (pp : PP) :
    simulateQ (prf.prfRealQueryImpl key) (startQueries projection pp) =
      pure (fun epoch chain =>
        projection.chainStart ((prf.eval key) (.start pp epoch chain))) := by
  unfold startQueries
  change simulateQ (prf.prfRealQueryImpl key)
    ((fun starts epoch chain => starts (finProdFinEquiv (epoch, chain))) <$>
      Fin.mOfFn (2 ^ h * v) fun index =>
        startQuery projection pp (Fin.divNat index) (Fin.modNat index)) = _
  rw [simulateQ_map]
  have hflat : simulateQ (prf.prfRealQueryImpl key)
      (Fin.mOfFn (2 ^ h * v) fun index =>
        startQuery projection pp (Fin.divNat index) (Fin.modNat index)) =
      pure (fun index => projection.chainStart ((prf.eval key)
        (.start pp (Fin.divNat index) (Fin.modNat index)))) := by
    apply simulateQ_fin_mOfFn_pure
    intro index
    simp [startQuery]
  rw [hflat]
  simp only [map_pure]
  congr
  funext epoch chain
  have hpair := (finProdFinEquiv (m := 2 ^ h) (n := v)).symm_apply_apply
    (epoch, chain)
  have hepoch := congrArg Prod.fst hpair
  have hchain := congrArg Prod.snd hpair
  change (finProdFinEquiv (epoch, chain)).divNat = epoch at hepoch
  change (finProdFinEquiv (epoch, chain)).modNat = chain at hchain
  rw [hepoch, hchain]

/-- Distinct flat indices select distinct serialized start-query constructors. -/
private theorem startInput_injective (pp : PP) : Function.Injective
    (fun index : Fin (2 ^ h * v) =>
      (GXMSS.PRFDerived.Query.start pp (Fin.divNat index) (Fin.modNat index) :
        GXMSS.PRFDerived.Query PP M h v)) := by
  intro i j hij
  obtain ⟨_, hepoch, hchain⟩ := GXMSS.PRFDerived.Query.start.inj hij
  let inverse := (finProdFinEquiv (m := 2 ^ h) (n := v)).symm
  apply inverse.injective
  exact Prod.ext hepoch hchain

/-- After the public-seed query, every start query is fresh in the cache. -/
private theorem startInput_fresh [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    (pp : PP) (response : Response) (index : Fin (2 ^ h * v)) :
    ((∅ : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache).cacheQuery
      .publicSeed response)
      (.start pp (Fin.divNat index) (Fin.modNat index)) = none := by
  rw [QueryCache.cacheQuery_of_ne]
  · exact QueryCache.empty_apply _
  · intro hcontra
    cases hcontra

/-- Independent projected abstract responses for the reached chain starts. -/
private def projectedStarts [SampleableType Response]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) :
    ProbComp (Fin (2 ^ h) → Fin v → H) :=
  flatToMatrix (2 ^ h) v <$> Fin.mOfFn (2 ^ h * v)
    (fun _ => projection.chainStart <$> ($ᵗ Response))

/-- Ideal-world start responses are independent once the seed query is cached. -/
private theorem startQueries_ideal [DecidableEq (GXMSS.PRFDerived.Query PP M h v)]
    [SampleableType Response] (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (pp : PP) (response : Response) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (startQueries projection pp)).run'
        ((∅ : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache).cacheQuery
          .publicSeed response) =
      projectedStarts (h := h) (v := v) projection := by
  unfold startQueries projectedStarts
  simp only [startQuery, ← Fin.mOfFn_map]
  change (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
    ((fun starts epoch chain => starts (finProdFinEquiv (epoch, chain))) <$>
      ((fun starts index => projection.chainStart (starts index)) <$>
        Fin.mOfFn (2 ^ h * v) (fun index => PRFScheme.functionQuery
          (R := Response) (GXMSS.PRFDerived.Query.start pp (Fin.divNat index)
            (Fin.modNat index)))))).run'
        ((∅ : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache).cacheQuery
          .publicSeed response) = _
  rw [simulateQ_map, simulateQ_map]
  rw [state_run'_map, state_run'_map]
  rw [ideal_fin_queries_fresh (2 ^ h * v)
    (fun index => (GXMSS.PRFDerived.Query.start pp (Fin.divNat index)
      (Fin.modNat index) : GXMSS.PRFDerived.Query PP M h v)) (startInput_injective pp)
    ((∅ : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache).cacheQuery
      .publicSeed response) (startInput_fresh pp response)]
  simp only [Functor.map_map]
  rfl

/-- The chain-start projection law lifts to the complete finite array of independent starts. -/
private theorem projectedStarts_sampling [SampleableType Response] [SampleableType H]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (hstart : ChainStartSamplingLaw projection) :
    letI : MeasurableSpace H := ⊤
    𝒟[projectedStarts (h := h) (v := v) projection] = 𝒟[GXMSS.sampleStarts H h v] := by
  let : MeasurableSpace H := ⊤
  unfold ChainStartSamplingLaw at hstart
  have hbase : 𝒟[projection.chainStart <$> ($ᵗ Response)] = uniformOn Set.univ := by
    rw [hstart]
    exact SampleableType.evalDist_uniformSample
  have hflat : 𝒟[Fin.mOfFn (2 ^ h * v)
      (fun _ => projection.chainStart <$> ($ᵗ Response))] = uniformOn Set.univ :=
    evalDist_mOfFn_const_uniform (2 ^ h * v)
      (projection.chainStart <$> ($ᵗ Response)) hbase
  have hinner : 𝒟[Fin.mOfFn v (fun _ : Fin v => ($ᵗ H))] = uniformOn Set.univ :=
    evalDist_mOfFn_const_uniform v ($ᵗ H) SampleableType.evalDist_uniformSample
  have hnested : 𝒟[GXMSS.sampleStarts H h v] = uniformOn Set.univ := by
    unfold GXMSS.sampleStarts
    exact evalDist_mOfFn_const_uniform (2 ^ h)
      (Fin.mOfFn v (fun _ : Fin v => ($ᵗ H))) hinner
  unfold projectedStarts
  rw [evalDist_map _ (Measurable.of_discrete : Measurable (flatToMatrix (2 ^ h) v :
    (Fin (2 ^ h * v) → H) → (Fin (2 ^ h) → Fin v → H))), hflat]
  rw [map_uniformOn_univ_of_bijective Measurable.of_discrete
    (flatToMatrix (2 ^ h) v).bijective]
  exact hnested.symm

/-- Query the ordered retry coordinates and project every response to a randomizer. -/
@[expose] def retryQueries (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response)
      (List R) :=
  (Fin.mOfFn budget fun attempt =>
    projection.retryRandomizer <$>
      PRFScheme.functionQuery (.retry pp epoch message attempt.val)).map List.ofFn

end GXMSS.PRFDerived.Unforgeability
