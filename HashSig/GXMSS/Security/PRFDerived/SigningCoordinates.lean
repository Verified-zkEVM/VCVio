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
public import HashSig.GXMSS.Security.PRFDerived.KeyGeneration
import all HashSig.GXMSS.Security.PRFDerived.KeyGeneration
public import HashSig.GXMSS.Security.PRFDerived.OracleQueries
import all HashSig.GXMSS.Security.PRFDerived.OracleQueries
public import HashSig.GXMSS.Security.PRFDerived.ResponseCache
import all HashSig.GXMSS.Security.PRFDerived.ResponseCache
public import HashSig.GXMSS.Security.PRFDerived.RetrySampling
import all HashSig.GXMSS.Security.PRFDerived.RetrySampling
public import HashSig.GXMSS.Security.PRFDerived.SigningSimulation
import all HashSig.GXMSS.Security.PRFDerived.SigningSimulation
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# Retry coordinates and cache freshness

Retry inputs separate consumed epochs and preserve the full cached response before projection.
The per-call retry law retains early success and exhausted-budget failure.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.RetrySampling
open GXMSS.PRFDerived.SigningSimulation

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- Every reached retry input consumes one function-oracle call. -/
private theorem retryQueries_bound
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    IsTotalQueryBound (retryQueries (v := v) projection budget pp epoch message) budget := by
  exact responseQueries_bound projection.retryRandomizer budget
    (fun attempt => GXMSS.PRFDerived.Query.retry pp epoch message attempt.val)

/-- Independent projected responses for one eligible signing call's finite retry budget. -/
private def projectedRetries [SampleableType Response]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) : ProbComp (List R) :=
  List.ofFn <$> Fin.mOfFn budget (fun _ => projection.retryRandomizer <$> ($ᵗ Response))

/-- One projected response has exactly the canonical uniform retry-randomizer law. -/
@[expose] def RetrySamplingLaw [SampleableType Response] [SampleableType R]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace R := ⊤
  𝒟[projection.retryRandomizer <$> ($ᵗ Response)] = 𝒟[$ᵗ R]

/-- Eager projected retries retain the recursive signer's returned-output law. -/
private theorem retry_sampling_sign [SampleableType Response] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (hretry : RetrySamplingLaw projection)
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M) :
    letI : MeasurableSpace (Option (Signature R H h v)) := ⊤
    𝒟[(fun randomizers =>
      (GXMSS.PRFDerived.signResult hash enc sk epoch message randomizers).output) <$>
      projectedRetries projection budget] = 𝒟[GXMSS.sign hash enc budget sk epoch message] := by
  apply eager_retry_sampling projection.retryRandomizer hretry
    (fun randomizers => (GXMSS.PRFDerived.signResult hash enc sk epoch message randomizers).output)
    (fun r => (enc.value sk.seed message r epoch).map
      (fun word => GXMSS.signatureOfWord hash sk epoch (word, r)))
    (fun n => GXMSS.sign hash enc n sk epoch message) ?_ ?_ ?_ ?_ budget
  · rfl
  · intro r rs
    rw [GXMSS.PRFDerived.signResult_cons]
    cases hv : enc.value sk.seed message r epoch with
    | some word => simp only [GXMSS.PRFDerived.SignResult.output, Option.map_some]
    | none =>
        cases GXMSS.PRFDerived.signResult hash enc sk epoch message rs <;>
          simp only [GXMSS.PRFDerived.SignResult.output, Option.map_none]
  · rfl
  · intro n
    simp only [GXMSS.sign, IncomparableEncoding.retry, map_bind]
    apply bind_congr
    intro r
    cases enc.value sk.seed message r epoch <;> rfl

/-- Distinct retry attempts have distinct full PRF query inputs. -/
private theorem retryInput_injective (pp : PP) (epoch : Fin (2 ^ h))
    (message : M) (budget : ℕ) : Function.Injective
      (fun attempt : Fin budget =>
        (GXMSS.PRFDerived.Query.retry pp epoch message attempt.val :
          GXMSS.PRFDerived.Query PP M h v)) := by
  intro i j hij
  obtain ⟨_, _, _, hattempt⟩ := GXMSS.PRFDerived.Query.retry.inj hij
  exact Fin.ext hattempt

/-- Fresh cached-ideal retry inputs return independent uniform abstract responses. -/
private theorem retryQueries_ideal_fresh
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M)
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hfresh : ∀ attempt : Fin budget, cache (.retry pp epoch message attempt.val) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (retryQueries projection budget pp epoch message)).run' cache =
    projectedRetries projection budget := by
  exact responseQueries_ideal_fresh projection.retryRandomizer budget
    (fun attempt => GXMSS.PRFDerived.Query.retry pp epoch message attempt.val)
    (retryInput_injective pp epoch message budget) cache hfresh

/-- One signing call's retry draws cannot touch any different cache coordinate. -/
private theorem retryQueries_avoids
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M)
    (target : GXMSS.PRFDerived.Query PP M h v) (hneq : ∀ attempt : Fin budget,
      target ≠ .retry pp epoch message attempt.val) :
    AllQueriesSatisfy (retryQueries projection budget pp epoch message)
      (fun query => ∀ d, query = Sum.inr d → d ≠ target) := by
  exact responseQueries_avoids projection.retryRandomizer budget
    (fun attempt => GXMSS.PRFDerived.Query.retry pp epoch message attempt.val) target
    (fun attempt => (hneq attempt).symm)

/-- Retry inputs of every unused epoch are absent from the ideal cache. -/
private def RetryFresh
    (pp : PP) (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) : Prop :=
  ∀ epoch, history epoch = none → ∀ message attempt,
    cache (.retry pp epoch message attempt) = none

/-- An eligible signing call preserves retry freshness for every other unused epoch. -/
private theorem retryQueries_preserve_retryFresh
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (budget : ℕ) (pp : PP)
    (epoch : Fin (2 ^ h)) (message : M)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v)) (answer : Option (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (result : List R × ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp history cache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (retryQueries projection budget pp epoch message)).run cache)) :
    RetryFresh (H := H) (R := R) pp
      (Function.update history epoch (some (message, answer)))
      result.2 := by
  intro ep hunused msg attempt
  have hne : ep ≠ epoch := by
    intro heq
    subst ep
    simp [Function.update] at hunused
  have htarget : ∀ index : Fin budget, (GXMSS.PRFDerived.Query.retry pp ep msg attempt :
        GXMSS.PRFDerived.Query PP M h v) ≠
        .retry pp epoch message index.val := by
    intro index heq
    obtain ⟨_, hepoch, _, _⟩ := GXMSS.PRFDerived.Query.retry.inj heq
    exact hne hepoch
  rw [ideal_cache_frame (.retry pp ep msg attempt) _
    (retryQueries_avoids projection budget pp epoch message _ htarget)
    cache result hresult]
  exact hcache ep (by simpa [Function.update, hne] using hunused)
    msg attempt

/-- Every start query leaves retry inputs untouched. -/
private theorem startQueries_avoids_retry
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (pp : PP) (target : GXMSS.PRFDerived.Query PP M h v)
    (htarget : ∃ (seed : PP) (epoch : Fin (2 ^ h)) (message : M)
      (attempt : ℕ), target = .retry seed epoch message attempt) :
    AllQueriesSatisfy (startQueries projection pp)
      (fun query => ∀ d, query = Sum.inr d → d ≠ target) := by
  unfold startQueries
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  apply allQueriesSatisfy_fin_mOfFn
  intro index
  unfold startQuery
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  unfold PRFScheme.functionQuery
  rw [allQueriesSatisfy_query_iff]
  intro d hd
  cases hd
  obtain ⟨seed, epoch, message, attempt, rfl⟩ := htarget
  intro hcontra
  cases hcontra

/-- Public-seed and start queries leave every retry coordinate fresh. -/
private theorem initial_retry_fresh
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (pp : PP) (seedResponse : Response) (result : (Fin (2 ^ h) → Fin v → H) ×
      ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (startQueries projection pp)).run
        ((∅ : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache).cacheQuery
          .publicSeed seedResponse))) :
    RetryFresh (H := H) (R := R) pp SyncSignatureUnforgeability.emptyHistory result.2 := by
  intro epoch _ message attempt
  let target : GXMSS.PRFDerived.Query PP M h v :=
    .retry pp epoch message attempt
  have hframe := ideal_cache_frame target (startQueries projection pp)
    (startQueries_avoids_retry projection pp target
      ⟨pp, epoch, message, attempt, rfl⟩)
    ((∅ : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache).cacheQuery
      .publicSeed seedResponse) result hresult
  rw [hframe]
  rw [QueryCache.cacheQuery_of_ne]
  · exact QueryCache.empty_apply target
  · intro hcontra
    dsimp [target] at hcontra
    cases hcontra

end GXMSS.PRFDerived.Unforgeability
