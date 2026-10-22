/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerived.KeyMaterial
import all HashSig.GXMSS.Security.PRFDerived.KeyMaterial

/-!
# Cached PRF signing

Bounded retry queries use retained signing material and preserve freshness of every unused
epoch in the persistent ideal function cache.
-/

public section

namespace GXMSS.PRFDerived.Security

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- Query the finite retry budget in attempt order under the derived public parameter. -/
@[expose] def retryQueries (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response)
      (List R) :=
  (Fin.mOfFn budget fun attempt =>
    projection.retryRandomizer <$>
      PRFScheme.functionQuery (.retry pp epoch message attempt.val)).map List.ofFn

/-- Every reached retry input consumes one function-oracle call. -/
private theorem retryQueries_bound
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    IsTotalQueryBound (retryQueries (v := v) projection budget pp epoch message) budget := by
  unfold retryQueries
  change IsTotalQueryBound
    (List.ofFn <$> Fin.mOfFn budget (fun attempt => projection.retryRandomizer <$>
      PRFScheme.functionQuery (GXMSS.PRFDerived.Query.retry pp epoch message attempt.val)))
    budget
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  simpa only [Nat.mul_one, IsTotalQueryBound] using
    (query_bound_fin_mOfFn
      (fun attempt : Fin budget => projection.retryRandomizer <$>
        PRFScheme.functionQuery (GXMSS.PRFDerived.Query.retry pp epoch message attempt.val))
      (fun attempt => (isQueryBound_map_iff _ _ _ _ _).mpr
        (functionQuery_bound (S := Response)
          (GXMSS.PRFDerived.Query.retry pp epoch message attempt.val))))

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

/-- Eager canonical finite draws and recursive first-success retry have the
same returned-signature measure. -/
private theorem canonical_retries_sign [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M)
    (budget : ℕ) :
    letI : MeasurableSpace (Option (Signature R H h v)) := ⊤
    𝒟[(fun randomizers =>
      (GXMSS.PRFDerived.signResult hash enc sk epoch message randomizers).output) <$>
      (List.ofFn <$> Fin.mOfFn budget (fun _ => ($ᵗ R)))] =
    𝒟[GXMSS.sign hash enc budget sk epoch message] := by
  let : MeasurableSpace (Option (Signature R H h v)) := ⊤
  induction budget with
  | zero =>
      simp [Fin.mOfFn, GXMSS.PRFDerived.signResult_nil, GXMSS.sign,
        IncomparableEncoding.retry, GXMSS.PRFDerived.SignResult.output]
  | succ n ih =>
      simp only [Fin.mOfFn, map_bind, map_pure,
        List.ofFn_cons]
      simp only [GXMSS.sign, IncomparableEncoding.retry, map_bind]
      apply evalDist_bind_congr ($ᵗ R)
      intro randomizer
      cases hword : enc.value sk.seed message randomizer epoch with
      | none =>
          simp only [GXMSS.PRFDerived.signResult_cons, hword]
          have houtput (tail : Fin n → R) :
              (match GXMSS.PRFDerived.signResult hash enc sk epoch message
                  (List.ofFn tail) with
                | .success signature attempt consumed =>
                    GXMSS.PRFDerived.SignResult.success signature (attempt + 1)
                      (randomizer :: consumed)
                | .exhausted consumed =>
                    GXMSS.PRFDerived.SignResult.exhausted (randomizer :: consumed)).output =
              (GXMSS.PRFDerived.signResult hash enc sk epoch message
                (List.ofFn tail)).output := by
            cases GXMSS.PRFDerived.signResult hash enc sk epoch message
              (List.ofFn tail) <;> rfl
          calc
            _ = 𝒟[(fun tail =>
                (GXMSS.PRFDerived.signResult hash enc sk epoch message
                  (List.ofFn tail)).output) <$>
                  Fin.mOfFn n (fun _ => ($ᵗ R))] := by
              simp only [map_eq_bind_pure_comp]
              apply congrArg
              apply bind_congr
              intro tail
              exact congrArg pure (houtput tail)
            _ = _ := by simpa only [Functor.map_map, GXMSS.sign] using ih
      | some word =>
          simp only [GXMSS.PRFDerived.signResult_cons, hword,
            GXMSS.PRFDerived.SignResult.output, map_pure]
          simp only [OracleComp.evalDist_bind_const, Option.map_some]

/-- Independent projected finite retry draws have the canonical first-success
signer law, including returned exhaustion and missing mass. -/
private theorem retry_sampling_sign [SampleableType Response] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (hretry : RetrySamplingLaw projection)
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M) :
    letI : MeasurableSpace (Option (Signature R H h v)) := ⊤
    𝒟[(fun randomizers =>
      (GXMSS.PRFDerived.signResult hash enc sk epoch message randomizers).output) <$>
      projectedRetries projection budget] =
    𝒟[GXMSS.sign hash enc budget sk epoch message] := by
  have hsingle :
      (projection.retryRandomizer <$> ($ᵗ Response)) =ᵈ ($ᵗ R) := by
    let : MeasurableSpace R := ⊤
    exact EvalDistEq.of_evalDist_eq hretry
  have hseq (n : ℕ) :
      Fin.mOfFn n (fun _ => projection.retryRandomizer <$> ($ᵗ Response)) =ᵈ
      Fin.mOfFn n (fun _ => ($ᵗ R)) := by
    induction n with
    | zero => exact EvalDistEq.rfl
    | succ n ih =>
        change (do
          let head ← projection.retryRandomizer <$> ($ᵗ Response)
          let tail ← Fin.mOfFn n (fun _ => projection.retryRandomizer <$> ($ᵗ Response))
          pure (Fin.cons head tail : Fin (n + 1) → R)) =ᵈ
          (do
            let head ← ($ᵗ R)
            let tail ← Fin.mOfFn n (fun _ => ($ᵗ R))
            pure (Fin.cons head tail : Fin (n + 1) → R))
        exact hsingle.bind (fun _ => ih.bind fun _ => EvalDistEq.rfl)
  have hlist : projectedRetries projection budget =ᵈ
      (List.ofFn <$> Fin.mOfFn budget (fun _ => ($ᵗ R))) :=
    (hseq budget).map List.ofFn
  have hout := hlist.map (fun randomizers =>
    (GXMSS.PRFDerived.signResult hash enc sk epoch message randomizers).output)
  let : MeasurableSpace (Option (Signature R H h v)) := ⊤
  exact hout.evalDist_eq.trans
    (canonical_retries_sign hash enc sk epoch message budget)

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
    (hfresh : ∀ attempt : Fin budget,
      cache (.retry pp epoch message attempt.val) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (retryQueries projection budget pp epoch message)).run' cache =
    projectedRetries projection budget := by
  unfold retryQueries projectedRetries
  simp only [← Fin.mOfFn_map]
  change (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
    (List.ofFn <$> ((fun responses attempt => projection.retryRandomizer
      (responses attempt)) <$>
      Fin.mOfFn budget (fun attempt => PRFScheme.functionQuery
        (R := Response) (GXMSS.PRFDerived.Query.retry pp epoch message attempt.val))))).run'
      cache = _
  rw [simulateQ_map, simulateQ_map, state_run'_map, state_run'_map]
  rw [ideal_fin_queries_fresh budget
    (fun attempt : Fin budget =>
      (GXMSS.PRFDerived.Query.retry pp epoch message attempt.val :
        GXMSS.PRFDerived.Query PP M h v))
    (retryInput_injective pp epoch message budget) cache hfresh]

/-- One signing call's retry draws cannot touch any different cache coordinate. -/
private theorem retryQueries_avoids
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M)
    (target : GXMSS.PRFDerived.Query PP M h v)
    (hneq : ∀ attempt : Fin budget,
      target ≠ .retry pp epoch message attempt.val) :
    AllQueriesSatisfy (retryQueries projection budget pp epoch message)
      (fun query => ∀ d, query = Sum.inr d → d ≠ target) := by
  unfold retryQueries
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  apply allQueriesSatisfy_fin_mOfFn
  intro attempt
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  unfold PRFScheme.functionQuery
  rw [allQueriesSatisfy_query_iff]
  intro d hd
  cases hd
  exact (hneq attempt).symm

/-- Retry inputs of every unused epoch are absent from the ideal cache. -/
private def RetryFresh
    (pp : PP)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) : Prop :=
  ∀ epoch, history epoch = none → ∀ message attempt,
    cache (.retry pp epoch message attempt) = none

/-- An eligible signing call preserves retry freshness for every other unused epoch. -/
private theorem retryQueries_preserve_retryFresh
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (pp : PP)
    (epoch : Fin (2 ^ h)) (message : M)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (answer : Option (Signature R H h v))
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
  have htarget : ∀ index : Fin budget,
      (GXMSS.PRFDerived.Query.retry pp ep msg attempt :
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
    (pp : PP) (seedResponse : Response)
    (result : (Fin (2 ^ h) → Fin v → H) ×
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
  have hrest := isTotalQueryBound_bind (n₂ := 0)
    (startQueries_bound (M := M) projection pp)
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
    (hseed : PublicSeedSamplingLaw hash projection)
    (hstart : ChainStartSamplingLaw projection) :
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
    rw [evalDist_map _ Measurable.of_discrete,
      evalDist_map _ Measurable.of_discrete, hstarts]
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
    (budget : ℕ) (core : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h)) (message : M) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response)
      (Option (Signature R H h v)) := do
  let randomizers ← retryQueries projection budget core.seed epoch message
  pure (GXMSS.PRFDerived.signResult hash enc core epoch message randomizers).output

/-- For a fresh eligible epoch, signing uses the retained key material and the
disjoint retry inputs have their independent sampling law. -/
private theorem oracleSign_ideal_output
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (epoch : Fin (2 ^ h)) (message : M)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp history cache)
    (hunused : history epoch = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (oracleSign hash enc projection budget (GXMSS.keys hash pp starts).2
        epoch message)).run' cache =
    (fun randomizers =>
      (GXMSS.PRFDerived.signResult hash enc (GXMSS.keys hash pp starts).2
        epoch message randomizers).output) <$>
      projectedRetries projection budget := by
  let ideal := PRFScheme.prfIdealQueryImpl
    (D := GXMSS.PRFDerived.Query PP M h v) (R := Response)
  have hfresh : ∀ attempt : Fin budget,
      cache (.retry pp epoch message attempt.val) = none :=
    fun attempt => hcache epoch hunused message attempt.val
  unfold oracleSign
  simp only [GXMSS.keys]
  rw [simulateQ_bind, StateT.run'_bind']
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure,
    map_pure, bind_pure_comp]
  calc
    _ = (fun randomizers =>
        (GXMSS.PRFDerived.signResult hash enc
          ⟨pp, starts, GXMSS.endpoints hash pp starts⟩
          epoch message randomizers).output) <$>
        (simulateQ (PRFScheme.prfIdealQueryImpl
          (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
          (retryQueries projection budget pp epoch message)).run' cache := by
          simp [StateT.run'_eq, Functor.map_map]
    _ = _ := by
      simpa only [GXMSS.keys] using
        congrArg (fun draws => (fun randomizers =>
          (GXMSS.PRFDerived.signResult hash enc
            ⟨pp, starts, GXMSS.endpoints hash pp starts⟩
            epoch message randomizers).output) <$> draws)
          (retryQueries_ideal_fresh projection budget pp epoch message cache hfresh)

/-- The full cached-ideal signing state differs from the retry-draw state only by
the deterministic first-success output. -/
private theorem oracleSign_ideal_run_cached
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (epoch : Fin (2 ^ h)) (message : M)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (oracleSign hash enc projection budget (GXMSS.keys hash pp starts).2
        epoch message)).run cache =
    (fun result =>
      ((GXMSS.PRFDerived.signResult hash enc (GXMSS.keys hash pp starts).2
        epoch message result.1).output, result.2)) <$>
      (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
        (retryQueries projection budget pp epoch message)).run cache := by
  unfold oracleSign
  simp only [GXMSS.keys]
  rw [simulateQ_bind, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]

/-- Every ideal signing outcome, including returned failure, retains the cache
relation for the updated consumed-epoch history. -/
private theorem oracleSign_ideal_preserves
    [DecidableEq (GXMSS.PRFDerived.Query PP M h v)] [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (epoch : Fin (2 ^ h)) (message : M)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H)
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (Signature R H h v))
    (cache : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hcache : RetryFresh (H := H) (R := R) pp history cache)
    (result : Option (Signature R H h v) ×
      ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := GXMSS.PRFDerived.Query PP M h v) (R := Response))
      (oracleSign hash enc projection budget (GXMSS.keys hash pp starts).2
        epoch message)).run cache)) :
    RetryFresh (H := H) (R := R) pp
      (Function.update history epoch (some (message, result.1))) result.2 := by
  rw [oracleSign_ideal_run_cached hash enc projection budget epoch message
    pp starts cache, support_map] at hresult
  obtain ⟨retries, hretries, heq⟩ := hresult
  subst result
  exact retryQueries_preserve_retryFresh projection budget pp epoch message
    history _ cache retries hcache hretries

/-- One eligible signing call makes exactly its budgeted retry calls. -/
private theorem oracleSign_bound
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (budget : ℕ) (core : GXMSS.SecretKey PP H h v)
    (epoch : Fin (2 ^ h)) (message : M) :
    IsTotalQueryBound (oracleSign hash enc projection budget core epoch message)
      budget := by
  unfold oracleSign
  have hretry := retryQueries_bound (v := v) projection budget core.seed epoch message
  have hresult : ∀ randomizers,
      IsTotalQueryBound
        (pure (GXMSS.PRFDerived.signResult hash enc core
          epoch message randomizers).output : OracleComp
            (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v) Response) _)
        0 := fun _ => trivial
  simpa only [Nat.add_zero] using isTotalQueryBound_bind hretry hresult


end GXMSS.PRFDerived.Security
