/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.PRFDerivedScheme
public import VCVio.CryptoFoundations.SyncSignatureAlg
public import HashSig.GXMSS.Security.Unforgeability
public import VCVio.CryptoFoundations.PRF
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# Public-seed and chain-start PRF queries

One abstract response supplies the derived parameter and all chain starts. Fresh cached ideal
queries project to the required independent startup sampling laws.
-/

public section

namespace GXMSS.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding ENNReal GXMSS ProbabilityTheory MeasureTheory TweakableHash
open OracleComp.ProgramLogic.Relational

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- One keyed PRF supplies every query family through a common abstract response. -/
abbrev SharedPRF (Key PP M Response : Type) (h v : ℕ) :=
  PRFScheme Key (GXMSS.PRFDerived.Query PP M h v) Response

/-- The distinguished response has exactly the THF public-seed sampling law. -/
@[expose] def PublicSeedSamplingLaw [SampleableType Response]
    (hash : HashInstance PP T X H h w v)
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace PP := ⊤
  𝒟[projection.publicParameter <$> ($ᵗ Response)] =
    𝒟[(HashInstance.thf hash).seedGen]

/-- Each distinct chain-start response projects to the canonical uniform start law. -/
@[expose] def ChainStartSamplingLaw [SampleableType Response] [SampleableType H]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) : Prop :=
  letI : MeasurableSpace H := ⊤
  𝒟[projection.chainStart <$> ($ᵗ Response)] = 𝒟[$ᵗ H]

/-- A function-oracle query for the public parameter. -/
@[expose] def publicSeedQuery (projection : GXMSS.PRFDerived.Interpretation PP H R Response) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v)
      Response) PP :=
  projection.publicParameter <$> PRFScheme.functionQuery .publicSeed

/-- A function-oracle query for one start under the derived public parameter. -/
@[expose] def startQuery (projection : GXMSS.PRFDerived.Interpretation PP H R Response) (pp : PP)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v)
      Response) H :=
  projection.chainStart <$> PRFScheme.functionQuery (.start pp epoch chain)

/-- Read all starts under the parameter obtained from the first query. -/
@[expose] def startQueries (projection : GXMSS.PRFDerived.Interpretation PP H R Response)
    (pp : PP) :
    OracleComp (PRFScheme.PRFOracleSpec (GXMSS.PRFDerived.Query PP M h v)
      Response) (Fin (2 ^ h) → Fin v → H) :=
  (Fin.mOfFn (2 ^ h * v) fun index =>
    startQuery projection pp (Fin.divNat index) (Fin.modNat index)).map
      fun starts epoch chain => starts (finProdFinEquiv (epoch, chain))

private theorem simulateQ_fin_mOfFn_pure {ι : Type} {spec : OracleSpec ι} {α : Type}
    {n : ℕ} (impl : QueryImpl spec ProbComp) (f : Fin n → OracleComp spec α)
    (g : Fin n → α) (hfg : ∀ i, simulateQ impl (f i) = pure (g i)) :
    simulateQ impl (Fin.mOfFn n f) = pure g := by
  induction n with
  | zero =>
      simp only [Fin.mOfFn, simulateQ_pure]
      congr
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [Fin.mOfFn, simulateQ_bind]
      rw [hfg 0, ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hfg i.succ)]
      simp only [simulateQ_pure, pure_bind]
      congr
      funext i
      cases i using Fin.cases <;> rfl

private theorem query_bound_fin_mOfFn {ι : Type} {spec : OracleSpec ι} {α : Type}
    {n k : ℕ} (f : Fin n → OracleComp spec α)
    (hf : ∀ i, IsTotalQueryBound (f i) k) :
    IsTotalQueryBound (Fin.mOfFn n f) (n * k) := by
  induction n with
  | zero => simp [Fin.mOfFn, IsTotalQueryBound]
  | succ n ih =>
      simp only [Fin.mOfFn, Nat.succ_mul]
      rw [Nat.add_comm (n * k) k]
      apply isTotalQueryBound_bind (hf 0)
      intro x
      have htail := isTotalQueryBound_bind (n₂ := 0)
        (ih (fun i => f i.succ) (fun i => hf i.succ))
        (fun xs : Fin n → α => (show IsTotalQueryBound
          (pure (Fin.cons (α := fun _ : Fin (n + 1) => α) x xs) : OracleComp spec _) 0
          from trivial))
      simpa using htail

private theorem allQueriesSatisfy_fin_mOfFn {ι : Type} {spec : OracleSpec ι}
    {α : Type} {n : ℕ} (f : Fin n → OracleComp spec α) (P : ι → Prop)
    (hf : ∀ i, AllQueriesSatisfy (f i) P) :
    AllQueriesSatisfy (Fin.mOfFn n f) P := by
  induction n with
  | zero =>
      simp only [Fin.mOfFn]
      exact allQueriesSatisfy_pure _ _
  | succ n ih =>
      simp only [Fin.mOfFn]
      apply allQueriesSatisfy_bind (hf 0)
      intro x
      apply allQueriesSatisfy_bind
        (ih (fun i => f i.succ) (fun i => hf i.succ))
      intro xs
      exact allQueriesSatisfy_pure _ _

/-- A target query cost per charged source query scales a pathwise source bound.
Uncharged source queries contribute no target calls. -/
private theorem isQueryBoundP_simulateQ_run_weighted
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {S A : Type} {p : ι → Prop} [DecidablePred p]
    {q : ι' → Prop} [DecidablePred q]
    (impl : QueryImpl spec (StateT S (OracleComp spec')))
    (cost : ℕ)
    (hcharged : ∀ query, p query → ∀ state,
      IsQueryBoundP ((impl query).run state) q cost)
    (hfree : ∀ query, ¬ p query → ∀ state,
      IsQueryBoundP ((impl query).run state) q 0)
    (program : OracleComp spec A) (n : ℕ)
    (hprogram : IsQueryBoundP program p n) (state : S) :
    IsQueryBoundP ((simulateQ impl program).run state) q (n * cost) := by
  induction program using OracleComp.inductionOn generalizing n state with
  | pure value =>
      simp [simulateQ_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at hprogram
      rw [simulateQ_query_bind, StateT.run_bind]
      by_cases hp : p query
      · have hn : 0 < n := hprogram.1.resolve_left (not_not.mpr hp)
        have hrest : ∀ output : spec.Range query × S,
            IsQueryBoundP ((simulateQ impl (next output.1)).run output.2) q
              ((n - 1) * cost) :=
          fun output => ih output.1 (n - 1)
            (by simpa [hp] using hprogram.2 output.1) output.2
        have hbound := isQueryBoundP_bind (hcharged query hp state)
          (fun output _ => hrest output)
        have hn_eq : cost + (n - 1) * cost = n * cost := by
          calc
            cost + (n - 1) * cost = ((n - 1) + 1) * cost := by
              simp [Nat.add_mul, Nat.add_comm]
            _ = n * cost := by rw [Nat.sub_add_cancel hn]
        simpa [hp, hn_eq] using hbound
      · have hrest : ∀ output : spec.Range query × S,
            IsQueryBoundP ((simulateQ impl (next output.1)).run output.2) q
              (n * cost) :=
          fun output => ih output.1 n (by simpa [hp] using hprogram.2 output.1)
            output.2
        have hbound := isQueryBoundP_bind (hfree query hp state)
          (fun output _ => hrest output)
        simpa using hbound

private theorem functionQuery_bound {D S : Type} (query : D) :
    IsTotalQueryBound (PRFScheme.functionQuery (R := S) query) 1 := by
  unfold PRFScheme.functionQuery
  change IsTotalQueryBound
    ((liftM (OracleSpec.query (Sum.inr query) : OracleQuery
      (PRFScheme.PRFOracleSpec D S) S)) >>= fun response => pure response) 1
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by omega, fun _ => trivial⟩

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

private theorem ideal_fin_queries_fresh {D S : Type} [DecidableEq D] [SampleableType S]
    (n : ℕ) : ∀ (q : Fin n → D) (_hq : Function.Injective q)
    (cache : (D →ₒ S).QueryCache) (_hfresh : ∀ i, cache (q i) = none),
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := S))
      (Fin.mOfFn n fun i => PRFScheme.functionQuery (R := S) (q i))).run' cache =
    Fin.mOfFn n (fun _ : Fin n => ($ᵗ S)) := by
  induction n with
  | zero =>
      intro q _hq cache _hfresh
      simp only [Fin.mOfFn, simulateQ_pure]
      rfl
  | succ n ih =>
      intro q hq cache hfresh
      simp only [Fin.mOfFn, simulateQ_bind]
      rw [StateT.run'_bind']
      rw [PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery]
      have hzero : cache (q 0) = none := hfresh 0
      unfold OracleSpec.randomOracle
      rw [QueryImpl.withCaching_run_none _ hzero]
      simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro response
      have htail : Function.Injective (fun i : Fin n => q i.succ) :=
        fun _ _ eq => Fin.succ_injective n (hq eq)
      have hfreshTail : ∀ i : Fin n,
          (cache.cacheQuery (q 0) response) (q i.succ) = none := by
        intro i
        rw [QueryCache.cacheQuery_of_ne]
        · exact hfresh i.succ
        · intro eq
          exact Fin.succ_ne_zero i (hq eq)
      simp only [Function.comp_apply, pure_bind, simulateQ_pure, StateT.run'_eq,
        StateT.run_bind, StateT.run_pure, map_bind, map_pure]
      calc
        _ = (Fin.cons response) <$>
          (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := S))
            (Fin.mOfFn n fun i => PRFScheme.functionQuery (R := S) (q i.succ))).run'
              (cache.cacheQuery (q 0) response) := by
              simp [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]
        _ = _ := by
          rw [ih (fun i : Fin n => q i.succ) htail
            (cache.cacheQuery (q 0) response) hfreshTail]
          simp [map_eq_bind_pure_comp]

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


/-- Reindex a flat array of responses by epoch and chain. -/
private def flatToMatrix {H : Type} (m n : ℕ) :
    (Fin (m * n) → H) ≃ (Fin m → Fin n → H) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl H)).trans
    (Equiv.curry (Fin m) (Fin n) H)

/-- Independent projected abstract responses for the reached chain starts. -/
private def projectedStarts [SampleableType Response]
    (projection : GXMSS.PRFDerived.Interpretation PP H R Response) :
    ProbComp (Fin (2 ^ h) → Fin v → H) :=
  flatToMatrix (2 ^ h) v <$> Fin.mOfFn (2 ^ h * v)
    (fun _ => projection.chainStart <$> ($ᵗ Response))

private theorem state_run'_map {S A B : Type} (f : A → B)
    (x : StateT S ProbComp A) (s : S) :
    (f <$> x).run' s = f <$> x.run' s := by
  simp [StateT.run'_eq, StateT.run_map, Functor.map_map]

/-- A single ideal query to a different function input leaves one cache coordinate alone. -/
private theorem ideal_query_cache_ne
    {D S : Type} [DecidableEq D] [SampleableType S]
    (target : D) (query : (PRFScheme.PRFOracleSpec D S).Domain)
    (havoid : ∀ d, query = Sum.inr d → d ≠ target)
    (cache : (D →ₒ S).QueryCache)
    (result : (PRFScheme.PRFOracleSpec D S).Range query × (D →ₒ S).QueryCache)
    (hresult : result ∈ support ((PRFScheme.prfIdealQueryImpl
      (D := D) (R := S) query).run cache)) :
    result.2 target = cache target := by
  cases query with
  | inl q =>
      have hrun : ((PRFScheme.prfIdealQueryImpl
          (D := D) (R := S) (Sum.inl q)).run cache) =
          (fun response => (response, cache)) <$>
            (liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) := by
        rfl
      rw [hrun, support_map] at hresult
      rcases hresult with ⟨response, _, rfl⟩
      rfl
  | inr d =>
      have hne : d ≠ target := havoid d rfl
      rw [PRFScheme.prfIdealQueryImpl_apply_inr, randomOracle.run_eq] at hresult
      cases hc : cache d with
      | some response =>
          simp only [hc, support_pure, Set.mem_singleton_iff] at hresult
          rcases hresult with rfl
          rfl
      | none =>
          simp only [hc, support_bind, Set.mem_iUnion, support_pure,
            Set.mem_singleton_iff] at hresult
          obtain ⟨response, _, rfl⟩ := hresult
          exact QueryCache.cacheQuery_of_ne cache response hne.symm

/-- A program that avoids one function input cannot change its cached value. -/
private theorem ideal_cache_frame
    {D S A : Type} [DecidableEq D] [SampleableType S]
    (target : D) (oa : OracleComp (PRFScheme.PRFOracleSpec D S) A)
    (havoid : AllQueriesSatisfy oa
      (fun query => ∀ d, query = Sum.inr d → d ≠ target))
    (cache : (D →ₒ S).QueryCache)
    (result : A × (D →ₒ S).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := D) (R := S)) oa).run cache)) :
    result.2 target = cache target := by
  induction oa using OracleComp.inductionOn generalizing cache result with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | query_bind query next ih =>
      obtain ⟨hq, hnext⟩ :=
        (allQueriesSatisfy_query_bind_iff query next _).mp havoid
      rw [simulateQ_query_bind, StateT.run_bind, support_bind] at hresult
      simp only [Set.mem_iUnion] at hresult
      obtain ⟨intermediate, hstep, htail⟩ := hresult
      rw [ih intermediate.1 (hnext intermediate.1) intermediate.2 result htail]
      exact ideal_query_cache_ne target query hq cache intermediate hstep

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
      (Fin.modNat index) : GXMSS.PRFDerived.Query PP M h v))
    (startInput_injective pp)
    ((∅ : ((GXMSS.PRFDerived.Query PP M h v) →ₒ Response).QueryCache).cacheQuery
      .publicSeed response)
    (startInput_fresh pp response)]
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


end GXMSS.PRFDerived.Unforgeability
