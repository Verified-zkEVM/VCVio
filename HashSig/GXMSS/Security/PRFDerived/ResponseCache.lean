/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# Full-response PRF cache transport

Finite query programs, cache restriction and relational couplings preserve complete responses
and their selected projections across the real and ideal function interfaces.
-/

public section
namespace GXMSS.PRFDerived.ResponseCache
open OracleComp OracleSpec ENNReal ProbabilityTheory MeasureTheory
open OracleComp.ProgramLogic.Relational


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


private def flatToMatrix {H : Type} (m n : ℕ) :
    (Fin (m * n) → H) ≃ (Fin m → Fin n → H) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl H)).trans
    (Equiv.curry (Fin m) (Fin n) H)


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
theorem ideal_cache_frame
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


/-- A projected output law and a support invariant give a coupling retaining the state relation. -/
theorem relTriple_of_projected_eq
    {A S T : Type} (source : ProbComp (A × S)) (target : ProbComp (A × T))
    (proj : S → T) (relation : S → T → Prop)
    (heq : Prod.map id proj <$> source =ᵈ target)
    (hsource : ∀ result ∈ support source, relation result.2 (proj result.2)) :
    RelTriple source target
      (fun left right => left.1 = right.1 ∧ relation left.2 right.2) := by
  have hself : RelTriple source source
      (fun left right => left.1 = right.1 ∧ relation left.2 (proj right.2)) := by
    apply relTriple_refl_of_mem_support
    intro result hresult
    exact ⟨rfl, hsource result hresult⟩
  have hmap : RelTriple (id <$> source) (Prod.map id proj <$> source)
      (fun left right => left.1 = right.1 ∧ relation left.2 right.2) :=
    relTriple_map (f := id) (g := Prod.map id proj) hself
  simpa only [id_map] using relTriple_of_evalDistEq_right heq hmap


end GXMSS.PRFDerived.ResponseCache
