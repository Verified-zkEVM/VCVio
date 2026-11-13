/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF.QuerySimulation
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# PRF input-domain transport

Renaming function inputs forwards uniform queries unchanged. An injective renaming preserves
the entire native ideal experiment by pulling back its cache of complete responses.
-/

public section
namespace PRFScheme.DomainTransport
open OracleComp OracleSpec
variable {K D E S A : Type}

/-- Rename function inputs and forward private uniform queries unchanged. -/
@[expose] def inputMap (f : D → E) :
    QueryImpl (PRFScheme.PRFOracleSpec D S)
      (OracleComp (PRFScheme.PRFOracleSpec E S))
  | .inl n => (PRFScheme.PRFOracleSpec E S).query (.inl n)
  | .inr d => PRFScheme.functionQuery (f d)

/-- Restrict an evaluator to the selected inputs, preserving its actual key sampler. -/
@[expose] def pullback (prf : PRFScheme K E S) (f : D → E) : PRFScheme K D S where
  keygen := prf.keygen
  eval key d := prf.eval key (f d)

/-- Pull back complete cached responses along an input map. -/
@[expose] def pullbackCache (f : D → E) (cache : (E →ₒ S).QueryCache) :
    (D →ₒ S).QueryCache := QueryCache.ofFn fun d => cache (f d)

/-- Pulling back an empty full-response cache leaves it empty. -/
@[simp] theorem pullbackCache_empty (f : D → E) :
    pullbackCache (S := S) f ∅ = ∅ := rfl

private theorem pullbackCache_cacheQuery [DecidableEq D] [DecidableEq E]
    (f : D → E) (hf : Function.Injective f) (cache : (E →ₒ S).QueryCache)
    (d : D) (response : S) :
    pullbackCache f (cache.cacheQuery (f d) response) =
      (pullbackCache f cache).cacheQuery d response := by
  ext d'
  by_cases hd : d' = d
  · subst d'
    simp [pullbackCache]
  · have hfd : f d' ≠ f d := fun h => hd (hf h)
    simp [pullbackCache, QueryCache.cacheQuery_of_ne, hd, hfd]

private theorem ideal_step [DecidableEq D] [DecidableEq E] [SampleableType S]
    (f : D → E) (hf : Function.Injective f)
    (query : (PRFScheme.PRFOracleSpec D S).Domain) (cache : (E →ₒ S).QueryCache) :
    Prod.map id (pullbackCache f) <$>
        ((PRFScheme.prfIdealQueryImpl ∘ₛ inputMap f) query).run cache =
      (PRFScheme.prfIdealQueryImpl query).run (pullbackCache f cache) := by
  cases query with
  | inl n =>
      simp [inputMap, PRFScheme.prfIdealQueryImpl, OracleSpec.romImpl,
        unifFwdImpl, Prod.map, Functor.map_map]
  | inr d =>
      simp only [QueryImpl.apply_compose, inputMap,
        PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery,
        PRFScheme.prfIdealQueryImpl_apply_inr, randomOracle.run_eq]
      rw [show (pullbackCache f cache) d = cache (f d) from rfl]
      cases hc : cache (f d) with
      | some response => simp
      | none =>
          simp only [map_bind, map_pure]
          apply bind_congr
          intro response
          congr 1
          exact Prod.ext rfl (pullbackCache_cacheQuery f hf cache d response)

/-- Injective renaming preserves the whole native ideal run and its complete pulled-back cache. -/
theorem ideal_run [DecidableEq D] [DecidableEq E] [SampleableType S]
    (f : D → E) (hf : Function.Injective f)
    (oa : OracleComp (PRFScheme.PRFOracleSpec D S) A) (cache : (E →ₒ S).QueryCache) :
    Prod.map id (pullbackCache f) <$>
        (simulateQ PRFScheme.prfIdealQueryImpl (simulateQ (inputMap f) oa)).run cache =
      (simulateQ PRFScheme.prfIdealQueryImpl oa).run (pullbackCache f cache) := by
  rw [← QueryImpl.simulateQ_compose]
  exact map_run_simulateQ_eq_of_query_map_eq _ _ _ (ideal_step f hf) oa cache

/-- Injective input renaming preserves the whole ideal output program from a pulled-back cache. -/
theorem ideal_run' [DecidableEq D] [DecidableEq E] [SampleableType S]
    (f : D → E) (hf : Function.Injective f)
    (oa : OracleComp (PRFScheme.PRFOracleSpec D S) A) (cache : (E →ₒ S).QueryCache) :
    (simulateQ PRFScheme.prfIdealQueryImpl (simulateQ (inputMap f) oa)).run' cache =
      (simulateQ PRFScheme.prfIdealQueryImpl oa).run' (pullbackCache f cache) := by
  have hmap := congrArg (fun program => Prod.fst <$> program) (ideal_run f hf oa cache)
  simpa only [StateT.run'_eq, Functor.map_map, Function.comp_def, Prod.map_fst, id_eq]
    using hmap

/-- Native ideal experiments agree under an injective input renaming. -/
theorem ideal_experiment [DecidableEq D] [DecidableEq E] [SampleableType S]
    (f : D → E) (hf : Function.Injective f) (adversary : PRFScheme.PRFAdversary D S) :
    PRFScheme.prfIdealExperiment (simulateQ (inputMap f) adversary) =
      PRFScheme.prfIdealExperiment adversary := by
  exact ideal_run' f hf adversary ∅

/-- Native real experiments retain the same key draw under any input renaming. -/
theorem real_experiment (prf : PRFScheme K E S) (f : D → E)
    (adversary : PRFScheme.PRFAdversary D S) :
    prf.prfRealExperiment (simulateQ (inputMap f) adversary) =
      (pullback prf f).prfRealExperiment adversary := by
  unfold PRFScheme.prfRealExperiment
  apply bind_congr
  intro key
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  rintro (n | d)
  · simp [inputMap, PRFScheme.prfRealQueryImpl]
  · simp [inputMap, pullback]

/-- An input renaming preserves the native PRF advantage, without changing key sampling. -/
theorem advantage [DecidableEq D] [DecidableEq E] [SampleableType S]
    (prf : PRFScheme K E S) (f : D → E) (hf : Function.Injective f)
    (adversary : PRFScheme.PRFAdversary D S) :
    prf.prfAdvantage (simulateQ (inputMap f) adversary) =
      (pullback prf f).prfAdvantage adversary := by
  unfold PRFScheme.prfAdvantage
  rw [real_experiment, ideal_experiment f hf]

private theorem simulateQ_congr_on_queries {ι : Type} {spec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (left right : QueryImpl spec m) (oa : OracleComp spec A) (P : ι → Prop)
    (h : AllQueriesSatisfy oa P) (hstep : ∀ t, P t → left t = right t) :
    simulateQ left oa = simulateQ right oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at h
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [hstep t h.1]
      exact bind_congr fun response => ih response (h.2 response)

/-- A retraction preserves an entire program when it fixes every function input used there. -/
theorem inputMap_roundtrip (f : D → E) (g : E → D)
    (oa : OracleComp (PRFScheme.PRFOracleSpec E S) A)
    (h : AllQueriesSatisfy oa (fun query => ∀ d, query = Sum.inr d → f (g d) = d)) :
    simulateQ (inputMap f) (simulateQ (inputMap g) oa) = oa := by
  rw [← QueryImpl.simulateQ_compose]
  calc
    _ = simulateQ (QueryImpl.id' (PRFScheme.PRFOracleSpec E S)) oa := by
      apply simulateQ_congr_on_queries _ _ oa _ h
      rintro (n | d) hquery
      · simp [inputMap]
      · calc
          _ = PRFScheme.functionQuery (R := S) (f (g d)) := by
            simp [inputMap, PRFScheme.functionQuery]
          _ = PRFScheme.functionQuery d :=
            congrArg (PRFScheme.functionQuery (R := S)) (hquery d rfl)
          _ = _ := rfl
    _ = oa := by simp

/-- Function-query budgets are unchanged by renaming inputs, including repeated inputs. -/
theorem functionQuery_bound_iff (f : D → E)
    (oa : OracleComp (PRFScheme.PRFOracleSpec D S) A) (budget : ℕ) :
    IsQueryBoundP (simulateQ (inputMap f) oa) (fun q => q.isRight = true) budget ↔
      IsQueryBoundP oa (fun q => q.isRight = true) budget := by
  induction oa using OracleComp.inductionOn generalizing budget with
  | pure x => simp
  | query_bind query next ih =>
      cases query <;>
        simp [inputMap, PRFScheme.functionQuery,
          isQueryBoundP_query_bind_iff, ih]

end PRFScheme.DomainTransport
