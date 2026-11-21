/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF
public import VCVio.OracleComp.QueryTracking.RandomOracle.FinMOfFn
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
public import VCVio.OracleComp.QueryTracking.QueryBound.FinMOfFn

/-!
# PRF query simulation through one full-response cache

Fresh finite inputs draw independent complete responses. Repeated inputs reuse their complete
cached response, and avoided inputs retain their cached value across an adaptive program.
-/

public section
namespace PRFScheme.QuerySimulation
open OracleComp OracleSpec
/-- One function query consumes one total oracle-query unit. -/
theorem functionQuery_bound {D S : Type} (query : D) :
    IsTotalQueryBound (PRFScheme.functionQuery (R := S) query) 1 := by
  unfold PRFScheme.functionQuery
  change IsTotalQueryBound
    ((liftM (OracleSpec.query (Sum.inr query) : OracleQuery
      (PRFScheme.PRFOracleSpec D S) S)) >>= fun response => pure response) 1
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by omega, fun _ => trivial⟩

/-- Mapping the visible value commutes with discarding only the final state. -/
theorem state_run'_map {S A B : Type} (f : A → B)
    (x : StateT S ProbComp A) (s : S) :
    (f <$> x).run' s = f <$> x.run' s := by
  simp [StateT.run'_eq, StateT.run_map, Functor.map_map]

/-- Distinct fresh PRF inputs return an ordered family of independent complete responses. -/
theorem ideal_fin_queries_fresh {D S : Type} [DecidableEq D] [SampleableType S]
    (n : ℕ) (q : Fin n → D) (hq : Function.Injective q)
    (cache : (D →ₒ S).QueryCache) (hfresh : ∀ i, cache (q i) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := S))
      (Fin.mOfFn n fun i => PRFScheme.functionQuery (R := S) (q i))).run' cache =
      Fin.mOfFn n (fun _ => ($ᵗ S)) := by
  have hprogram :
      simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := S))
          (Fin.mOfFn n fun i => PRFScheme.functionQuery (R := S) (q i)) =
        simulateQ (randomOracle (spec := D →ₒ S))
          (Fin.mOfFn n fun i => (liftM ((D →ₒ S).query (q i)) :
            OracleComp (D →ₒ S) S)) := by
    simp only [simulateQ_fin_mOfFn, PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery,
      simulateQ_spec_query]
  rw [hprogram]
  exact OracleComp.run'_fin_mOfFn_randomOracle_of_fresh n q hq cache hfresh

/-- A PRF program avoiding one input preserves its entire cached response at that input. -/
theorem ideal_cache_frame {D S A : Type} [DecidableEq D] [SampleableType S]
    (target : D) (oa : OracleComp (PRFScheme.PRFOracleSpec D S) A)
    (havoid : AllQueriesSatisfy oa
      (fun query => ∀ d, query = Sum.inr d → d ≠ target))
    (cache : (D →ₒ S).QueryCache) (result : A × (D →ₒ S).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := D) (R := S)) oa).run cache)) : result.2 target = cache target := by
  apply OracleComp.snd_apply_eq_of_mem_support_run_romImpl target ?_ hresult
  apply havoid.mono
  rintro (q | input) hq
  · trivial
  · exact hq input rfl

end PRFScheme.QuerySimulation
