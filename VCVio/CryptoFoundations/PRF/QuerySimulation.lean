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
# Query facts for the ideal PRF handler

The ideal PRF handler `PRFScheme.prfIdealQueryImpl` answers each function query with a lazily
sampled random function. Its cache stores, at each queried input, the whole value the function
returns there (the full response), so a later query at that input returns the same value. This
file proves three facts about that handler:

- a function query uses one query of the total query budget (`functionQuery_bound`);
- queries at distinct inputs that are not yet cached return independent uniform responses
  (`ideal_fin_queries_fresh`);
- a program that never queries an input leaves the cache entry at that input unchanged
  (`ideal_cache_frame`).

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055).
-/

public section
namespace PRFScheme.QuerySimulation
open OracleComp OracleSpec

/-- A function query makes one oracle query. -/
theorem functionQuery_bound {D S : Type} (query : D) :
    IsTotalQueryBound (PRFScheme.functionQuery (R := S) query) 1 := by
  unfold PRFScheme.functionQuery
  change IsTotalQueryBound
    ((liftM (OracleSpec.query (Sum.inr query) : OracleQuery
      (PRFScheme.PRFOracleSpec D S) S)) >>= fun response => pure response) 1
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by omega, fun _ => trivial⟩

/-- Querying distinct inputs that are not in the cache returns independent uniform responses, in
input order. -/
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

/-- If a program never queries the function at `target`, then every run of it under the ideal
handler leaves the cache entry at `target` unchanged. -/
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
