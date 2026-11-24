/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF.QuerySimulation

/-!
# Querying a PRF for a list of projected responses

A PRF here returns a full response at each input: a value of some type `S`, often a tuple, from
which a caller reads only the part it needs through a projection `project : S → R`.
`responseQueries project n input` queries the function at `input 0, …, input (n - 1)` and returns
the list of projected responses.

The ideal PRF handler caches the full response, not the projected one. If two calls read different
parts of the response at the same input, the second call reuses the cached response, so both parts
come from the same random value, as they would under a real PRF. A cache that stored only one
projected part could not answer the second call consistently.

The lemmas give the query count of `responseQueries` (`responseQueries_bound`), its result under a
real key (`responseQueries_real`), its distribution at distinct inputs that are not yet cached
(`responseQueries_ideal_fresh`), and the inputs it never queries (`responseQueries_avoids`).

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055).
-/

public section
namespace PRFScheme.ResponseQueries
open OracleComp OracleSpec PRFScheme.QuerySimulation

/-- Query the function at `input 0, …, input (n - 1)` and project each response with `project`. -/
@[expose] def responseQueries {D S R : Type} (project : S → R) (n : ℕ) (input : Fin n → D) :
    OracleComp (PRFScheme.PRFOracleSpec D S) (List R) :=
  List.ofFn <$> Fin.mOfFn n (fun i => project <$> PRFScheme.functionQuery (input i))

/-- `responseQueries` makes at most `n` oracle queries. The bound counts one query per input,
including inputs whose responses a caller later ignores. -/
theorem responseQueries_bound {D S R : Type} (project : S → R)
    (n : ℕ) (input : Fin n → D) :
    IsTotalQueryBound (responseQueries project n input) n := by
  unfold responseQueries
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  simpa only [Nat.mul_one, IsTotalQueryBound] using
    OracleComp.isTotalQueryBound_fin_mOfFn (fun i => project <$> PRFScheme.functionQuery (input i))
      (fun i => (isQueryBound_map_iff _ _ _ _ _).mpr (functionQuery_bound (input i)))

/-- Under a real key, `responseQueries` returns the projected PRF values in input order. -/
theorem responseQueries_real {D S R Key : Type}
    (prf : PRFScheme Key D S) (project : S → R) (n : ℕ)
    (input : Fin n → D) (key : Key) :
    simulateQ (prf.prfRealQueryImpl key) (responseQueries project n input) =
      pure (List.ofFn fun i => project (prf.eval key (input i))) := by
  unfold responseQueries
  rw [simulateQ_map]
  rw [simulateQ_fin_mOfFn_pure (g := fun i => project (prf.eval key (input i)))
    (hfg := fun i => by simp)]
  rfl

/-- At distinct inputs that are not yet cached, the ideal handler returns `n` independent
projections of uniform responses. -/
theorem responseQueries_ideal_fresh {D S R : Type} [DecidableEq D]
    [SampleableType S] (project : S → R) (n : ℕ) (input : Fin n → D)
    (hinj : Function.Injective input) (cache : (D →ₒ S).QueryCache)
    (hfresh : ∀ i, cache (input i) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := S))
      (responseQueries project n input)).run' cache =
      List.ofFn <$> Fin.mOfFn n (fun _ => project <$> ($ᵗ S)) := by
  unfold responseQueries
  simp only [← Fin.mOfFn_map]
  rw [simulateQ_map, simulateQ_map, StateT.run'_map', StateT.run'_map',
    ideal_fin_queries_fresh n input hinj cache hfresh]

/-- If no input equals `target`, then `responseQueries` never queries the function at `target`. -/
theorem responseQueries_avoids {D S R : Type} (project : S → R)
    (n : ℕ) (input : Fin n → D) (target : D) (hneq : ∀ i, input i ≠ target) :
    AllQueriesSatisfy (responseQueries project n input)
      (fun query => ∀ d, query = Sum.inr d → d ≠ target) := by
  unfold responseQueries
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  apply OracleComp.allQueriesSatisfy_fin_mOfFn
  intro i
  rw [allQueriesSatisfy_def]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  rw [← allQueriesSatisfy_def]
  unfold PRFScheme.functionQuery
  rw [allQueriesSatisfy_query_iff]
  intro d hd
  cases hd
  exact hneq i

end PRFScheme.ResponseQueries
