/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF.QuerySimulation

/-!
# Projected finite PRF response queries

Each query caches its complete response before projection. Fresh-input sampling and first-success
output laws keep eager coordinate lists distinct from consumed retry prefixes.
-/

public section
namespace PRFScheme.ProjectedQueries
open OracleComp OracleSpec ProbabilityTheory MeasureTheory PRFScheme.QuerySimulation

/-- Query a finite list of typed inputs, projecting each complete cached response. -/
@[expose] def responseQueries {D S R : Type} (project : S → R) (n : ℕ) (input : Fin n → D) :
    OracleComp (PRFScheme.PRFOracleSpec D S) (List R) :=
  List.ofFn <$> Fin.mOfFn n (fun i => project <$> PRFScheme.functionQuery (input i))

/-- The eager list charges every input, including an unconsumed suffix. -/
theorem responseQueries_bound {D S R : Type} (project : S → R)
    (n : ℕ) (input : Fin n → D) :
    IsTotalQueryBound (responseQueries project n input) n := by
  unfold responseQueries
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  simpa only [Nat.mul_one, IsTotalQueryBound] using
    OracleComp.isTotalQueryBound_fin_mOfFn (fun i => project <$> PRFScheme.functionQuery (input i))
      (fun i => (isQueryBound_map_iff _ _ _ _ _).mpr (functionQuery_bound (input i)))

/-- The real handler returns the projections of its actual keyed responses in index order. -/
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

/-- Distinct fresh inputs yield independent projected responses, retaining returned mass. -/
theorem responseQueries_ideal_fresh {D S R : Type} [DecidableEq D]
    [SampleableType S] (project : S → R) (n : ℕ) (input : Fin n → D)
    (hinj : Function.Injective input) (cache : (D →ₒ S).QueryCache)
    (hfresh : ∀ i, cache (input i) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := S))
      (responseQueries project n input)).run' cache =
      List.ofFn <$> Fin.mOfFn n (fun _ => project <$> ($ᵗ S)) := by
  unfold responseQueries
  simp only [← Fin.mOfFn_map]
  rw [simulateQ_map, simulateQ_map, state_run'_map, state_run'_map,
    ideal_fin_queries_fresh n input hinj cache hfresh]

/-- A finite list avoiding one input leaves that input outside its complete query trace. -/
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

/-- Eager independent retry draws have the same returned-output law as recursive first success.
Only returned outputs are observed; the finite eager list is separate from consumed prefixes. -/
theorem eager_retry_sampling {R Response S : Type} [SampleableType R]
    [SampleableType Response] (project : Response → R)
    (hlaw : letI : MeasurableSpace R := ⊤; 𝒟[project <$> ($ᵗ Response)] = 𝒟[$ᵗ R])
    (output : List R → Option S) (trial : R → Option S)
    (direct : ℕ → ProbComp (Option S))
    (hnil : output [] = none)
    (hcons : ∀ r rs, output (r :: rs) = match trial r with
      | some result => some result | none => output rs)
    (hzero : direct 0 = pure none)
    (hsucc : ∀ n, direct (n + 1) = do
      let r ← $ᵗ R
      match trial r with
      | some result => pure (some result)
      | none => direct n)
    (budget : ℕ) :
    letI : MeasurableSpace (Option S) := ⊤
    𝒟[output <$> (List.ofFn <$> Fin.mOfFn budget
      (fun _ => project <$> ($ᵗ Response)))] = 𝒟[direct budget] := by
  have hsingle : (project <$> ($ᵗ Response)) =ᵈ ($ᵗ R) := by
    let : MeasurableSpace R := ⊤
    exact EvalDistEq.of_evalDist_eq hlaw
  have hseq (n : ℕ) : Fin.mOfFn n (fun _ => project <$> ($ᵗ Response)) =ᵈ
      Fin.mOfFn n (fun _ => ($ᵗ R)) := by
    induction n with
    | zero => exact EvalDistEq.rfl
    | succ n ih =>
        change (do
          let head ← project <$> ($ᵗ Response)
          let tail ← Fin.mOfFn n (fun _ => project <$> ($ᵗ Response))
          pure (Fin.cons head tail : Fin (n + 1) → R)) =ᵈ _
        exact hsingle.bind (fun _ => ih.bind fun _ => EvalDistEq.rfl)
  let : MeasurableSpace (Option S) := ⊤
  have hcanonical (n : ℕ) :
      𝒟[output <$> (List.ofFn <$> Fin.mOfFn n (fun _ => ($ᵗ R)))] = 𝒟[direct n] := by
    induction n with
    | zero => simp [Fin.mOfFn, hnil, hzero]
    | succ n ih =>
        rw [hsucc]
        simp only [Fin.mOfFn, map_bind, map_pure, List.ofFn_cons]
        apply evalDist_bind_congr ($ᵗ R)
        intro r
        simp only [hcons]
        cases trial r with
        | some result => simp only [OracleComp.evalDist_bind_const]
        | none => simpa [map_eq_bind_pure_comp, bind_assoc] using ih
  exact ((hseq budget).map List.ofFn |>.map output).evalDist_eq.trans (hcanonical budget)

end PRFScheme.ProjectedQueries
