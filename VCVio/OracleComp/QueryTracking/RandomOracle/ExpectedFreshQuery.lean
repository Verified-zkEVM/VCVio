/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun

/-!
# Expected charges for distinct cached random-oracle queries
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

/-! ## Joint lazy-versus-eager execution with interleaved private sampling -/

namespace OracleComp

variable {D α : Type} {R : D → Type}

/-- Sampling a finite complete answer assignment and then running fixed-table interleaved
execution gives the joint distribution of the actual cached run: output, ordered RO log, and
final cache. The proof is cache-parametrized for induction through a miss. -/
theorem evalDist_randomOracleLoggedRun_eq_fixedTable_finite
    [DecidableEq D] [Finite D]
    [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]
    [MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache)]
    [DiscreteMeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (cache : (ofFn R).QueryCache) :
    𝒟[randomOracleLoggedRun oa cache] =
      𝒟[($ᵗ (∀ d, R d)) >>= fun g =>
        fixedTableLoggedRun oa (completeTable cache g) cache] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
      simp [randomOracleLoggedRun, fixedTableLoggedRun]
  | query_bind q k ih =>
      cases q with
      | inl n =>
          rw [randomOracleLoggedRun_bind]
          simp_rw [fixedTableLoggedRun_bind]
          rw [randomOracleLoggedRun_uniformQuery]
          have hfixed (g : ∀ d, R d) :
              fixedTableLoggedRun
                  (liftM ((unifSpec + ofFn R).query (.inl n)) :
                    OracleComp (unifSpec + ofFn R) (Fin (n + 1)))
                  (completeTable cache g) cache =
                (fun u => ((u, ([] : QueryLog (ofFn R))), cache)) <$>
                  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) :=
            fixedTableLoggedRun_uniformQuery n (completeTable cache g) cache
          simp_rw [hfixed]
          simp only [bind_map_left, List.nil_append, Prod.mk.eta]
          have hid :
              (fun q : ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) => q) = id := rfl
          simp only [hid, id_map]
          let : ∀ d, Fintype (R d) := fun d => Fintype.ofFinite (R d)
          let : MeasurableSpace (∀ d, R d) := ⊤
          rw [evalDist_bind_bind_swap_of_countable]
          rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
          apply Measure.bind_congr_right
          filter_upwards [] with u
          exact ih u cache
      | inr t =>
          classical
          rw [randomOracleLoggedRun_bind]
          simp_rw [fixedTableLoggedRun_bind]
          rw [randomOracleLoggedRun_hashQuery]
          have hfixed (g : ∀ d, R d) :
              fixedTableLoggedRun
                  (liftM ((unifSpec + ofFn R).query (.inr t)) :
                    OracleComp (unifSpec + ofFn R) (R t))
                  (completeTable cache g) cache =
                (fun p => ((p.1, [⟨t, p.1⟩]), p.2)) <$>
                  ((((QueryImpl.ofFn (completeTable cache g)).liftTarget ProbComp).withCaching)
                    t).run cache :=
            fixedTableLoggedRun_hashQuery t (completeTable cache g) cache
          simp_rw [hfixed]
          simp only [bind_map_left]
          rcases hc : cache t with _ | u
          · rw [randomOracle.run_eq]
            simp only [hc]
            simp_rw [QueryImpl.withCaching_run_none _ hc]
            have hlift (g : ∀ d, R d) :
                (QueryImpl.liftTarget ProbComp (QueryImpl.ofFn (completeTable cache g))) t =
                  (pure (completeTable cache g t) : ProbComp (R t)) := by
              change (liftM (pure (completeTable cache g t) : Id (R t)) :
                ProbComp (R t)) = _
              rw [liftM_pure]
            simp_rw [hlift]
            simp only [map_pure, pure_bind, bind_map_left, bind_pure_comp]
            let : ∀ d, Fintype (R d) := fun d => Fintype.ofFinite (R d)
            have : Nonempty (∀ d, R d) := ⟨fun d => Classical.arbitrary (R d)⟩
            let : ∀ d, MeasurableSpace (R d) := fun _ => ⊤
            let ψ : (∀ d, R d) →
                ProbComp ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) :=
              fun g =>
                (fun q => ((q.1.1, [⟨t, completeTable cache g t⟩] ++ q.1.2), q.2)) <$>
                  fixedTableLoggedRun (k (completeTable cache g t))
                    (completeTable cache g)
                    (cache.cacheQuery t (completeTable cache g t))
            have hfun (u : R t) (g : ∀ d, R d) :
                (fun q => ((q.1.1, [⟨t, u⟩] ++ q.1.2), q.2)) <$>
                  fixedTableLoggedRun (k u) (completeTable (cache.cacheQuery t u) g)
                    (cache.cacheQuery t u) = ψ (Function.update g t u) := by
              have htable : completeTable (cache.cacheQuery t u) g =
                  completeTable cache (Function.update g t u) := by
                rw [completeTable_cacheQuery, completeTable_update_of_none cache g hc u]
              have hvalue : completeTable cache (Function.update g t u) t = u := by
                simp [completeTable, hc]
              simp only [ψ, hvalue, ← htable]
            change _ = 𝒟[$ᵗ (∀ d, R d) >>= ψ]
            trans 𝒟[do
              let u ← $ᵗ (R t)
              let g ← $ᵗ (∀ d, R d)
              ψ (Function.update g t u)]
            · apply evalDist_bind_congr
              intro u
              let front (q : (α × QueryLog (ofFn R)) × (ofFn R).QueryCache) :=
                ((q.1.1, [⟨t, u⟩] ++ q.1.2), q.2)
              change 𝒟[front <$> randomOracleLoggedRun (k u) (cache.cacheQuery t u)] = _
              calc
                _ = 𝒟[front <$> (($ᵗ (∀ d, R d)) >>= fun g =>
                    fixedTableLoggedRun (k u)
                      (completeTable (cache.cacheQuery t u) g)
                      (cache.cacheQuery t u))] := by
                  rw [evalDist_map_of_discrete, ih u (cache.cacheQuery t u)]
                  rw [← evalDist_map_of_discrete]
                _ = 𝒟[($ᵗ (∀ d, R d)) >>= fun g => ψ (Function.update g t u)] := by
                  simp only [map_bind]
                  apply evalDist_bind_congr
                  intro g
                  exact congrArg (fun x : ProbComp _ => 𝒟[x]) (hfun u g)
            · exact evalDist_bind_bind_update_dependent t ($ᵗ (R t))
                ($ᵗ (∀ d, R d)) SampleableType.evalDist_uniformSample
                SampleableType.evalDist_uniformSample ψ
          · rw [randomOracle.run_eq]
            simp only [hc]
            simp_rw [QueryImpl.withCaching_run_some _ hc]
            simp only [pure_bind]
            rw [evalDist_map_of_discrete]
            rw [ih u cache]
            rw [← evalDist_map_of_discrete]
            simp only [map_bind]
            trace_state

end OracleComp

/-! ## Finite-table expected bad-query bound -/

namespace OracleComp

variable {D α : Type} {R : D → Type}
variable [DecidableEq D] [Finite D]
  [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]

/-- A bad event at a particular queried key is charged only by the probability that the key
is queried. The query-occurrence event is unchanged by resampling that key's answer. -/
theorem prEvent_tableFreshKey_bad_le
    (oa : OracleComp (ofFn R) α) (t : D)
    (bad : D → (∀ d, R d) → Prop) (error : D → ENNReal)
    (hbad : ∀ g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error t) :
    Pr{let g ← $ᵗ (∀ d, R d)}[t ∈ tableFreshKeys oa g ∧ bad t g] ≤
      Pr{let g ← $ᵗ (∀ d, R d)}[t ∈ tableFreshKeys oa g] * error t := by
  let : ∀ d, MeasurableSpace (R d) := fun _ => ⊤
  let : MeasurableSpace (∀ d, R d) := ⊤
  rw [prEvent_uniformTable_update t]
  simp_rw [tableFreshKeys_mem_update oa]
  have hswap := evalDist_bind_bind_swap_of_countable
    ($ᵗ (R t)) ($ᵗ (∀ d, R d))
    (fun u g => pure (t ∈ tableFreshKeys oa g ∧ bad t (Function.update g t u)))
  change (𝒟[do
    let u ← $ᵗ (R t)
    let g ← $ᵗ (∀ d, R d)
    pure (t ∈ tableFreshKeys oa g ∧ bad t (Function.update g t u))]) {True} ≤ _
  rw [hswap]
  have hinner (g : ∀ d, R d) :
      Pr{let u ← $ᵗ (R t)}[t ∈ tableFreshKeys oa g ∧
        bad t (Function.update g t u)] ≤
      ({g' | t ∈ tableFreshKeys oa g'}.indicator (fun _ => error t)) g := by
    by_cases hq : t ∈ tableFreshKeys oa g
    · simpa [Set.indicator, hq] using hbad g
    · simp [Set.indicator, hq]
  have hbind := prEvent_bind_eq_lintegral_of_discrete
    ($ᵗ (∀ d, R d))
    (fun g => do let u ← $ᵗ (R t)
                 pure (t ∈ tableFreshKeys oa g ∧ bad t (Function.update g t u))) id
  have hbind' :
      (𝒟[do
        let g ← $ᵗ (∀ d, R d)
        let u ← $ᵗ (R t)
        pure (t ∈ tableFreshKeys oa g ∧ bad t (Function.update g t u))]) {True} =
      ∫⁻ g, Pr{let u ← $ᵗ (R t)}[t ∈ tableFreshKeys oa g ∧
        bad t (Function.update g t u)] ∂𝒟[$ᵗ (∀ d, R d)] := by
    simpa only [bind_assoc, pure_bind, id_eq] using hbind
  rw [hbind']
  calc
    ∫⁻ g, Pr{let u ← $ᵗ (R t)}[t ∈ tableFreshKeys oa g ∧
        bad t (Function.update g t u)] ∂𝒟[$ᵗ (∀ d, R d)]
      ≤ ∫⁻ g, ({g' | t ∈ tableFreshKeys oa g'}.indicator
          (fun _ => error t)) g ∂𝒟[$ᵗ (∀ d, R d)] :=
        lintegral_mono hinner
    _ = error t * 𝒟[$ᵗ (∀ d, R d)] {g | t ∈ tableFreshKeys oa g} :=
        lintegral_indicator_const MeasurableSet.of_discrete (error t)
    _ = Pr{let g ← $ᵗ (∀ d, R d)}[t ∈ tableFreshKeys oa g] * error t := by
        rw [prEvent_eq_evalDist_of_discrete]
        exact mul_comm _ _

/-- A finite union of key-specific bad events is charged by the expected sum of the weights
of the keys that actually appear. -/
private theorem prEvent_bad_in_freshKeys_le_expectedCharge
    {β : Type} [Fintype D] [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (mx : ProbComp β) (keys : β → Finset D) (bad : D → β → Prop)
    (error : D → ENNReal)
    (hkey : ∀ t, Pr{let a ← mx}[t ∈ keys a ∧ bad t a] ≤
      Pr{let a ← mx}[t ∈ keys a] * error t) :
    Pr{let a ← mx}[∃ t ∈ keys a, bad t a] ≤
      ∫⁻ a, ∑ t ∈ keys a, error t ∂𝒟[mx] := by
  classical
  have h : Pr{let a ← mx}[∃ t, t ∈ keys a ∧ bad t a] ≤
      ∫⁻ a, ∑ t, ({x | t ∈ keys x}.indicator (fun _ => error t)) a ∂𝒟[mx] := by
    calc
      _ ≤ ∑ t, Pr{let a ← mx}[t ∈ keys a ∧ bad t a] :=
        prEvent_exists_le mx (fun t a => t ∈ keys a ∧ bad t a)
      _ ≤ ∑ t, Pr{let a ← mx}[t ∈ keys a] * error t :=
        Finset.sum_le_sum (fun t _ => hkey t)
      _ = _ := by
        rw [lintegral_finsetSum]
        · apply Finset.sum_congr rfl
          intro t _
          rw [lintegral_indicator_const MeasurableSet.of_discrete]
          rw [prEvent_eq_evalDist_of_discrete]
          exact mul_comm _ _
        · intro t _
          exact measurable_const.indicator MeasurableSet.of_discrete
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_ite_mem,
    Finset.univ_inter] using h

/-- Under independent uniform answer cells, a bad event at any adaptively queried key is
bounded by the expected weight of the distinct keys in the actual deterministic trace. -/
theorem prEvent_tableFresh_bad_le_expectedCharge
    [MeasurableSpace (∀ d, R d)] [DiscreteMeasurableSpace (∀ d, R d)]
    (oa : OracleComp (ofFn R) α)
    (bad : D → (∀ d, R d) → Prop) (error : D → ENNReal)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error t) :
    Pr{let g ← $ᵗ (∀ d, R d)}[∃ t ∈ tableFreshKeys oa g, bad t g] ≤
      ∫⁻ g, ∑ t ∈ tableFreshKeys oa g, error t ∂𝒟[$ᵗ (∀ d, R d)] := by
  classical
  let : Fintype D := Fintype.ofFinite D
  exact prEvent_bad_in_freshKeys_le_expectedCharge ($ᵗ (∀ d, R d))
    (tableFreshKeys oa) bad error
    (fun t => prEvent_tableFreshKey_bad_le oa t bad error (hbad t))

end OracleComp
