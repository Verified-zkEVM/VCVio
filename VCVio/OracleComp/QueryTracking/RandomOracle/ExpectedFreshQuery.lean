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

end OracleComp



/-! ## Query-occurrence invariance under one-cell resampling -/

namespace OracleComp

variable {D α : Type} {R : D → Type}

/-- The probability of ever querying a key is unaffected by changing that key's table answer,
even when private uniform draws are interleaved with hash queries. -/
theorem prEvent_fixedTableLoggedRun_queries_mem_update [DecidableEq D]
    (oa : OracleComp (unifSpec + ofFn R) α) (g : ∀ d, R d)
    (t : D) (u : R t) (cache : (ofFn R).QueryCache) :
    Pr{let z ← (fixedTableLoggedRun oa (Function.update g t u) cache)}[
      t ∈ freshKeysOfLog z.1.2] =
    Pr{let z ← (fixedTableLoggedRun oa g cache)}[t ∈ freshKeysOfLog z.1.2] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
      simp [fixedTableLoggedRun]
  | query_bind q k ih =>
      cases q with
      | inl n =>
          have hrun (G : ∀ d, R d) :
              fixedTableLoggedRun (liftM ((unifSpec + ofFn R).query (.inl n)) >>= k)
                G cache =
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) n) >>= fun x =>
                fixedTableLoggedRun (k x) G cache := by
            rw [fixedTableLoggedRun_bind, fixedTableLoggedRun_uniformQuery]
            simp only [bind_map_left, List.nil_append, Prod.mk.eta]
            simp
          rw [hrun, hrun]
          apply prEvent_bind_congr
          intro x
          exact ih x cache
      | inr s =>
          have hrun (G : ∀ d, R d) :
              fixedTableLoggedRun (liftM ((unifSpec + ofFn R).query (.inr s)) >>= k)
                G cache =
              (((QueryImpl.ofFn G).liftTarget ProbComp).withCaching s).run cache >>= fun p =>
                (fun z => ((z.1.1, [⟨s, p.1⟩] ++ z.1.2), z.2)) <$>
                  fixedTableLoggedRun (k p.1) G p.2 := by
            rw [fixedTableLoggedRun_bind, fixedTableLoggedRun_hashQuery]
            simp only [bind_map_left]
          by_cases hst : s = t
          · subst s
            have hcase (G : ∀ d, R d) :
                Pr{let z ← (fixedTableLoggedRun
                  (liftM ((unifSpec + ofFn R).query (.inr t)) >>= k) G cache)}[
                    t ∈ freshKeysOfLog z.1.2] = 1 := by
              let run := fixedTableLoggedRun
                (liftM ((unifSpec + ofFn R).query (.inr t)) >>= k) G cache
              calc
                Pr{let z ← run}[t ∈ freshKeysOfLog z.1.2] =
                    Pr{let z ← run}[True] := by
                  dsimp [run]
                  rw [hrun]
                  apply prEvent_bind_congr
                  intro p
                  simp
                _ = 1 := by
                  dsimp [run]
                  let : MeasurableSpace
                      ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
                  rw [prEvent_true_eq_evalDist_apply_univ]
                  exact OracleComp.evalDist_apply_univ_eq_one _
            exact (hcase (Function.update g t u)).trans (hcase g).symm
          · rw [hrun, hrun]
            have hanswer : Function.update g t u s = g s :=
              Function.update_of_ne hst u g
            have hhandler :
                (((QueryImpl.ofFn (Function.update g t u)).liftTarget ProbComp).withCaching s).run
                  cache =
                  (((QueryImpl.ofFn g).liftTarget ProbComp).withCaching s).run cache := by
              rcases hc : cache s with _ | v
              · rw [QueryImpl.withCaching_run_none _ hc,
                  QueryImpl.withCaching_run_none _ hc]
                simp [QueryImpl.ofFn_apply, hanswer]
              · rw [QueryImpl.withCaching_run_some _ hc,
                  QueryImpl.withCaching_run_some _ hc]
            rw [hhandler]
            apply prEvent_bind_congr
            intro p
            rw [prEvent_map, prEvent_map]
            have hts : t ≠ s := Ne.symm hst
            simp only [List.singleton_append, freshKeysOfLog_cons,
              Finset.mem_insert, hts, false_or]
            exact ih p.1 p.2

end OracleComp

/-! ## Expected charge for interleaved private randomness -/

namespace OracleComp

variable {D α : Type} {R : D → Type}
variable [DecidableEq D] [Finite D]
  [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]

/-- If the conditional chance of a query event is constant across an outer draw, the joint
event factors into that query chance and the bad-answer chance. -/
theorem prEvent_bind_and_factor {A B : Type} (mx : ProbComp A) (my : A → ProbComp B)
    (queried : B → Prop) (bad : A → Prop) (q : ENNReal)
    (hq : ∀ a, Pr{let z ← my a}[queried z] = q) :
    Pr{let a ← mx; let z ← my a}[queried z ∧ bad a] =
      q * Pr{let a ← mx}[bad a] := by
  let : MeasurableSpace A := ⊤
  have hinner (a : A) :
      Pr{let z ← my a}[queried z ∧ bad a] =
        {a | bad a}.indicator (fun _ => q) a := by
    by_cases ha : bad a
    · simpa only [ha, and_true, Set.indicator_of_mem (show a ∈ {a | bad a} from ha)]
        using hq a
    · simp [ha, Set.indicator_of_notMem]
  have hbind := prEvent_bind_eq_lintegral_of_discrete mx
    (fun a => do let z ← my a; pure (queried z ∧ bad a)) id
  have hbind' :
      Pr{let a ← mx; let z ← my a}[queried z ∧ bad a] =
        ∫⁻ a, Pr{let z ← my a}[queried z ∧ bad a] ∂𝒟[mx] := by
    simpa only [bind_assoc, pure_bind, id_eq] using hbind
  rw [hbind']
  simp_rw [hinner]
  rw [lintegral_indicator_const MeasurableSet.of_discrete]
  rw [prEvent_eq_evalDist_of_discrete]

/-- A particular bad key is charged by the probability it appears in the fixed-table log,
including all interleaved private draws. -/
theorem prEvent_interleavedFreshKey_bad_le
    (oa : OracleComp (unifSpec + ofFn R) α) (t : D)
    (bad : D → (∀ d, R d) → Prop) (error : D → ENNReal)
    (hbad : ∀ g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error t) :
    Pr{let g ← $ᵗ (∀ d, R d); let z ← (fixedTableLoggedRun oa g ∅)}[
      t ∈ freshKeysOfLog z.1.2 ∧ bad t g] ≤
      Pr{let g ← $ᵗ (∀ d, R d); let z ← (fixedTableLoggedRun oa g ∅)}[
        t ∈ freshKeysOfLog z.1.2] * error t := by
  let : ∀ d, Fintype (R d) := fun d => Fintype.ofFinite (R d)
  have : Nonempty (∀ d, R d) := ⟨fun d => Classical.arbitrary (R d)⟩
  let : ∀ d, MeasurableSpace (R d) := fun _ => ⊤
  let f : (∀ d, R d) → ProbComp Prop := fun g => do
    let z ← fixedTableLoggedRun oa g ∅
    pure (t ∈ freshKeysOfLog z.1.2 ∧ bad t g)
  have hresample :
      𝒟[do
        let g ← $ᵗ (∀ d, R d)
        let z ← fixedTableLoggedRun oa g ∅
        pure (t ∈ freshKeysOfLog z.1.2 ∧ bad t g)] {True} =
      𝒟[do
        let u ← $ᵗ (R t)
        let g ← $ᵗ (∀ d, R d)
        let z ← fixedTableLoggedRun oa (Function.update g t u) ∅
        pure (t ∈ freshKeysOfLog z.1.2 ∧ bad t (Function.update g t u))] {True} := by
    have h := evalDist_bind_bind_update_dependent t ($ᵗ (R t))
      ($ᵗ (∀ d, R d)) SampleableType.evalDist_uniformSample
      SampleableType.evalDist_uniformSample f
    simpa only [f, bind_assoc] using congrArg (fun μ : Measure Prop => μ {True}) h.symm
  have hcell (g : ∀ d, R d) :
      Pr{let u ← $ᵗ (R t); let z ← (fixedTableLoggedRun oa (Function.update g t u) ∅)}[
        t ∈ freshKeysOfLog z.1.2 ∧ bad t (Function.update g t u)] ≤
      Pr{let z ← (fixedTableLoggedRun oa g ∅)}[t ∈ freshKeysOfLog z.1.2] * error t := by
    have hfactor := prEvent_bind_and_factor ($ᵗ (R t))
      (fun u => fixedTableLoggedRun oa (Function.update g t u) ∅)
      (fun z => t ∈ freshKeysOfLog z.1.2)
      (fun u => bad t (Function.update g t u))
      (Pr{let z ← (fixedTableLoggedRun oa g ∅)}[t ∈ freshKeysOfLog z.1.2])
      (fun u => prEvent_fixedTableLoggedRun_queries_mem_update oa g t u ∅)
    rw [hfactor]
    gcongr
    exact hbad g
  have hswap := evalDist_bind_bind_swap_of_countable
    ($ᵗ (R t)) ($ᵗ (∀ d, R d))
    (fun u g => do
      let z ← fixedTableLoggedRun oa (Function.update g t u) ∅
      pure (t ∈ freshKeysOfLog z.1.2 ∧ bad t (Function.update g t u)))
  rw [hresample, hswap]
  let : MeasurableSpace (∀ d, R d) := ⊤
  have hleft :
      (𝒟[do
        let g ← $ᵗ (∀ d, R d)
        let u ← $ᵗ (R t)
        let z ← fixedTableLoggedRun oa (Function.update g t u) ∅
        pure (t ∈ freshKeysOfLog z.1.2 ∧ bad t (Function.update g t u))]) {True} =
      ∫⁻ g,
      Pr{let u ← $ᵗ (R t); let z ← (fixedTableLoggedRun oa (Function.update g t u) ∅)}[
        t ∈ freshKeysOfLog z.1.2 ∧ bad t (Function.update g t u)]
        ∂𝒟[$ᵗ (∀ d, R d)] := by
    simpa only [bind_assoc, pure_bind, id_eq] using
      (prEvent_bind_eq_lintegral_of_discrete ($ᵗ (∀ d, R d))
        (fun g => do
          let u ← $ᵗ (R t)
          let z ← fixedTableLoggedRun oa (Function.update g t u) ∅
          pure (t ∈ freshKeysOfLog z.1.2 ∧ bad t (Function.update g t u))) id)
  have hright :
      Pr{let g ← $ᵗ (∀ d, R d); let z ← (fixedTableLoggedRun oa g ∅)}[
        t ∈ freshKeysOfLog z.1.2] =
      ∫⁻ g, Pr{let z ← (fixedTableLoggedRun oa g ∅)}[
        t ∈ freshKeysOfLog z.1.2] ∂𝒟[$ᵗ (∀ d, R d)] := by
    simpa only [bind_assoc, pure_bind, id_eq] using
      (prEvent_bind_eq_lintegral_of_discrete ($ᵗ (∀ d, R d))
        (fun g => do
          let z ← fixedTableLoggedRun oa g ∅
          pure (t ∈ freshKeysOfLog z.1.2)) id)
  rw [hleft, hright]
  calc
    ∫⁻ g,
    Pr{let u ← $ᵗ (R t); let z ← (fixedTableLoggedRun oa (Function.update g t u) ∅)}[
      t ∈ freshKeysOfLog z.1.2 ∧ bad t (Function.update g t u)] ∂𝒟[$ᵗ (∀ d, R d)]
      ≤ ∫⁻ g, Pr{let z ← (fixedTableLoggedRun oa g ∅)}[
          t ∈ freshKeysOfLog z.1.2] * error t ∂𝒟[$ᵗ (∀ d, R d)] :=
        lintegral_mono hcell
    _ = (∫⁻ g, Pr{let z ← (fixedTableLoggedRun oa g ∅)}[
      t ∈ freshKeysOfLog z.1.2] ∂𝒟[$ᵗ (∀ d, R d)]) * error t := by
      rw [lintegral_mul_const]
      exact Measurable.of_discrete

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

omit [Finite D] in
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

/-! ## Interleaved finite-domain expected fresh-query bound -/

namespace OracleComp

/-- A bad event witnessed by a genuinely queried key in every fixed-table trace is bounded by
the expected sum of per-key errors over the distinct keys in the actual cached run. -/
theorem prEvent_interleavedFreshBad_le_expectedCharge
    {D α : Type} {R : D → Type} [DecidableEq D] [Finite D]
    [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (event : α → Prop) (bad : D → (∀ d, R d) → Prop) (error : D → ENNReal)
    (htrace : ∀ g z, z ∈ support (fixedTableLoggedRun oa g ∅) →
      event z.1.1 → ∃ t ∈ freshKeysOfLog z.1.2, bad t g)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error t) :
    Pr{let z ← randomOracleLoggedRun oa ∅}[event z.1.1] ≤
      expectedFreshQueryCharge oa error := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  let : MeasurableSpace (∀ d, R d) := ⊤
  let : MeasurableSpace ((∀ d, R d) ×
    ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache)) := ⊤
  let mx : ProbComp ((∀ d, R d) ×
    ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache)) := do
      let g ← $ᵗ (∀ d, R d)
      let z ← fixedTableLoggedRun oa g ∅
      pure (g, z)
  have hkey (t : D) :
      Pr{let p ← mx}[t ∈ freshKeysOfLog p.2.1.2 ∧ bad t p.1] ≤
      Pr{let p ← mx}[t ∈ freshKeysOfLog p.2.1.2] * error t := by
    simpa only [mx, bind_assoc, pure_bind] using
      prEvent_interleavedFreshKey_bad_le oa t bad error (hbad t)
  have hunion := prEvent_bad_in_freshKeys_le_expectedCharge mx
    (fun p => freshKeysOfLog p.2.1.2) (fun t p => bad t p.1) error hkey
  have htarget :
      Pr{let p ← mx}[event p.2.1.1] ≤
      Pr{let p ← mx}[∃ t ∈ freshKeysOfLog p.2.1.2, bad t p.1] := by
    apply prEvent_mono_of_support
    intro p hp he
    obtain ⟨g, _, hp'⟩ := mem_support_bind_peel ($ᵗ (∀ d, R d))
      (fun g => do
        let z ← fixedTableLoggedRun oa g ∅
        pure (g, z)) hp
    obtain ⟨z, hz, hp''⟩ := mem_support_bind_peel (fixedTableLoggedRun oa g ∅)
      (fun z => pure (g, z)) hp'
    have hp_eq : p = (g, z) := eq_of_mem_support_pure (g, z) hp''
    subst p
    exact htrace g z hz he
  have heager : 𝒟[randomOracleLoggedRun oa ∅] = 𝒟[Prod.snd <$> mx] := by
    rw [evalDist_randomOracleLoggedRun_eq_fixedTable_finite oa ∅]
    simp only [completeTable_empty]
    simp only [mx, map_bind, map_pure, bind_pure]
  have hevent :
      Pr{let z ← randomOracleLoggedRun oa ∅}[event z.1.1] =
      Pr{let p ← mx}[event p.2.1.1] := by
    rw [prEvent_congr_of_evalDist_eq _ _ heager]
    rw [prEvent_map]
  have hcharge :
      (∫⁻ p, ∑ t ∈ freshKeysOfLog p.2.1.2, error t ∂𝒟[mx]) =
      expectedFreshQueryCharge oa error := by
    unfold expectedFreshQueryCharge freshQueryCharge
    rw [heager, evalDist_map_of_discrete]
    rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
  rw [hevent, ← hcharge]
  exact htarget.trans hunion

end OracleComp
