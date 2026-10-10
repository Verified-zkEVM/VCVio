/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Adaptive queries with bad events depending on unqueried cells

A fresh-key bad event may depend on the entire random function, not merely the visible query
history. A uniform worst-case bound under resampling the tested cell gives a query-count bound
for every adaptive client. The proof fixes cached answers, exposes the next fresh response, and
recurses without conditioning on the absence of previous bad events.

The finite complete-table formulation is linked to the actual cached random oracle by the
dependent table execution theorem. The final result allows an infinite key domain: each fixed
finite-answer computation can be restricted to finitely many reachable keys without changing
its actual lazy execution. Unqueried coordinates outside that set are fixed inside the proof,
using hypotheses quantified over every background table. These results assert a statistical
bound, not an extraction or runtime claim for a particular cryptographic protocol.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleComp

variable {D α : Type} {R : D → Type}

/-- The actual query/response log from deterministic execution against a complete answer table. -/
@[expose] def tableQueryLog (oa : OracleComp (OracleSpec.ofFn R) α)
    (g : (d : D) → R d) : QueryLog (OracleSpec.ofFn R) :=
  ((simulateQ (QueryImpl.ofFn g).withLogging oa).run).2

/-- Returning a result makes no oracle queries. -/
@[simp] theorem tableQueryLog_pure (a : α) (g : (d : D) → R d) :
    tableQueryLog (pure a : OracleComp (OracleSpec.ofFn R) α) g = [] := by
  simp [tableQueryLog]
  rfl

/-- A query appears before the log of its answer-selected continuation. -/
@[simp] theorem tableQueryLog_query_bind (t : D) (k : R t → OracleComp (OracleSpec.ofFn R) α)
    (g : (d : D) → R d) :
    tableQueryLog (liftM ((OracleSpec.ofFn R).query t) >>= k) g =
      ⟨t, g t⟩ :: tableQueryLog (k (g t)) g := by
  simp [tableQueryLog, QueryImpl.ofFn, WriterT.run_bind, WriterT.run_tell]
  rfl

/-- A primitive query contributes its actual input and table answer to the log. -/
@[simp] theorem tableQueryLog_query (t : D) (g : ∀ d, R d) :
    tableQueryLog (liftM ((ofFn R).query t) : OracleComp (ofFn R) (R t)) g = [⟨t, g t⟩] := by
  simpa only [bind_pure, tableQueryLog_pure] using
    tableQueryLog_query_bind t (fun r => pure r) g


/-- Sequential computation concatenates the actual query logs. -/
theorem tableQueryLog_bind {β : Type} (oa : OracleComp (ofFn R) α)
    (ob : α → OracleComp (ofFn R) β) (g : ∀ d, R d) :
    tableQueryLog (oa >>= ob) g =
      tableQueryLog oa g ++ tableQueryLog (ob (evalWithAnswerFn (QueryImpl.ofFn g) oa)) g := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
      simp only [bind_assoc, tableQueryLog_query_bind, evalWithAnswerFn_bind,
        evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, ih, List.cons_append]

/-- The log of an oracle reduction concatenates the logs of its query implementations,
using the same answer table throughout. -/
theorem tableQueryLog_simulateQ {D' : Type} {R' : D' → Type} (g : ∀ d, R' d)
    (impl : QueryImpl (ofFn R) (OracleComp (ofFn R')))
    (oa : OracleComp (ofFn R) α) :
    tableQueryLog (simulateQ impl oa) g =
      (tableQueryLog oa (fun t => evalWithAnswerFn (QueryImpl.ofFn g) (impl t))).flatMap
        (fun q => tableQueryLog (impl q.1) g) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, tableQueryLog_bind,
        tableQueryLog_query, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, ih]


private theorem query_budget_tail [∀ d, Nonempty (R d)]
    (t : D) (k : R t → OracleComp (ofFn R) α) (error : D → ENNReal) (B : ENNReal)
    (hB : B ≠ ⊤)
    (hb : WorstCaseCostBound (liftM ((ofFn R).query t) >>= k) ⟨error⟩ B) :
    error t ≤ B ∧ ∀ u, WorstCaseCostBound (k u) ⟨error⟩ (B - error t) := by
  have h := (worstCaseCostBound_query_bind_iff t k ⟨error⟩ B).mp hb
  obtain ⟨u⟩ : Nonempty (R t) := inferInstance
  obtain ⟨z, hz⟩ := support_nonempty (costDist (k u) ⟨error⟩)
  have he : error t ≤ B := (le_add_right (le_refl _)).trans (h u z hz)
  refine ⟨he, fun u => ?_⟩
  rw [worstCaseCostBound_iff_support_bound]
  intro z hz
  exact ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top hB he) (h u z hz)


variable [DecidableEq D]

/-- Some actually queried coordinate, absent from the initial cache, is bad in the completed table.
The event may inspect every table cell, including cells never queried by the computation. -/
@[expose] def freshBadQuery (oa : OracleComp (OracleSpec.ofFn R) α)
    (c : (OracleSpec.ofFn R).QueryCache)
    (g : (d : D) → R d) (bad : D → (∀ d, R d) → Prop) : Prop :=
  ∃ q ∈ tableQueryLog oa (completeTable c g), c q.1 = none ∧ bad q.1 (completeTable c g)

omit [DecidableEq D] in
/-- A cache hit creates no new initially uncached bad coordinate. -/
theorem freshBadQuery_query_bind_of_some (t : D) (k : R t → OracleComp (OracleSpec.ofFn R) α)
    (c : (OracleSpec.ofFn R).QueryCache) (g : (d : D) → R d) (bad : D → (∀ d, R d) → Prop)
    {u : R t} (hc : c t = some u) :
    freshBadQuery (liftM ((OracleSpec.ofFn R).query t) >>= k) c g bad ↔
      freshBadQuery (k u) c g bad := by
  simp [freshBadQuery, tableQueryLog_query_bind, completeTable, hc]

/-- A fresh query separates its own bad event from new bad coordinates in the continuation. -/
theorem freshBadQuery_query_bind_of_none (t : D) (k : R t → OracleComp (OracleSpec.ofFn R) α)
    (c : (OracleSpec.ofFn R).QueryCache) (g : (d : D) → R d) (bad : D → (∀ d, R d) → Prop)
    (hc : c t = none) :
    freshBadQuery (liftM ((OracleSpec.ofFn R).query t) >>= k) c g bad ↔
      bad t (completeTable c g) ∨
      freshBadQuery (k (completeTable c g t))
        (c.cacheQuery t (completeTable c g t)) g bad := by
  rw [freshBadQuery, tableQueryLog_query_bind]
  simp only [List.mem_cons, exists_eq_or_imp, hc, true_and]
  unfold freshBadQuery
  rw [completeTable_cacheQuery_value]
  constructor
  · rintro (h | ⟨q, hq, hnone, hb⟩)
    · exact Or.inl h
    · by_cases heq : q.1 = t
      · exact Or.inl (heq ▸ hb)
      · exact Or.inr ⟨q, hq, (QueryCache.cacheQuery_of_ne c _ heq).trans hnone, hb⟩
  · rintro (h | ⟨q, hq, hnone, hb⟩)
    · exact Or.inl h
    · right
      refine ⟨q, hq, ?_, hb⟩
      by_cases heq : q.1 = t
      · subst heq
        simp at hnone
      · rwa [QueryCache.cacheQuery_of_ne c _ heq] at hnone

/-- Changing a cached fallback cell cannot affect the query log or its bad event. -/
theorem freshBadQuery_update_of_some (oa : OracleComp (OracleSpec.ofFn R) α)
    (c : (OracleSpec.ofFn R).QueryCache) (g : (d : D) → R d) (bad : D → (∀ d, R d) → Prop)
    {t : D} {v : R t} (hc : c t = some v) (u : R t) :
    freshBadQuery oa c (Function.update g t u) bad ↔ freshBadQuery oa c g bad := by
  simp only [freshBadQuery, completeTable_update_of_some c g hc u]

variable [Finite D] [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]

/-- A fresh uniform response may replace any cell before observing the entire table. -/
theorem prEvent_uniformTable_update (t : D) (event : (∀ d, R d) → Prop) :
    Pr{let g ← $ᵗ (∀ d, R d)}[event g] =
      Pr{let u ← $ᵗ (R t); let g ← $ᵗ (∀ d, R d)}[event (Function.update g t u)] := by
  let : ∀ d, MeasurableSpace (R d) := fun _ => ⊤
  have h := (evalDist_bind_bind_update_map_dependent t ($ᵗ (R t)) ($ᵗ (∀ d, R d))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample event).symm
  simpa only [prEvent_norm, evalDist_singleton_true] using
    congrArg (fun μ : Measure Prop => μ {True}) h

/-- A pointwise cell-resampling bound remains valid after fixing a cache
not containing that cell. -/
theorem prEvent_completeTable_cell_le (c : (OracleSpec.ofFn R).QueryCache) (t : D)
    (hc : c t = none) (bad : D → (∀ d, R d) → Prop) (ε : ℝ≥0∞)
    (hbad : ∀ g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ ε) :
    Pr{let g ← $ᵗ (∀ d, R d)}[bad t (completeTable c g)] ≤ ε := by
  let : ∀ d, MeasurableSpace (R d) := fun _ => ⊤
  let : MeasurableSpace (∀ d, R d) := ⊤
  rw [prEvent_uniformTable_update t]
  simp_rw [← completeTable_update_of_none c _ hc]
  let : MeasurableSpace Prop := ⊤
  have hswap := evalDist_bind_bind_swap_of_countable ($ᵗ (R t)) ($ᵗ (∀ d, R d))
    (fun u g => pure (bad t (Function.update (completeTable c g) t u)))
  have h' := (EvalDistEq.of_evalDist_eq hswap).prEvent_eq id
  simp only [prEvent_norm, id_eq] at h'
  rw [h']
  simpa only [prEvent_norm, id_eq] using
    (prEvent_bind_le_of_forall_le ($ᵗ (∀ d, R d))
      (fun g => (fun u => bad t (Function.update (completeTable c g) t u)) <$> ($ᵗ (R t)))
      id (fun g => by simpa only [prEvent_norm, id_eq] using hbad (completeTable c g)))

/-- Expose a fresh response before continuing the actual adaptive computation
under the extended cache. -/
theorem prEvent_freshBadQuery_suffix (t : D) (k : R t → OracleComp (OracleSpec.ofFn R) α)
    (c : (OracleSpec.ofFn R).QueryCache) (hc : c t = none) (bad : D → (∀ d, R d) → Prop) :
    Pr{let g ← $ᵗ (∀ d, R d)}[freshBadQuery (k (completeTable c g t))
      (c.cacheQuery t (completeTable c g t)) g bad] =
    Pr{let u ← $ᵗ (R t); let g ← $ᵗ (∀ d, R d)}[freshBadQuery (k u) (c.cacheQuery t u) g bad] := by
  rw [prEvent_uniformTable_update t]
  have hval (g : (d : D) → R d) (u : R t) : completeTable c (Function.update g t u) t = u := by
    simp [completeTable, hc]
  simp_rw [hval, freshBadQuery_update_of_some _ _ _ _ (QueryCache.cacheQuery_self _ _ _)]

/-- An adaptive computation making at most `n` queries encounters an initially uncached bad
coordinate with probability at most `n * ε`. The bad predicate may depend on unqueried table
entries. Its hypothesis must hold for every fixed background table, with only the tested
coordinate resampled. Query bounds count repeated calls; repeated keys retain the same bad event. -/
theorem prEvent_freshBadQuery_le (oa : OracleComp (OracleSpec.ofFn R) α) (n : ℕ)
    (hbound : IsTotalQueryBound oa n) (c : (OracleSpec.ofFn R).QueryCache)
    (bad : D → (∀ d, R d) → Prop) (ε : ℝ≥0∞)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ ε) :
    Pr{let g ← $ᵗ (∀ d, R d)}[freshBadQuery oa c g bad] ≤ n * ε := by
  induction oa using OracleComp.inductionOn generalizing n c with
  | pure a => simp [freshBadQuery]
  | query_bind t k ih =>
      obtain ⟨hn, hk⟩ := isTotalQueryBound_query_bind_iff.mp hbound
      cases hc : c t with
      | some u =>
          simp_rw [freshBadQuery_query_bind_of_some t k c _ bad hc]
          exact (ih u (n-1) (hk u) c).trans (by gcongr; exact Nat.sub_le n 1)
      | none =>
          simp_rw [freshBadQuery_query_bind_of_none t k c _ bad hc]
          apply (prEvent_or_le _ _ _).trans
          have hfirst := prEvent_completeTable_cell_le c t hc bad ε (hbad t)
          have hrest : Pr{let g ← $ᵗ (∀ d, R d)}[freshBadQuery (k (completeTable c g t))
              (c.cacheQuery t (completeTable c g t)) g bad] ≤ ((n-1 : ℕ) : ℝ≥0∞) * ε := by
            rw [prEvent_freshBadQuery_suffix t k c hc bad]
            simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
              pure_bind, id_eq] using
              (prEvent_bind_le_of_forall_le ($ᵗ (R t))
              (fun u => (fun g => freshBadQuery (k u) (c.cacheQuery t u) g bad) <$> ($ᵗ (∀ d, R d)))
              id (fun u => by simpa using ih u (n-1) (hk u) (c.cacheQuery t u)))
          calc
            _ ≤ ε + ((n-1 : ℕ) : ℝ≥0∞) * ε := add_le_add hfirst hrest
            _ = n * ε := by
              conv_lhs => lhs; rw [← one_mul ε]
              rw [← add_mul, ← Nat.cast_one, ← Nat.cast_add]
              congr 2
              omega

/-- Under a uniform complete answer table, any bad queried coordinate has probability at most
`n * ε` for an arbitrary adaptive `n`-query computation. No query-order restriction is imposed. -/
theorem prEvent_tableQueryLog_bad_le (oa : OracleComp (OracleSpec.ofFn R) α) (n : ℕ)
    (hbound : IsTotalQueryBound oa n) (bad : D → (∀ d, R d) → Prop) (ε : ℝ≥0∞)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ ε) :
    Pr{let g ← $ᵗ (∀ d, R d)}[∃ q ∈ tableQueryLog oa g, bad q.1 g] ≤ n * ε := by
  simpa [freshBadQuery, completeTable_empty] using
    prEvent_freshBadQuery_le oa n hbound ∅ bad ε hbad


/-- Bound an event in the actual cached-random-oracle execution by its bad queried keys.
The pointwise trace implication is deterministic. The resampling hypothesis can inspect every
unqueried cell, so no history-measurability or ancestor-first query order is required. -/
theorem prEvent_randomOracle_le_of_bad_queries_finite (oa : OracleComp (ofFn R) α) (n : ℕ)
    (hbound : IsTotalQueryBound oa n) (event : α → Prop)
    (bad : D → (∀ d, R d) → Prop) (ε : ℝ≥0∞)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ ε)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ q ∈ tableQueryLog oa g, bad q.1 g) :
    Pr{let result ← (simulateQ randomOracle oa).run' ∅}[event result] ≤ n * ε := by
  let : MeasurableSpace α := ⊤
  have heager := evalDist_simulateQ_randomOracle_run'_eq_completeTable oa ∅
  simp only [completeTable_empty] at heager
  rw [(EvalDistEq.of_evalDist_eq heager).prEvent_eq event]
  simp only [prEvent_norm]
  exact (prEvent_mono ($ᵗ (∀ d, R d)) _ _ htrace).trans
    (prEvent_tableQueryLog_bad_le oa n hbound bad ε hbad)


/-- A pathwise weighted query budget bounds encounters with initially uncached bad cells.
Each key has its own all-background-table resampling bound; repeated calls still incur
their key charge in the cost model, even though the cache preserves their answer. -/
theorem prEvent_freshBadQuery_le_weighted (oa : OracleComp (ofFn R) α)
    (error : D → ENNReal) (B : ENNReal)
    (hbound : WorstCaseCostBound oa ⟨error⟩ B) (c : (ofFn R).QueryCache)
    (bad : D → (∀ d, R d) → Prop)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error t) :
    Pr{let g ← $ᵗ (∀ d, R d)}[freshBadQuery oa c g bad] ≤ B := by
  induction oa using OracleComp.inductionOn generalizing B c with
  | pure a => simp [freshBadQuery]
  | query_bind t k ih =>
      by_cases hB : B = ⊤
      · simp [hB]
      obtain ⟨he, hk⟩ := query_budget_tail t k error B hB hbound
      cases hc : c t with
      | some u =>
          simp_rw [freshBadQuery_query_bind_of_some t k c _ bad hc]
          exact (ih u (B - error t) (hk u) c).trans tsub_le_self
      | none =>
          simp_rw [freshBadQuery_query_bind_of_none t k c _ bad hc]
          apply (prEvent_or_le _ _ _).trans
          have hfirst := prEvent_completeTable_cell_le c t hc bad (error t) (hbad t)
          have hrest : Pr{let g ← $ᵗ (∀ d, R d)}[freshBadQuery (k (completeTable c g t))
              (c.cacheQuery t (completeTable c g t)) g bad] ≤ B - error t := by
            rw [prEvent_freshBadQuery_suffix t k c hc bad]
            simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
              pure_bind, id_eq] using
              (prEvent_bind_le_of_forall_le ($ᵗ (R t))
              (fun u => (fun g => freshBadQuery (k u) (c.cacheQuery t u) g bad) <$>
                ($ᵗ (∀ d, R d))) id
              (fun u => by simpa using ih u (B - error t) (hk u) (c.cacheQuery t u)))
          calc
            _ ≤ error t + (B - error t) := add_le_add hfirst hrest
            _ = B := by rw [add_comm, tsub_add_cancel_of_le he]

/-- The weighted bad-query bound for the actual cached execution on a finite key domain. -/
theorem prEvent_randomOracle_le_of_bad_queries_weighted_finite (oa : OracleComp (ofFn R) α)
    (error : D → ENNReal) (B : ENNReal)
    (hbound : WorstCaseCostBound oa ⟨error⟩ B) (event : α → Prop)
    (bad : D → (∀ d, R d) → Prop)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error t)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ q ∈ tableQueryLog oa g, bad q.1 g) :
    Pr{let result ← (simulateQ randomOracle oa).run' ∅}[event result] ≤ B := by
  let : MeasurableSpace α := ⊤
  have heager := evalDist_simulateQ_randomOracle_run'_eq_completeTable oa ∅
  simp only [completeTable_empty] at heager
  rw [(EvalDistEq.of_evalDist_eq heager).prEvent_eq event]
  simp only [prEvent_norm]
  refine (prEvent_mono ($ᵗ (∀ d, R d)) _ _ htrace).trans ?_
  simpa [freshBadQuery, completeTable_empty] using
    prEvent_freshBadQuery_le_weighted oa error B hbound ∅ bad hbad

end OracleComp

/-! ## Removing the finite key-domain restriction -/

namespace OracleComp
variable {D α : Type} {R : D → Type}

/-- A finite set containing every key that can occur on any response branch of a program. -/
@[expose] noncomputable def possibleQueryKeys [DecidableEq D] [∀ d, Finite (R d)]
    (oa : OracleComp (ofFn R) α) : Finset D := by
  classical
  letI : ∀ d, Fintype (R d) := fun d => Fintype.ofFinite (R d)
  exact OracleComp.construct (C := fun _ => Finset D)
    (fun _ => ∅) (fun t _ rest => insert t (Finset.univ.biUnion rest)) oa

@[simp] theorem possibleQueryKeys_pure [DecidableEq D] [∀ d, Finite (R d)] (a : α) :
    possibleQueryKeys (pure a : OracleComp (ofFn R) α) = ∅ := rfl

@[simp] theorem possibleQueryKeys_query_bind [DecidableEq D] [∀ d, Finite (R d)]
    (t : D) (k : R t → OracleComp (ofFn R) α) :
    possibleQueryKeys (liftM ((ofFn R).query t) >>= k) =
      insert t (Set.Finite.toFinset
        (Set.finite_iUnion fun u => (possibleQueryKeys (k u)).finite_toSet)) := by
  classical
  ext q
  simp [possibleQueryKeys]

/-- Every query is in the finite key support determined by the program syntax. -/
theorem allQueriesSatisfy_possibleQueryKeys [DecidableEq D] [∀ d, Finite (R d)]
    (oa : OracleComp (ofFn R) α) : AllQueriesSatisfy oa (· ∈ possibleQueryKeys oa) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
      rw [allQueriesSatisfy_query_bind_iff]
      refine ⟨by simp, fun u => (ih u).mono fun d hd => ?_⟩
      simp only [possibleQueryKeys_query_bind, Finset.mem_insert, Set.Finite.mem_toFinset,
        Set.mem_iUnion, Finset.mem_coe]
      exact Or.inr ⟨u, hd⟩

/-- Retype a computation to a finite key set containing all its possible queries. -/
@[expose] noncomputable def restrictQueries (S : Finset D) :
    (oa : OracleComp (ofFn R) α) → AllQueriesSatisfy oa (· ∈ S) →
      OracleComp (ofFn (fun d : S => R d.val)) α
  | .pure a, _ => pure a
  | .queryBind t k, h =>
      liftM ((ofFn (fun d : S => R d.val)).query
        ⟨t, ((allQueriesSatisfy_query_bind_iff _ _ _).mp h).1⟩) >>=
        fun u => restrictQueries S (k u) (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u)

@[simp] theorem restrictQueries_pure (S : Finset D) (a : α) (h) :
    restrictQueries S (pure a : OracleComp (ofFn R) α) h = pure a := rfl

@[simp] theorem restrictQueries_query_bind (S : Finset D) (t : D)
    (k : R t → OracleComp (ofFn R) α) (h) :
    restrictQueries S (liftM ((ofFn R).query t) >>= k) h =
      liftM ((ofFn (fun d : S => R d.val)).query
        ⟨t, ((allQueriesSatisfy_query_bind_iff _ _ _).mp h).1⟩) >>=
        fun u => restrictQueries S (k u)
          (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) := rfl

private theorem restrictQueries_queryBound (S : Finset D) (oa : OracleComp (ofFn R) α)
    (h : AllQueriesSatisfy oa (· ∈ S)) (n : ℕ) (hb : IsTotalQueryBound oa n) :
    IsTotalQueryBound (restrictQueries S oa h) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
      exact ⟨hb.1, fun u => ih u
        (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) _ (hb.2 u)⟩

private theorem restrictQueries_costBound [∀ d, Nonempty (R d)]
    (S : Finset D) (oa : OracleComp (ofFn R) α) (h : AllQueriesSatisfy oa (· ∈ S))
    (error : D → ENNReal) (B : ENNReal) (hb : WorstCaseCostBound oa ⟨error⟩ B) :
    WorstCaseCostBound (restrictQueries S oa h) ⟨fun t => error t.val⟩ B := by
  induction oa using OracleComp.inductionOn generalizing B with
  | pure a => simp [restrictQueries_pure]
  | query_bind t k ih =>
      by_cases hB : B = ⊤
      · rw [worstCaseCostBound_iff_support_bound]
        simp [hB]
      obtain ⟨he, hk⟩ := query_budget_tail t k error B hB hb
      rw [restrictQueries_query_bind, worstCaseCostBound_query_bind_iff]
      intro u z hz
      have hku := ih u (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u)
        (B - error t) (hk u)
      have hzle := (worstCaseCostBound_iff_support_bound _ _ _).mp hku z hz
      calc
        _ ≤ error t + (B - error t) := add_le_add (le_refl (error t)) hzle
        _ = B := by rw [add_comm, tsub_add_cancel_of_le he]

/-- Restricting keys and the answer table preserves deterministic execution. -/
theorem evalWithAnswerFn_restrictQueries (S : Finset D) (oa : OracleComp (ofFn R) α)
    (h : AllQueriesSatisfy oa (· ∈ S)) (g : ∀ d, R d) :
    evalWithAnswerFn (QueryImpl.ofFn (fun d : S => g d.val)) (restrictQueries S oa h) =
      evalWithAnswerFn (QueryImpl.ofFn g) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
      simp only [restrictQueries_query_bind, evalWithAnswerFn_bind,
        evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
      exact ih _ (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 _)

/-- Re-embedding the restricted query log recovers the complete ordered query log. -/
theorem tableQueryLog_restrictQueries (S : Finset D) (oa : OracleComp (ofFn R) α)
    (h : AllQueriesSatisfy oa (· ∈ S)) (g : ∀ d, R d) :
    (tableQueryLog (restrictQueries S oa h) (fun d : S => g d.val)).map
      (fun q => (⟨q.1.val, q.2⟩ : Σ d, R d)) = tableQueryLog oa g := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
      simp only [restrictQueries_query_bind, tableQueryLog_query_bind, List.map_cons]
      exact congrArg (List.cons _) (ih _ (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 _))

/-- Restrict a cached answer assignment to a finite key set. -/
@[expose] def restrictCache (S : Finset D) (c : (ofFn R).QueryCache) :
    (ofFn (fun d : S => R d.val)).QueryCache :=
  QueryCache.ofFn (fun d => c d.val)

/-- Restriction commutes with updating a key in the retained set. -/
theorem restrictCache_update [DecidableEq D] (S : Finset D) (c : (ofFn R).QueryCache)
    (t : S) (u : R t.val) :
    restrictCache S (c.cacheQuery t.val u) = (restrictCache S c).cacheQuery t u := by
  apply QueryCache.ext
  intro q
  by_cases hq : q = t
  · subst q
    simp [restrictCache]
  · have hv : q.val ≠ t.val := fun h => hq (Subtype.ext h)
    simp [restrictCache, QueryCache.cacheQuery_of_ne _ _ hq,
      QueryCache.cacheQuery_of_ne _ _ hv]

private theorem randomOracle_query_bind_run' [DecidableEq D] [∀ d, SampleableType (R d)]
    (t : D) (k : R t → OracleComp (ofFn R) α) (c : (ofFn R).QueryCache) :
    (simulateQ randomOracle (liftM ((ofFn R).query t) >>= k)).run' c =
      ((randomOracle (spec := ofFn R) t).run c) >>=
        fun p => (simulateQ randomOracle (k p.1)).run' p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- Retyping possible keys preserves the actual cached output computation. -/
theorem randomOracle_restrictQueries [DecidableEq D] [∀ d, SampleableType (R d)]
    (S : Finset D) (oa : OracleComp (ofFn R) α)
    (h : AllQueriesSatisfy oa (· ∈ S)) (c : (ofFn R).QueryCache) :
    (simulateQ randomOracle (restrictQueries S oa h)).run' (restrictCache S c) =
      (simulateQ randomOracle oa).run' c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => rfl
  | query_bind t k ih =>
      simp only [restrictQueries_query_bind, randomOracle_query_bind_run', randomOracle.run_eq]
      have hc' : (restrictCache S c)
          ⟨t, ((allQueriesSatisfy_query_bind_iff _ _ _).mp h).1⟩ = c t := rfl
      rw [hc']
      cases hc : c t with
      | some u =>
          simp only [pure_bind]
          exact ih u (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) c
      | none =>
          simp only [bind_assoc, pure_bind]
          apply bind_congr
          intro u
          rw [← restrictCache_update]
          exact ih u (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) (c.cacheQuery t u)

/-- Extend a finite answer table with fixed arbitrary answers outside its key set. -/
@[expose] noncomputable def extendTable [∀ d, Nonempty (R d)] (S : Finset D)
    (g : (d : S) → R d.val) : ∀ d, R d := by
  classical
  exact fun d => if h : d ∈ S then g ⟨d, h⟩ else Classical.arbitrary (R d)

@[simp] theorem extendTable_subtype [∀ d, Nonempty (R d)] (S : Finset D)
    (g : (d : S) → R d.val) (d : S) : extendTable S g d.val = g d := by
  simp [extendTable, d.property]

/-- Updating a retained answer cell commutes with extension to all keys. -/
theorem extendTable_update [DecidableEq D] [∀ d, Nonempty (R d)] (S : Finset D)
    (g : (d : S) → R d.val) (t : S) (u : R t.val) :
    extendTable S (Function.update g t u) = Function.update (extendTable S g) t.val u := by
  classical
  funext q
  by_cases hq : q = t.val
  · subst q
    simp
  · by_cases hs : q ∈ S
    · have hsub : (⟨q, hs⟩ : S) ≠ t := fun h => hq (congrArg Subtype.val h)
      simp [extendTable, hs, Function.update_of_ne hq, Function.update_of_ne hsub]
    · simp [extendTable, hs, Function.update_of_ne hq]

/-- For any adaptive computation with finite nonempty answer spaces, a uniform cell-resampling
bound and an all-table bad-query implication bound its actual cached-oracle event by `n * error`.
The key domain may be infinite. A finite restriction of this fixed program preserves the exact
lazy computation, including repeated queries, and is used only inside the proof. No history
measurability or query-order assumption is imposed on the bad predicate. -/
theorem prEvent_randomOracle_le_of_bad_queries [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (ofFn R) α) (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (event : α → Prop) (bad : D → (∀ d, R d) → Prop) (error : ENNReal)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ q ∈ tableQueryLog oa g, bad q.1 g) :
    Pr{let result ← (simulateQ randomOracle oa).run' ∅}[event result] ≤ n * error := by
  classical
  let S := possibleQueryKeys oa
  have hS : AllQueriesSatisfy oa (· ∈ S) := allQueriesSatisfy_possibleQueryKeys oa
  let small := restrictQueries S oa hS
  let : ∀ d : S, Fintype (R d.val) := fun d => Fintype.ofFinite (R d.val)
  let : Nonempty ((d : S) → R d.val) := ⟨fun d => Classical.arbitrary (R d.val)⟩
  let : SampleableType ((d : S) → R d.val) := SampleableType.ofFintype _
  have hrun : (simulateQ randomOracle small).run' ∅ =
      (simulateQ randomOracle oa).run' ∅ := randomOracle_restrictQueries S oa hS ∅
  rw [← hrun]
  apply prEvent_randomOracle_le_of_bad_queries_finite small n
    (restrictQueries_queryBound S oa hS n hbound) event
    (fun t g => bad t.val (extendTable S g)) error
  · intro t g
    simp_rw [extendTable_update]
    exact hbad t.val (extendTable S g)
  · intro g hevent
    have hrestrict : (fun d : S => extendTable S g d.val) = g := by
      funext d
      exact extendTable_subtype S g d
    have heval := evalWithAnswerFn_restrictQueries S oa hS (extendTable S g)
    rw [hrestrict] at heval
    obtain ⟨q, hq, hb⟩ := htrace (extendTable S g) (heval ▸ hevent)
    have hlog := tableQueryLog_restrictQueries S oa hS (extendTable S g)
    rw [hrestrict] at hlog
    rw [← hlog] at hq
    obtain ⟨smallq, hsmallq, rfl⟩ := List.mem_map.mp hq
    exact ⟨smallq, hsmallq, hb⟩

/-- An all-table, key-dependent resampling bound and an actual bad-query trace implication
bound the event in the empty-cache random-oracle execution by its pathwise weighted budget.
The key domain may be infinite. Queries may be adaptive, repeated, and out of order, and
the bad predicate may inspect unqueried cells. Weights are probability charges. -/
theorem prEvent_randomOracle_le_of_bad_queries_weighted [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (ofFn R) α) (error : D → ENNReal) (B : ENNReal)
    (hbound : WorstCaseCostBound oa ⟨error⟩ B) (event : α → Prop)
    (bad : D → (∀ d, R d) → Prop)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t (Function.update g t u)] ≤ error t)
    (htrace : ∀ g, event (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ q ∈ tableQueryLog oa g, bad q.1 g) :
    Pr{let result ← (simulateQ randomOracle oa).run' ∅}[event result] ≤ B := by
  classical
  let S := possibleQueryKeys oa
  have hS : AllQueriesSatisfy oa (· ∈ S) := allQueriesSatisfy_possibleQueryKeys oa
  let small := restrictQueries S oa hS
  let : ∀ d : S, Fintype (R d.val) := fun d => Fintype.ofFinite (R d.val)
  let : Nonempty ((d : S) → R d.val) := ⟨fun d => Classical.arbitrary (R d.val)⟩
  let : SampleableType ((d : S) → R d.val) := SampleableType.ofFintype _
  have hrun : (simulateQ randomOracle small).run' ∅ =
      (simulateQ randomOracle oa).run' ∅ := randomOracle_restrictQueries S oa hS ∅
  rw [← hrun]
  apply prEvent_randomOracle_le_of_bad_queries_weighted_finite small (fun t => error t.val) B
    (restrictQueries_costBound S oa hS error B hbound) event
    (fun t g => bad t.val (extendTable S g))
  · intro t g
    simp_rw [extendTable_update]
    exact hbad t.val (extendTable S g)
  · intro g hevent
    have hrestrict : (fun d : S => extendTable S g d.val) = g := by
      funext d
      exact extendTable_subtype S g d
    have heval := evalWithAnswerFn_restrictQueries S oa hS (extendTable S g)
    rw [hrestrict] at heval
    obtain ⟨q, hq, hb⟩ := htrace (extendTable S g) (heval ▸ hevent)
    have hlog := tableQueryLog_restrictQueries S oa hS (extendTable S g)
    rw [hrestrict] at hlog
    rw [← hlog] at hq
    obtain ⟨smallq, hsmallq, rfl⟩ := List.mem_map.mp hq
    exact ⟨smallq, hsmallq, hb⟩

end OracleComp
