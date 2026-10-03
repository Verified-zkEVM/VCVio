/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun

/-!
# Finite random-oracle support with interleaved private sampling

Every finite computation with finite oracle responses can query only finitely many hash keys,
even when the hash-input domain is infinite. Restricting to these keys preserves the complete
execution: returned value, ordered hash-query log, and final cache. Private uniform queries are
left unchanged and remain fresh at each occurrence.

The restriction laws are equalities of computations, so they preserve joint distributions and
phase handoff without choosing a uniform answer table on an infinite domain. The distinct-query
charge is unchanged by reembedding the finite log. An optional failure is part of the returned
value, and therefore retains its log, cache, and charge.
-/

public section
open OracleComp OracleSpec MeasureTheory
namespace OracleComp
variable {D α : Type} {R : D → Type}

local instance [∀ d, Finite (R d)] : ∀ q, Finite ((unifSpec + ofFn R) q)
  | .inl n => inferInstanceAs (Finite (Fin (n + 1)))
  | .inr t => inferInstanceAs (Finite (R t))

/-- A finite set containing every possible hash key on every branch of an interleaved program. -/
@[expose] noncomputable def possibleRandomOracleKeys [DecidableEq D] [∀ d, Finite (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α) : Finset D := by
  classical
  let all := possibleQueryKeys oa
  exact all.biUnion fun q => Sum.elim (fun _ => ∅) (fun t => {t}) q

@[simp] theorem mem_possibleRandomOracleKeys [DecidableEq D] [∀ d, Finite (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α) (t : D) :
    t ∈ possibleRandomOracleKeys oa ↔ Sum.inr t ∈ possibleQueryKeys oa := by
  classical
  simp only [possibleRandomOracleKeys, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, ht⟩
    cases q with
    | inl n => simp at ht
    | inr d =>
        have htd : t = d := by simpa using ht
        simpa [htd] using hq
  · intro h
    exact ⟨.inr t, h, by simp⟩

private theorem allQueriesSatisfy_mono' {ι : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec α) (P Q : ι → Prop)
    (h : AllQueriesSatisfy oa P) (himp : ∀ t, P t → Q t) :
    AllQueriesSatisfy oa Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
      obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨himp t ht, fun u => ih u (hk u)⟩

theorem allQueriesSatisfy_possibleRandomOracleKeys [DecidableEq D]
    [∀ d, Finite (R d)] (oa : OracleComp (unifSpec + ofFn R) α) :
    AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ∈ possibleRandomOracleKeys oa)) := by
  apply allQueriesSatisfy_mono' oa _ _ (allQueriesSatisfy_possibleQueryKeys oa)
  intro q hq
  cases q with
  | inl n => trivial
  | inr t => exact (mem_possibleRandomOracleKeys oa t).mpr hq

/-- Restrict hash keys to a finite set containing every possible query;
keep private samples unchanged. -/
@[expose] noncomputable def restrictRandomOracleQueries (S : Finset D) :
    (oa : OracleComp (unifSpec + ofFn R) α) →
      AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ∈ S)) →
      OracleComp (unifSpec + ofFn (fun t : S => R t.val)) α
  | .pure a, _ => pure a
  | .queryBind (.inl n) k, h =>
      liftM ((unifSpec + ofFn (fun t : S => R t.val)).query (.inl n)) >>=
        fun u => restrictRandomOracleQueries S (k u)
          (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u)
  | .queryBind (.inr t) k, h =>
      liftM ((unifSpec + ofFn (fun t : S => R t.val)).query
        (.inr ⟨t, ((allQueriesSatisfy_query_bind_iff _ _ _).mp h).1⟩)) >>=
        fun u => restrictRandomOracleQueries S (k u)
          (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u)

@[simp] theorem restrictRandomOracleQueries_pure (S : Finset D) (a : α) (h) :
    restrictRandomOracleQueries S (pure a : OracleComp (unifSpec + ofFn R) α) h = pure a := rfl

@[simp] theorem restrictRandomOracleQueries_uniformQuery_bind (S : Finset D) (n : ℕ)
    (k : Fin (n + 1) → OracleComp (unifSpec + ofFn R) α) (h) :
    restrictRandomOracleQueries S (liftM ((unifSpec + ofFn R).query (.inl n)) >>= k) h =
      liftM ((unifSpec + ofFn (fun t : S => R t.val)).query (.inl n)) >>=
        fun u => restrictRandomOracleQueries S (k u)
          (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) := rfl

@[simp] theorem restrictRandomOracleQueries_hashQuery_bind (S : Finset D) (t : D)
    (k : R t → OracleComp (unifSpec + ofFn R) α) (h) :
    restrictRandomOracleQueries S (liftM ((unifSpec + ofFn R).query (.inr t)) >>= k) h =
      liftM ((unifSpec + ofFn (fun t : S => R t.val)).query
        (.inr ⟨t, ((allQueriesSatisfy_query_bind_iff _ _ _).mp h).1⟩)) >>=
        fun u => restrictRandomOracleQueries S (k u)
          (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 u) := rfl

/-- Reembed a restricted cache, preserving the supplied cache outside the finite key set. -/
@[expose] noncomputable def extendCache [DecidableEq D] (S : Finset D)
    (outside : (ofFn R).QueryCache) (inside : (ofFn (fun t : S => R t.val)).QueryCache) :
    (ofFn R).QueryCache :=
  QueryCache.ofFn fun t => if h : t ∈ S then inside ⟨t, h⟩ else outside t

@[simp] theorem extendCache_subtype [DecidableEq D] (S : Finset D)
    (outside : (ofFn R).QueryCache) (inside : (ofFn (fun t : S => R t.val)).QueryCache)
    (t : S) : extendCache S outside inside t.val = inside t := by
  simp [extendCache, t.property]

@[simp] theorem extendCache_restrictCache [DecidableEq D] (S : Finset D)
    (cache : (ofFn R).QueryCache) : extendCache S cache (restrictCache S cache) = cache := by
  ext t
  simp [extendCache, restrictCache]

theorem extendCache_update [DecidableEq D] (S : Finset D)
    (outside : (ofFn R).QueryCache) (inside : (ofFn (fun t : S => R t.val)).QueryCache)
    (t : S) (u : R t.val) :
    extendCache S outside (inside.cacheQuery t u) =
      (extendCache S outside inside).cacheQuery t.val u := by
  apply QueryCache.ext
  intro q
  by_cases hq : q = t.val
  · subst q
    simp
  · by_cases hs : q ∈ S
    · have hqt : (⟨q, hs⟩ : S) ≠ t := fun h => hq (congrArg Subtype.val h)
      simp [extendCache, hs, QueryCache.cacheQuery_of_ne _ _ hq,
        QueryCache.cacheQuery_of_ne _ _ hqt]
    · simp [extendCache, hs, QueryCache.cacheQuery_of_ne _ _ hq]


/-- Reembed the ordered hash-query log without changing its answers or multiplicities. -/
@[expose] noncomputable def extendLog (S : Finset D)
    (log : QueryLog (ofFn (fun t : S => R t.val))) : QueryLog (ofFn R) :=
  log.map fun q => ⟨q.1.val, q.2⟩

/-- Reembed the returned value, ordered log, and final cache together. -/
@[expose] noncomputable def extendLoggedResult [DecidableEq D] (S : Finset D)
    (outside : (ofFn R).QueryCache)
    (z : (α × QueryLog (ofFn (fun t : S => R t.val))) ×
      (ofFn (fun t : S => R t.val)).QueryCache) :
    (α × QueryLog (ofFn R)) × (ofFn R).QueryCache :=
  ((z.1.1, extendLog S z.1.2), extendCache S outside z.2)

/-- Restriction preserves the entire cached execution, including an arbitrary initial cache. -/
theorem randomOracleLoggedRun_restrict [DecidableEq D]
    [∀ d, SampleableType (R d)] (S : Finset D)
    (oa : OracleComp (unifSpec + ofFn R) α)
    (h : AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ∈ S)))
    (outside : (ofFn R).QueryCache)
    (inside : (ofFn (fun t : S => R t.val)).QueryCache) :
    extendLoggedResult S outside <$> randomOracleLoggedRun
      (restrictRandomOracleQueries S oa h) inside =
        randomOracleLoggedRun oa (extendCache S outside inside) := by
  induction oa using OracleComp.inductionOn generalizing inside with
  | pure a => simp [randomOracleLoggedRun,
      extendLoggedResult, extendLog]
  | query_bind q k ih =>
    have hs := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
    cases q with
    | inl n =>
      rw [restrictRandomOracleQueries_uniformQuery_bind, randomOracleLoggedRun_bind,
        randomOracleLoggedRun_bind, randomOracleLoggedRun_uniformQuery,
        randomOracleLoggedRun_uniformQuery]
      simp only [bind_map_left, map_bind, Functor.map_map, List.nil_append, Prod.mk.eta]
      apply bind_congr
      intro u
      change extendLoggedResult S outside <$> _ = id <$> _
      rw [id_map]
      exact ih u (hs.2 u) inside
    | inr t =>
      simp only [restrictRandomOracleQueries_hashQuery_bind, randomOracleLoggedRun_bind,
        randomOracleLoggedRun_hashQuery, randomOracle.run_eq]
      have he : extendCache S outside inside t = inside ⟨t, hs.1⟩ :=
        extendCache_subtype S outside inside ⟨t, hs.1⟩
      rw [he]
      cases hc : inside ⟨t, hs.1⟩ with
      | none =>
        simp only [bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
        apply bind_congr
        intro u
        have step := congrArg
          (fun m => (fun z : ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) =>
            ((z.1.1, (⟨t, u⟩ : (d : D) × R d) :: z.1.2), z.2)) <$> m)
          (ih u (hs.2 u) (inside.cacheQuery ⟨t, hs.1⟩ u))
        simpa only [Functor.map_map, extendLoggedResult, extendLog, List.map_append,
          List.map_cons, List.map_nil, List.singleton_append, extendCache_update] using step
      | some u =>
        simp only [map_pure, pure_bind, Functor.map_map]
        have step := congrArg
          (fun m => (fun z : ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) =>
            ((z.1.1, (⟨t, u⟩ : (d : D) × R d) :: z.1.2), z.2)) <$> m)
          (ih u (hs.2 u) inside)
        simpa only [Functor.map_map, extendLoggedResult, extendLog, List.map_append,
          List.map_cons, List.map_nil, List.singleton_append, extendCache_update] using step


private theorem fixedHashRun [DecidableEq D] (g : ∀ d, R d)
    (cache : (ofFn R).QueryCache) (t : D) :
    ((((QueryImpl.ofFn g).liftTarget ProbComp).withCaching) t).run cache =
      match cache t with
      | some u => pure (u, cache)
      | none => pure (g t, cache.cacheQuery t (g t)) := by
  cases hc : cache t with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc]
      change (fun u => (u, cache.cacheQuery t u)) <$> pure (g t) = _
      simp
  | some u => exact QueryImpl.withCaching_run_some _ hc

/-- Restriction also preserves the entire execution against a fixed answer assignment. -/
theorem fixedTableLoggedRun_restrict [DecidableEq D]
    (S : Finset D) (g : ∀ d, R d)
    (oa : OracleComp (unifSpec + ofFn R) α)
    (h : AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ∈ S)))
    (outside : (ofFn R).QueryCache)
    (inside : (ofFn (fun t : S => R t.val)).QueryCache) :
    extendLoggedResult S outside <$> fixedTableLoggedRun
      (restrictRandomOracleQueries S oa h) (fun t => g t.val) inside =
        fixedTableLoggedRun oa g (extendCache S outside inside) := by
  induction oa using OracleComp.inductionOn generalizing inside with
  | pure a => simp [fixedTableLoggedRun,
      extendLoggedResult, extendLog]
  | query_bind q k ih =>
    have hs := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
    cases q with
    | inl n =>
      rw [restrictRandomOracleQueries_uniformQuery_bind, fixedTableLoggedRun_bind,
        fixedTableLoggedRun_bind, fixedTableLoggedRun_uniformQuery,
        fixedTableLoggedRun_uniformQuery]
      simp only [bind_map_left, map_bind, Functor.map_map, List.nil_append, Prod.mk.eta]
      apply bind_congr
      intro u
      change extendLoggedResult S outside <$> _ = id <$> _
      rw [id_map]
      exact ih u (hs.2 u) inside
    | inr t =>
      simp only [restrictRandomOracleQueries_hashQuery_bind, fixedTableLoggedRun_bind,
        fixedTableLoggedRun_hashQuery, fixedHashRun]
      have he : extendCache S outside inside t = inside ⟨t, hs.1⟩ :=
        extendCache_subtype S outside inside ⟨t, hs.1⟩
      rw [he]
      cases hc : inside ⟨t, hs.1⟩ with
      | none =>
        simp only [map_pure, pure_bind, Functor.map_map]
        let u := g t
        have step := congrArg
          (fun m => (fun z : ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) =>
            ((z.1.1, (⟨t, u⟩ : (d : D) × R d) :: z.1.2), z.2)) <$> m)
          (ih u (hs.2 u) (inside.cacheQuery ⟨t, hs.1⟩ u))
        simpa only [Functor.map_map, extendLoggedResult, extendLog, List.map_append,
          List.map_cons, List.map_nil, List.singleton_append, extendCache_update] using step
      | some u =>
        simp only [map_pure, pure_bind, Functor.map_map]
        have step := congrArg
          (fun m => (fun z : ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) =>
            ((z.1.1, (⟨t, u⟩ : (d : D) × R d) :: z.1.2), z.2)) <$> m)
          (ih u (hs.2 u) inside)
        simpa only [Functor.map_map, extendLoggedResult, extendLog, List.map_append,
          List.map_cons, List.map_nil, List.singleton_append, extendCache_update] using step



@[simp] theorem freshKeysOfLog_extendLog [DecidableEq D] (S : Finset D)
    (log : QueryLog (ofFn (fun t : S => R t.val))) :
    freshKeysOfLog (extendLog S log) =
      (freshKeysOfLog log).map ⟨Subtype.val, Subtype.val_injective⟩ := by
  ext t
  simp [freshKeysOfLog, extendLog, List.map_map, Finset.map_eq_image,
    List.mem_map, Function.comp_def]

@[simp] theorem freshQueryCharge_extendLog [DecidableEq D] (S : Finset D)
    (error : D → ENNReal) (log : QueryLog (ofFn (fun t : S => R t.val))) :
    freshQueryCharge error (extendLog S log) =
      freshQueryCharge (fun t : S => error t.val) log := by
  simp [freshQueryCharge]

/-- The finite restriction preserves the actual initial cache, returned output, ordered log,
and final cache. Private samples remain interleaved and are never cached. -/
theorem randomOracleLoggedRun_restrictCache [DecidableEq D]
    [∀ d, SampleableType (R d)] (S : Finset D)
    (oa : OracleComp (unifSpec + ofFn R) α)
    (h : AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ∈ S)))
    (cache : (ofFn R).QueryCache) :
    extendLoggedResult S cache <$> randomOracleLoggedRun
      (restrictRandomOracleQueries S oa h) (restrictCache S cache) =
        randomOracleLoggedRun oa cache := by
  simpa only [extendCache_restrictCache] using
    randomOracleLoggedRun_restrict S oa h cache (restrictCache S cache)

/-- The same finite restriction preserves the joint fixed-table experiment. -/
theorem fixedTableLoggedRun_restrictCache [DecidableEq D]
    (S : Finset D) (g : ∀ d, R d)
    (oa : OracleComp (unifSpec + ofFn R) α)
    (h : AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ∈ S)))
    (cache : (ofFn R).QueryCache) :
    extendLoggedResult S cache <$> fixedTableLoggedRun
      (restrictRandomOracleQueries S oa h) (fun t => g t.val) (restrictCache S cache) =
        fixedTableLoggedRun oa g cache := by
  simpa only [extendCache_restrictCache] using
    fixedTableLoggedRun_restrict S g oa h cache (restrictCache S cache)

@[simp] theorem restrictCache_empty (S : Finset D) :
    restrictCache S (∅ : (ofFn R).QueryCache) = ∅ := by
  ext t
  simp [restrictCache]

/-- Restricting to possible hash keys preserves the expected distinct-query charge of the
actual empty-cache run, including optional failures returned as values. -/
theorem expectedFreshQueryCharge_restrict [DecidableEq D]
    [∀ d, SampleableType (R d)] (S : Finset D)
    (oa : OracleComp (unifSpec + ofFn R) α)
    (h : AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ∈ S)))
    (error : D → ENNReal) :
    expectedFreshQueryCharge (restrictRandomOracleQueries S oa h)
      (fun t : S => error t.val) = expectedFreshQueryCharge oa error := by
  let : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  let : MeasurableSpace ((α × QueryLog (ofFn (fun t : S => R t.val))) ×
    (ofFn (fun t : S => R t.val)).QueryCache) := ⊤
  unfold expectedFreshQueryCharge
  have hr := randomOracleLoggedRun_restrictCache S oa h ∅
  simp only [restrictCache_empty] at hr
  rw [← hr, evalDist_map_of_discrete]
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
  apply lintegral_congr
  intro z
  exact (freshQueryCharge_extendLog S error z.1.2).symm

end OracleComp
