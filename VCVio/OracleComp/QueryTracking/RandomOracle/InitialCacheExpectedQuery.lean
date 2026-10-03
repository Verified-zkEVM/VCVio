/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQueryInfinite

/-!
# Expected charges for keys outside an initial random-oracle cache

The charge counts distinct hash keys absent from the fixed initial cache. Cached replies can
still influence execution and remain present in the completed table. A bad output is charged
only when the same trace identifies a newly sampled key satisfying the bad predicate.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleComp

variable {D α : Type} {R : D → Type}

/-- Distinct logged hash keys absent from the fixed initial cache. -/
@[expose] def newQueryKeys [DecidableEq D]
    (cache : (ofFn R).QueryCache) (log : QueryLog (ofFn R)) : Finset D :=
  (freshKeysOfLog log).filter (fun t => cache t = none)

@[simp] theorem mem_newQueryKeys [DecidableEq D]
    (cache : (ofFn R).QueryCache) (log : QueryLog (ofFn R)) (t : D) :
    t ∈ newQueryKeys cache log ↔ t ∈ freshKeysOfLog log ∧ cache t = none := by
  simp [newQueryKeys]

@[simp] theorem newQueryKeys_empty_cache [DecidableEq D]
    (log : QueryLog (ofFn R)) :
    newQueryKeys (∅ : (ofFn R).QueryCache) log = freshKeysOfLog log := by
  ext t
  simp

/-- Sum of per-key error charges for the distinct newly sampled hash keys. -/
@[expose] noncomputable def newQueryCharge [DecidableEq D]
    (cache : (ofFn R).QueryCache) (error : D → ENNReal)
    (log : QueryLog (ofFn R)) : ENNReal :=
  ∑ t ∈ newQueryKeys cache log, error t

/-- Expected new-key charge in the actual joint cached run, including returned failures. -/
@[expose] noncomputable def expectedNewQueryCharge [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (cache : (ofFn R).QueryCache) (error : D → ENNReal) : ENNReal :=
  letI : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  ∫⁻ z, newQueryCharge cache error z.1.2 ∂𝒟[randomOracleLoggedRun oa cache]

@[simp] theorem newQueryCharge_empty_cache [DecidableEq D]
    (error : D → ENNReal) (log : QueryLog (ofFn R)) :
    newQueryCharge (∅ : (ofFn R).QueryCache) error log = freshQueryCharge error log := by
  simp [newQueryCharge, freshQueryCharge]

/-- The initial-cache charge specializes to the established distinct-query charge when no
answers are cached before execution. -/
theorem expectedNewQueryCharge_empty_cache [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α) (error : D → ENNReal) :
    expectedNewQueryCharge oa (∅ : (ofFn R).QueryCache) error =
      expectedFreshQueryCharge oa error := by
  simp [expectedNewQueryCharge, expectedFreshQueryCharge]

/-- Restricting a finite program preserves precisely which logged keys were absent from the
original cache. -/
theorem newQueryKeys_extendLog [DecidableEq D] (S : Finset D)
    (cache : (ofFn R).QueryCache)
    (log : QueryLog (ofFn (fun t : S => R t.val))) :
    newQueryKeys cache (extendLog S log) =
      (newQueryKeys (restrictCache S cache) log).map
        ⟨Subtype.val, Subtype.val_injective⟩ := by
  ext t
  simp only [mem_newQueryKeys, freshKeysOfLog_extendLog, Finset.mem_map]
  constructor
  · rintro ⟨⟨smallt, hsmallt, rfl⟩, hc⟩
    exact ⟨smallt, ⟨hsmallt, by simpa [restrictCache] using hc⟩, rfl⟩
  · rintro ⟨smallt, ⟨hlog, hc⟩, rfl⟩
    exact ⟨⟨smallt, hlog, rfl⟩, by simpa [restrictCache] using hc⟩

/-- Reembedding a finite log preserves its charge for initially uncached keys. -/
theorem newQueryCharge_extendLog [DecidableEq D] (S : Finset D)
    (cache : (ofFn R).QueryCache) (error : D → ENNReal)
    (log : QueryLog (ofFn (fun t : S => R t.val))) :
    newQueryCharge cache error (extendLog S log) =
      newQueryCharge (restrictCache S cache) (fun t : S => error t.val) log := by
  simp [newQueryCharge, newQueryKeys_extendLog]

/-- Finite restriction preserves the expected charge in the actual cached run. -/
theorem expectedNewQueryCharge_restrict [DecidableEq D]
    [∀ d, SampleableType (R d)] (S : Finset D)
    (oa : OracleComp (unifSpec + ofFn R) α)
    (h : AllQueriesSatisfy oa (Sum.elim (fun _ => True) (· ∈ S)))
    (cache : (ofFn R).QueryCache) (error : D → ENNReal) :
    expectedNewQueryCharge (restrictRandomOracleQueries S oa h)
      (restrictCache S cache) (fun t : S => error t.val) =
        expectedNewQueryCharge oa cache error := by
  let : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  let : MeasurableSpace ((α × QueryLog (ofFn (fun t : S => R t.val))) ×
    (ofFn (fun t : S => R t.val)).QueryCache) := ⊤
  unfold expectedNewQueryCharge
  have hr := randomOracleLoggedRun_restrictCache S oa h cache
  rw [← hr, evalDist_map_of_discrete]
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
  apply lintegral_congr
  intro z
  exact (newQueryCharge_extendLog S cache error z.1.2).symm

/-- Completing a restricted cache agrees on the retained keys with completing the original
cache after extending the fallback table. -/
private theorem completeTable_restrictCache [∀ d, Nonempty (R d)]
    (S : Finset D) (cache : (ofFn R).QueryCache)
    (g : (t : S) → R t.val) :
    (fun t : S => completeTable cache (extendTable S g) t.val) =
      completeTable (restrictCache S cache) g := by
  funext t
  simp [completeTable, restrictCache]

/-- Completing the restricted cache before extension adds no answers beyond those already
retained by the full initial cache. -/
private theorem completeTable_extend_restrict [∀ d, Nonempty (R d)]
    (S : Finset D) (cache : (ofFn R).QueryCache)
    (g : (t : S) → R t.val) :
    completeTable cache (extendTable S (completeTable (restrictCache S cache) g)) =
      completeTable cache (extendTable S g) := by
  funext t
  by_cases ht : t ∈ S
  · cases hc : cache t <;> simp [completeTable, extendTable, ht, restrictCache, hc]
  · simp [completeTable, extendTable, ht]

private theorem completeTable_idempotent
    (cache : (ofFn R).QueryCache) (g : ∀ d, R d) :
    completeTable cache (completeTable cache g) = completeTable cache g := by
  funext t
  cases hc : cache t <;> simp [completeTable, hc]

/-! ## Finite-domain initial-cache bound -/

/-- A same-run bad witness at a newly sampled key bounds the event by the expected charge
of keys outside the fixed initial cache. Cached answers remain in `completeTable cache g`.
Private uniform draws remain interleaved in both the actual and fixed-table runs. -/
theorem prEvent_interleavedInitialCacheBad_le_expectedCharge
    [DecidableEq D] [Finite D]
    [∀ d, SampleableType (R d)] [SampleableType (∀ d, R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (cache : (ofFn R).QueryCache)
    (event : α → Prop) (bad : D → (∀ d, R d) → Prop) (error : D → ENNReal)
    (htrace : ∀ g z, z ∈ support (fixedTableLoggedRun oa g cache) →
      event z.1.1 → ∃ t ∈ newQueryKeys cache z.1.2, bad t (completeTable cache g))
    (hbad : ∀ t g, cache t = none → Pr{let u ← $ᵗ (R t)}[bad t
      (completeTable cache (Function.update g t u))] ≤ error t) :
    Pr{let z ← randomOracleLoggedRun oa cache}[event z.1.1] ≤
      expectedNewQueryCharge oa cache error := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : MeasurableSpace ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache) := ⊤
  let : MeasurableSpace (∀ d, R d) := ⊤
  let : MeasurableSpace ((∀ d, R d) ×
    ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache)) := ⊤
  let mx : ProbComp ((∀ d, R d) ×
    ((α × QueryLog (ofFn R)) × (ofFn R).QueryCache)) := do
      let g ← $ᵗ (∀ d, R d)
      let z ← fixedTableLoggedRun oa (completeTable cache g) cache
      pure (g, z)
  have hkey (t : D) :
      Pr{let p ← mx}[t ∈ newQueryKeys cache p.2.1.2 ∧ bad t (completeTable cache p.1)] ≤
      Pr{let p ← mx}[t ∈ newQueryKeys cache p.2.1.2] * error t := by
    by_cases hc : cache t = none
    · have hk := prEvent_interleavedKey_bad_le_of_initialCache
        oa cache t hc bad error (fun g => hbad t g hc)
      simpa only [mx, bind_assoc, pure_bind, mem_newQueryKeys, hc, and_true] using hk
    · have hnone (log : QueryLog (ofFn R)) : t ∉ newQueryKeys cache log := by
        simp [mem_newQueryKeys, hc]
      have hleft : Pr{let p ← mx}[t ∈ newQueryKeys cache p.2.1.2 ∧
          bad t (completeTable cache p.1)] = 0 :=
        prEvent_eq_zero_of_forall_not mx _ (fun p hp => hnone _ hp.1)
      have hright : Pr{let p ← mx}[t ∈ newQueryKeys cache p.2.1.2] = 0 :=
        prEvent_eq_zero_of_forall_not mx _ (fun p hp => hnone _ hp)
      rw [hleft, hright]
      simp
  have hunion := prEvent_bad_in_freshKeys_le_expectedCharge mx
    (fun p => newQueryKeys cache p.2.1.2)
    (fun t p => bad t (completeTable cache p.1)) error hkey
  have htarget :
      Pr{let p ← mx}[event p.2.1.1] ≤
      Pr{let p ← mx}[∃ t ∈ newQueryKeys cache p.2.1.2,
        bad t (completeTable cache p.1)] := by
    apply prEvent_mono_of_support
    intro p hp he
    obtain ⟨g, _, hp'⟩ := mem_support_bind_peel ($ᵗ (∀ d, R d))
      (fun g => do
        let z ← fixedTableLoggedRun oa (completeTable cache g) cache
        pure (g, z)) hp
    obtain ⟨z, hz, hp''⟩ := mem_support_bind_peel
      (fixedTableLoggedRun oa (completeTable cache g) cache)
      (fun z => pure (g, z)) hp'
    have hp_eq : p = (g, z) := eq_of_mem_support_pure (g, z) hp''
    subst p
    simpa only [completeTable_idempotent] using
      htrace (completeTable cache g) z hz he
  have heager : 𝒟[randomOracleLoggedRun oa cache] = 𝒟[Prod.snd <$> mx] := by
    rw [evalDist_randomOracleLoggedRun_eq_fixedTable_finite oa cache]
    simp only [mx, map_bind, map_pure, bind_pure]
  have hevent :
      Pr{let z ← randomOracleLoggedRun oa cache}[event z.1.1] =
      Pr{let p ← mx}[event p.2.1.1] := by
    rw [prEvent_congr_of_evalDist_eq _ _ heager]
    rw [prEvent_map]
  have hcharge :
      (∫⁻ p, ∑ t ∈ newQueryKeys cache p.2.1.2, error t ∂𝒟[mx]) =
      expectedNewQueryCharge oa cache error := by
    unfold expectedNewQueryCharge newQueryCharge
    rw [heager, evalDist_map_of_discrete]
    rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
  rw [hevent, ← hcharge]
  exact htarget.trans hunion

/-! ## Arbitrary-domain initial-cache bound -/

/-- For any hash-input domain, the bad-output probability in the actual cached run is bounded
by the expected error charge of distinct queried keys absent from the fixed initial cache.
Every supported fixed-table trace must identify a newly sampled bad key in that same run;
the own-cell bound applies to the cache-completed table. In particular, a bad answer already
present in the initial cache cannot by itself discharge the trace hypothesis. -/
theorem prEvent_randomOracle_le_expectedNewQueryCharge [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (cache : (ofFn R).QueryCache)
    (event : α → Prop) (bad : D → (∀ d, R d) → Prop) (error : D → ENNReal)
    (htrace : ∀ g z, z ∈ support (fixedTableLoggedRun oa g cache) →
      event z.1.1 → ∃ t ∈ newQueryKeys cache z.1.2, bad t (completeTable cache g))
    (hbad : ∀ t g, cache t = none → Pr{let u ← $ᵗ (R t)}[bad t
      (completeTable cache (Function.update g t u))] ≤ error t) :
    Pr{let z ← randomOracleLoggedRun oa cache}[event z.1.1] ≤
      expectedNewQueryCharge oa cache error := by
  classical
  let S := possibleRandomOracleKeys oa
  let hS := allQueriesSatisfy_possibleRandomOracleKeys oa
  let small := restrictRandomOracleQueries S oa hS
  let smallCache := restrictCache S cache
  have hrun := randomOracleLoggedRun_restrictCache S oa hS cache
  rw [← hrun, prEvent_map]
  rw [← expectedNewQueryCharge_restrict S oa hS cache error]
  let : ∀ t : S, Fintype (R t.val) := fun t => Fintype.ofFinite (R t.val)
  let : SampleableType (∀ t : S, R t.val) := SampleableType.piOfFintype _
  let smallBad : S → ((t : S) → R t.val) → Prop :=
    fun t g => bad t.val (completeTable cache (extendTable S g))
  apply prEvent_interleavedInitialCacheBad_le_expectedCharge
    small smallCache event smallBad (fun t : S => error t.val)
  · intro g z hz hevent
    let full := extendTable S g
    have hext : (fun t : S => full t.val) = g := by
      funext t
      exact extendTable_subtype S g t
    have hfixed := fixedTableLoggedRun_restrictCache S full oa hS cache
    rw [hext] at hfixed
    have hsource : extendLoggedResult S cache z ∈
        support (fixedTableLoggedRun oa full cache) := by
      rw [← hfixed, support_map]
      exact Set.mem_image_of_mem _ hz
    obtain ⟨t, ht, hb⟩ := htrace full (extendLoggedResult S cache z) hsource hevent
    change t ∈ newQueryKeys cache (extendLog S z.1.2) at ht
    rw [newQueryKeys_extendLog, Finset.mem_map] at ht
    obtain ⟨smallt, hsmallt, heq⟩ := ht
    subst t
    refine ⟨smallt, hsmallt, ?_⟩
    change bad smallt.val
      (completeTable cache (extendTable S (completeTable smallCache g)))
    rw [completeTable_extend_restrict]
    exact hb
  · intro t g hc
    change Pr{let u ← $ᵗ (R t.val)}[bad t.val (completeTable cache
        (extendTable S (completeTable smallCache (Function.update g t u))))] ≤ error t.val
    change Pr{let u ← $ᵗ (R t.val)}[bad t.val (completeTable cache
        (extendTable S (completeTable (restrictCache S cache)
          (Function.update g t u))))] ≤ error t.val
    simp_rw [completeTable_extend_restrict, extendTable_update]
    exact hbad t.val (extendTable S g) (by simpa [smallCache, restrictCache] using hc)

/-- With an empty initial cache, the initial-cache theorem has the established
distinct-query trace and own-cell hypotheses. -/
theorem prEvent_randomOracle_le_expectedFreshQueryCharge_via_initialCache [DecidableEq D]
    [∀ d, SampleableType (R d)]
    (oa : OracleComp (unifSpec + ofFn R) α)
    (event : α → Prop) (bad : D → (∀ d, R d) → Prop) (error : D → ENNReal)
    (htrace : ∀ g z, z ∈ support (fixedTableLoggedRun oa g ∅) →
      event z.1.1 → ∃ t ∈ freshKeysOfLog z.1.2, bad t g)
    (hbad : ∀ t g, Pr{let u ← $ᵗ (R t)}[bad t
      (Function.update g t u)] ≤ error t) :
    Pr{let z ← randomOracleLoggedRun oa}[event z.1.1] ≤
      expectedFreshQueryCharge oa error := by
  have htrace' : ∀ g z, z ∈ support (fixedTableLoggedRun oa g ∅) →
      event z.1.1 → ∃ t ∈ newQueryKeys (∅ : (ofFn R).QueryCache) z.1.2,
        bad t (completeTable ∅ g) := by
    intro g z hz he
    obtain ⟨t, ht, hb⟩ := htrace g z hz he
    exact ⟨t, by simpa using ht, by simpa only [completeTable_empty] using hb⟩
  have hbad' : ∀ t g, (∅ : (ofFn R).QueryCache) t = none →
      Pr{let u ← $ᵗ (R t)}[bad t (completeTable ∅ (Function.update g t u))] ≤
        error t := by
    intro t g _
    simpa only [completeTable_empty] using hbad t g
  simpa only [expectedNewQueryCharge_empty_cache] using
    prEvent_randomOracle_le_expectedNewQueryCharge oa ∅ event bad error htrace' hbad'

end OracleComp
