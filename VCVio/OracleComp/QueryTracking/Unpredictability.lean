/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.Birthday
public import VCVio.OracleComp.QueryTracking.ProgrammingOracle
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# ROM Unpredictability and Collision Win Bounds

Fresh query uniformity and cache preimage bounds under uniform measure semantics.

## Unpredictability

`HasUnpredictableSample samples β` packages "the probability of any specific outcome of
`samples : ProbComp α` is at most `β`". It is the abstract handle through which downstream
collision bounds ingest min-entropy of a sample distribution without re-deriving uniform-sample
arithmetic at each call site.

Instances:
* `HasUnpredictableSample.uniformSample`: `$ᵗ α` is `1/|α|`-unpredictable.
* `HasUnpredictableSample.mono`: `β`-unpredictability transports up to any `β' ≥ β`.

The TV-distance "programming collision" bound that consumes this typeclass lives downstream in
`VCVio/ProgramLogic/Relational/ProgrammingOracle.lean` (see `programming_collision_bound` and
its `qP * qH * β` repackaging), keeping the relational theorem in the `ProgramLogic` layer
while the unpredictability primitive stays here in `QueryTracking`.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal Finset

open scoped OracleSpec.PrimitiveQuery

universe u

namespace OracleComp

/-! ## Unpredictability -/

section Unpredictability

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [UniformAnswerMeasure spec] [∀ t, Fintype (spec.Range t)]

/-- **Fresh query uniformity**: querying `cachingOracle` at an uncached point
yields each value, together with the cache that records it, with probability `1/|C|`. -/
theorem prEvent_fresh_cachingOracle_query
    (t : spec.Domain) (u : spec.Range t)
    (cache₀ : QueryCache spec) (hfresh : cache₀ t = none) :
    Pr{let z ← (cachingOracle t).run cache₀}[z = (u, cache₀.cacheQuery t u)] =
      (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  classical
  rw [cachingOracle.run_none hfresh, prEvent_map]
  have hevent : ∀ u' : spec.Range t,
      ((u', cache₀.cacheQuery t u') = (u, cache₀.cacheQuery t u)) ↔ u' = u := fun u' =>
    ⟨fun h => (Prod.ext_iff.mp h).1, fun h => h ▸ rfl⟩
  simp only [hevent]
  rw [prEvent_liftM_query_eq_card_div, Finset.filter_eq' Finset.univ u]
  simp

/-- **Cache preimage bound**: if the initial cache contains at most one preimage
of a target value `v₀`, then the probability that `simulateQ cachingOracle oa`
creates a fresh cache entry equal to `v₀` is at most `n / |C|`, where `n` is the
total query bound. Each cache miss is a fresh uniform draw, so a union bound
over the at most `n` misses gives the result.

This is the reusable ROM lemma for the extractability "fresh target hit" case. -/
theorem prEvent_cache_has_value_le_of_unique_preimage {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (v₀ : spec.Range default)
    (cache₀ : QueryCache spec)
    (hunique_v₀ :
      ∀ t₀ t₁ : spec.Domain,
        ∀ v₁ : spec.Range t₀, ∀ v₂ : spec.Range t₁,
          cache₀ t₀ = some v₁ →
          cache₀ t₁ = some v₂ →
          HEq v₁ v₀ →
          HEq v₂ v₀ →
          t₀ = t₁) :
    Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ t₀ : spec.Domain,
        ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] ≤
      (n : ℝ≥0∞) * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  classical
  let C := (Fintype.card (spec.Range default) : ℝ≥0∞)
  induction oa using OracleComp.inductionOn generalizing n cache₀ with
  | pure x =>
    rw [simulateQ_pure]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_) bot_le
    change z ∈ support (pure (x, cache₀) : OracleComp _ _) at hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨t₀, v, hcache, hnone, _⟩ := h
    simp [hnone] at hcache
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hbound
    obtain ⟨hpos, hrest⟩ := hbound
    by_cases ht : ∃ v, cache₀ t = some v
    · obtain ⟨v, hv⟩ := ht
      have hrun : (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
          (simulateQ cachingOracle (mx v)).run cache₀ := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        have hcache : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
            pure (v, cache₀) := by
          simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, hv, pure_bind, StateT.run_pure]
        rw [hcache, pure_bind]
        simp [OracleQuery.cont_query]
      rw [hrun]
      calc Pr{let z ← (simulateQ cachingOracle (mx v)).run cache₀}[∃ t₀ v,
            z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀]
          ≤ ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ := ih v (n - 1) (hrest v) cache₀ hunique_v₀
        _ ≤ (n : ℝ≥0∞) * C⁻¹ := by gcongr; exact_mod_cast Nat.sub_le n 1
    · push Not at ht
      have ht_none : cache₀ t = none := Option.eq_none_iff_forall_ne_some.mpr ht
      have hrun : (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
          (liftM (query t) >>= fun u =>
            (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)) := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        have hstep : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
            (liftM (query t) >>= fun u =>
              pure (u, cache₀.cacheQuery t u) : OracleComp spec _) := by
          simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, pure_bind, ht_none]
          change (StateT.lift (PFunctor.FreeM.lift (P := spec.toPFunctor) t) cache₀ >>= _) = _
          simp only [StateT.lift, monad_norm,
            modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, StateT.run]
          rfl
        rw [hstep]; simp [monad_norm]
      rw [hrun, prEvent_bind]
      have hih : ∀ u ∈ support (liftM (query t) : OracleComp spec (spec.Range t)),
          ¬HEq u v₀ →
          Pr{let z ← (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)}[∃ t₀ v,
            z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] ≤
          ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ := by
        intro u _ heq_v₀
        have hunique_v₀' :
            ∀ t₀ t₁ : spec.Domain,
              ∀ v₁ : spec.Range t₀, ∀ v₂ : spec.Range t₁,
                (cache₀.cacheQuery t u) t₀ = some v₁ →
                (cache₀.cacheQuery t u) t₁ = some v₂ →
                HEq v₁ v₀ →
                HEq v₂ v₀ →
                t₀ = t₁ := by
          intro t₀ t₁ v₁ v₂ hcache₁ hcache₂ hheq₁ hheq₂
          by_cases heq_t₀ : t₀ = t
          · subst heq_t₀
            rw [QueryCache.cacheQuery_self] at hcache₁
            cases hcache₁
            exact (heq_v₀ hheq₁).elim
          · by_cases heq_t₁ : t₁ = t
            · subst heq_t₁
              rw [QueryCache.cacheQuery_self] at hcache₂
              cases hcache₂
              exact (heq_v₀ hheq₂).elim
            · rw [QueryCache.cacheQuery_of_ne _ _ heq_t₀] at hcache₁
              rw [QueryCache.cacheQuery_of_ne _ _ heq_t₁] at hcache₂
              exact hunique_v₀ t₀ t₁ v₁ v₂ hcache₁ hcache₂ hheq₁ hheq₂
        refine le_trans (prEvent_mono_of_support _ _ (fun z => ∃ t₀ v, z.2 t₀ = some v ∧
            (cache₀.cacheQuery t u) t₀ = none ∧ HEq v v₀)
          fun z hz ⟨t₀, v, hcache_f, hnone₀, hheq⟩ => ?_) (ih u (n - 1) (hrest u) _ hunique_v₀')
        by_cases heq_t : t₀ = t
        · exfalso
          subst heq_t
          have hle := simulateQ_cachingOracle_cache_le (mx u) (cache₀.cacheQuery t₀ u) _ hz
          have hzu : z.2 t₀ = some u := hle (QueryCache.cacheQuery_self cache₀ t₀ u)
          rw [hzu] at hcache_f; cases hcache_f
          exact heq_v₀ hheq
        · exact ⟨t₀, v, hcache_f,
            (QueryCache.cacheQuery_of_ne cache₀ u heq_t).trans hnone₀, hheq⟩
      have hhit : Pr{let u ← (liftM (query t) : OracleComp spec (spec.Range t))}[HEq u v₀] ≤
          C⁻¹ := by
        rw [prEvent_liftM_query_eq_card_div]
        have hcard : (Finset.univ.filter fun u : spec.Range t => HEq u v₀).card ≤ 1 :=
          Finset.card_le_one.mpr fun a ha b hb => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            exact eq_of_heq (ha.trans hb.symm)
        calc ((Finset.univ.filter fun u : spec.Range t => HEq u v₀).card : ℝ≥0∞) /
              Fintype.card (spec.Range t)
            ≤ 1 / Fintype.card (spec.Range t) := by gcongr; exact_mod_cast hcard
          _ ≤ C⁻¹ := by
            rw [one_div]; exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (hrange t))
      calc Pr{let u ← (liftM (query t) : OracleComp spec (spec.Range t));
              let z ← (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)}[∃ t₀ v,
                z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀]
          ≤ C⁻¹ + ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ :=
            (prEvent_bind_le_prEvent_add_of_support _ _ (fun u => HEq u v₀) _ hih).trans
              (add_le_add hhit le_rfl)
        _ = (n : ℝ≥0∞) * C⁻¹ := by
            rw [← one_add_mul, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_cancel' hpos]

/-- Special case of
`prEvent_cache_has_value_le_of_unique_preimage` when the initial cache
contains at most one preimage of `v₀` because the cache is collision-free. -/
theorem prEvent_cache_has_value_le_of_noCollision {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (v₀ : spec.Range default)
    (cache₀ : QueryCache spec)
    (hno : ¬ CacheHasCollision cache₀) :
    Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ t₀ : spec.Domain,
        ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] ≤
      (n : ℝ≥0∞) * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
  prEvent_cache_has_value_le_of_unique_preimage
    (oa := oa) (n := n) hbound hrange v₀ cache₀
    fun t₀ t₁ v₁ v₂ hcache₀ hcache₁ hheq₀ hheq₁ => not_not.1 fun hne =>
      hno ⟨t₀, t₁, v₁, v₂, hne, hcache₀, hcache₁, hheq₀.trans hheq₁.symm⟩

/-- Special case of
`prEvent_cache_has_value_le_of_unique_preimage` when the initial cache
contains no preimage of `v₀`. -/
theorem prEvent_cache_has_value_le {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (v₀ : spec.Range default)
    (cache₀ : QueryCache spec)
    (hno_v₀ : ∀ t₀ : spec.Domain, ∀ v : spec.Range t₀, cache₀ t₀ = some v → ¬HEq v v₀) :
    Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ t₀ : spec.Domain,
        ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] ≤
      (n : ℝ≥0∞) * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
  prEvent_cache_has_value_le_of_unique_preimage
    (oa := oa) (n := n) hbound hrange v₀ cache₀
    fun t₀ _ v₁ _ hcache₁ _ hheq₁ _ => (hno_v₀ t₀ v₁ hcache₁ hheq₁).elim

/-- **Finite-target cache-hit bound**: suppose every value in `targets` has at most one
preimage in the initial cache. If `oa` makes at most `n` queries, then the probability that its
cached execution creates a fresh entry whose value belongs to `targets` is at most
`|targets| * n / |Range default|`.

`targets.card` counts distinct output values, not positions or labels carrying those values.
A consumer that starts from a positional collection can deduplicate its values into a `Finset`
and then weaken the result using the corresponding cardinality bound. -/
theorem prEvent_cache_hits_targets_le_of_unique_preimage {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (targets : Finset (spec.Range default))
    (cache₀ : QueryCache spec)
    (hunique : ∀ v₀ ∈ targets,
      ∀ t₀ t₁ : spec.Domain,
        ∀ v₁ : spec.Range t₀, ∀ v₂ : spec.Range t₁,
          cache₀ t₀ = some v₁ →
          cache₀ t₁ = some v₂ →
          HEq v₁ v₀ →
          HEq v₂ v₀ →
          t₀ = t₁) :
    Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ v₀ ∈ targets, ∃ t₀ : spec.Domain,
        ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] ≤
      ((targets.card * n : ℕ) : ℝ≥0∞) *
        (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  calc
    Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ v₀ ∈ targets, ∃ t₀ : spec.Domain,
        ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀]
      ≤ ∑ v₀ ∈ targets,
          Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ t₀ : spec.Domain,
            ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] :=
        prEvent_exists_finset_le targets _ _
    _ ≤ ∑ _v₀ ∈ targets,
          (n : ℝ≥0∞) * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun v₀ hv₀ => ?_
        exact prEvent_cache_has_value_le_of_unique_preimage
          oa n hbound hrange v₀ cache₀ (hunique v₀ hv₀)
    _ = ((targets.card * n : ℕ) : ℝ≥0∞) *
          (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
        simp [Nat.cast_mul, mul_assoc]

/-- Finite-target cache-hit bound specialized to a collision-free initial cache. Collision
freeness ensures that each distinct target value has at most one initial preimage. -/
theorem prEvent_cache_hits_targets_le_of_noCollision {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (targets : Finset (spec.Range default))
    (cache₀ : QueryCache spec)
    (hno : ¬ CacheHasCollision cache₀) :
    Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ v₀ ∈ targets, ∃ t₀ : spec.Domain,
        ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] ≤
      ((targets.card * n : ℕ) : ℝ≥0∞) *
        (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
  prEvent_cache_hits_targets_le_of_unique_preimage oa n hbound hrange targets cache₀
    fun _ _ t₀ t₁ v₁ v₂ hcache₀ hcache₁ hheq₀ hheq₁ => not_not.1 fun hne =>
      hno ⟨t₀, t₁, v₁, v₂, hne, hcache₀, hcache₁, hheq₀.trans hheq₁.symm⟩

end Unpredictability

/-- Homogeneous finite-target fresh-hit bound without an artificial inhabited-domain
assumption.  If the query domain is empty, the event is impossible; otherwise this is the
homogeneous specialization of `prEvent_cache_hits_targets_le_of_noCollision`. -/
theorem prEvent_cache_hits_targets_le_of_noCollision_homogeneous
    {ι Y α : Type} [DecidableEq ι] [Finite Y]
    [UniformAnswerMeasure (ι →ₒ Y)]
    (oa : OracleComp (ι →ₒ Y) α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (targets : Finset Y)
    (cache₀ : (ι →ₒ Y).QueryCache)
    (hno : ¬ CacheHasCollision cache₀) :
    Pr{let z ← (simulateQ (ι →ₒ Y).cachingOracle oa).run cache₀}[∃ target ∈ targets,
        ∃ input : ι, ∃ value : Y, z.2 input = some value ∧ cache₀ input = none ∧
          value = target] ≤
      ((targets.card * n : ℕ) : ℝ≥0∞) * (Nat.card Y : ℝ≥0∞)⁻¹ := by
  classical
  let _ : Fintype Y := Fintype.ofFinite Y
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun z hhit => ?_) bot_le
      obtain ⟨_, _, input, _⟩ := hhit
      exact isEmptyElim input
  | inr hnonempty =>
      let _ : Inhabited ι := Classical.inhabited_of_nonempty hnonempty
      have hbase := prEvent_cache_hits_targets_le_of_noCollision
        (spec := ι →ₒ Y) oa n hbound (fun _ => le_rfl) targets cache₀ hno
      simpa only [Nat.card_eq_fintype_card, heq_eq_eq] using hbase

/-! ## `HasUnpredictableSample` -/

/-- A probabilistic computation `samples : ProbComp α` is **`β`-unpredictable** if every specific
outcome occurs with probability at most `β`. This is the standard "min-entropy at level
`log₂(1/β)`" notion, packaged as a structured proposition so that downstream collision bounds
can ingest it generically.

Equivalent to `∀ x, Pr{let y ← samples}[y = x] ≤ β`; the structure shape lets it serve as the
canonical abstract hypothesis for "values drawn from `samples` are hard to guess". -/
@[mk_iff]
structure HasUnpredictableSample {α : Type} (samples : ProbComp α) (β : ℝ≥0∞) : Prop where
  prob_le : ∀ x : α, Pr{let y ← samples}[y = x] ≤ β

namespace HasUnpredictableSample

variable {α : Type} {samples : ProbComp α} {β β' : ℝ≥0∞}

/-- Monotonicity in the bound: a `β`-unpredictable sample is also `β'`-unpredictable for any
`β' ≥ β`. -/
lemma mono (h : HasUnpredictableSample samples β) (hβ : β ≤ β') :
    HasUnpredictableSample samples β' :=
  ⟨fun x => (h.prob_le x).trans hβ⟩

/-- `$ᵗ α` is `(|α|)⁻¹`-unpredictable for any nonempty `Fintype`. -/
lemma uniformSample {α : Type} [SampleableType α] [Fintype α] :
    HasUnpredictableSample ($ᵗ α) ((Fintype.card α : ℝ≥0∞)⁻¹) :=
  ⟨fun x => (SampleableType.prEvent_uniformSample_eq_singleton x).le⟩

end HasUnpredictableSample

end OracleComp
