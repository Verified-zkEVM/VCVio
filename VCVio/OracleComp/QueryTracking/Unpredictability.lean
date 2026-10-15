/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters, Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.Birthday
public import VCVio.OracleComp.QueryTracking.ProgrammingOracle
public import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.ProgramLogic.Unary.SimulateQSpecs
import VCVio.ProgramLogic.Unary.WP.Upper

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

open OracleSpec OracleComp ENNReal Finset OrderDual Std.WP

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

/-- The fresh-target potential: the target sits at a key the initial cache left empty, plus `k`
remaining queries, each hitting it with probability at most `1 / C`. -/
private noncomputable def hitPotential [Inhabited ι] (C : ℝ≥0∞) (cache₀ : QueryCache spec)
    (v₀ : spec.Range default) (k : ℕ) (cache : QueryCache spec) : ℝ≥0∞ᵒᵈ :=
  toDual (propInd (∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
    cache t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀) + k * C⁻¹)

omit [DecidableEq ι] [UniformAnswerMeasure spec] in
/-- At most one answer of a query is the target, so the fresh answer hits it with probability
at most `1 / |Range t|`. -/
private theorem sum_propInd_heq_le_one [Inhabited ι] (t : spec.Domain)
    (v₀ : spec.Range default) :
    ∑ u : spec.Range t, propInd (HEq u v₀) ≤ 1 := by
  classical
  simp only [propInd_eq_ite, Finset.sum_boole]
  have hcard : (Finset.univ.filter fun u : spec.Range t => HEq u v₀).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact eq_of_heq (ha.trans hb.symm)
  exact_mod_cast hcard

open scoped OracleComp.Upper in
private theorem cachingOracle_hitPotential_step [Inhabited ι]
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (cache₀ : QueryCache spec) (v₀ : spec.Range default) (t : spec.Domain) (k : ℕ) :
    ⦃ hitPotential (Fintype.card (spec.Range default)) cache₀ v₀ (k + 1) ⦄
      (cachingOracle t : StateT (QueryCache spec) (OracleComp spec) _)
      ⦃ fun _ => hitPotential (Fintype.card (spec.Range default)) cache₀ v₀ k ⦄ := by
  classical
  set C : ℝ≥0∞ := (Fintype.card (spec.Range default) : ℝ≥0∞)
  rw [cachingOracle.apply_eq]
  vcgen [OracleComp.Upper.Spec.monadLift_query_avg]
  · -- cache hit: the cache is unchanged and the unused budget is dropped
    simp only [OracleComp.Upper.rel_iff, hitPotential, ofDual_toDual]
    gcongr
    exact_mod_cast Nat.le_succ k
  · -- cache miss: the fresh answer hits the target with probability at most `1 / C`
    rename_i s hs
    simp only [OracleComp.Upper.rel_iff, hitPotential, ofDual_toDual, binderNameHint,
      StateT.wp_apply_eq, StateT.run_modifyGet, ExactWPMonad.wp_pure]
    have := UniformAnswerMeasure.nonempty_range (spec := spec) t
    set c : ℝ≥0∞ := (Fintype.card (spec.Range t) : ℝ≥0∞)
    have hc0 : c ≠ 0 := by simp [c]
    have hct : c ≠ ⊤ := by simp [c]
    -- a hit after the fresh answer is a hit before it, or the fresh answer itself
    have hpt : ∀ u : spec.Range t,
        propInd (∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
            (s.cacheQuery t u) t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀) ≤
          propInd (∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
            s t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀) + propInd (HEq u v₀) := by
      intro u
      by_cases hE : ∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
          (s.cacheQuery t u) t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀
      · obtain ⟨t₀, v, hv, h0, hheq⟩ := hE
        rw [propInd_eq_one_iff.mpr ⟨t₀, v, hv, h0, hheq⟩]
        by_cases ht₀ : t₀ = t
        · subst ht₀
          rw [QueryCache.cacheQuery_self, Option.some.injEq] at hv
          subst hv
          rw [propInd_eq_one_iff.mpr hheq]
          exact le_add_self
        · rw [QueryCache.cacheQuery_of_ne s u ht₀] at hv
          rw [propInd_eq_one_iff.mpr ⟨t₀, v, hv, h0, hheq⟩]
          exact le_self_add
      · rw [propInd_eq_zero_iff.mpr hE]
        exact zero_le
    calc ∑ u, c⁻¹ * (propInd (∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
            (s.cacheQuery t u) t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀) + k * C⁻¹)
        ≤ ∑ u, c⁻¹ * (propInd (∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
            s t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀) + propInd (HEq u v₀) + k * C⁻¹) := by
          gcongr with u
          exact hpt u
      _ = propInd (∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
            s t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀) +
            c⁻¹ * ∑ u, propInd (HEq u v₀) + k * C⁻¹ := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, ← mul_assoc, ← Finset.mul_sum]
          rw [show (Fintype.card (spec.Range t) : ℝ≥0∞) = c from rfl,
            ENNReal.mul_inv_cancel hc0 hct]
          simp only [one_mul]
          rfl
      _ ≤ propInd (∃ t₀ : spec.Domain, ∃ v : spec.Range t₀,
            s t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀) + C⁻¹ + k * C⁻¹ := by
          gcongr
          calc c⁻¹ * ∑ u, propInd (HEq u v₀) ≤ c⁻¹ * 1 := by
                gcongr
                exact sum_propInd_heq_le_one t v₀
            _ ≤ C⁻¹ := by
                rw [mul_one]
                gcongr
                simp only [C, c]
                exact_mod_cast hrange t
      _ = _ := by
          rw [add_assoc, Nat.cast_succ, add_mul, one_mul, add_comm C⁻¹]

open scoped OracleComp.Upper in
/-- **Cache preimage bound**: the probability that `simulateQ cachingOracle oa` creates a fresh
cache entry equal to a target `v₀` is at most `n / |C|`, where `n` is the total query bound.
Each cache miss is a fresh uniform draw that hits the target with probability at most `1 / |C|`,
whatever the cache holds, so the bound is the ranked potential `hitPotential` spent one unit per
query; the hypothesis `_hunique_v₀` on the initial cache is not used.

This is the reusable ROM lemma for the extractability "fresh target hit" case. -/
theorem prEvent_cache_has_value_le_of_unique_preimage {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (v₀ : spec.Range default)
    (cache₀ : QueryCache spec)
    (_hunique_v₀ :
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
  set C : ℝ≥0∞ := (Fintype.card (spec.Range default) : ℝ≥0∞)
  have h := (OracleComp.ProgramLogic.simulateQ_triple_ranked cachingOracle
    (hitPotential C cache₀ v₀) (cachingOracle_hitPotential_step hrange cache₀ v₀)
    (fun k s => by
      simp only [OracleComp.Upper.rel_iff, hitPotential, ofDual_toDual, Nat.cast_zero, zero_mul,
        add_zero]
      exact le_self_add) oa n hbound).le_wp cache₀
  rw [OracleComp.Upper.rel_iff, StateT.wp_apply_eq, OracleComp.Upper.ofDual_wp] at h
  calc Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ t₀ : spec.Domain,
        ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀]
      ≤ _ := ExpectationWP.wp_mono _ fun z => le_self_add
    _ ≤ _ := h
    _ = n * C⁻¹ := by
        simp only [hitPotential, ofDual_toDual]
        rw [propInd_eq_zero_iff.mpr fun ⟨_, _, hsome, hnone, _⟩ => by simp [hnone] at hsome,
          zero_add]

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
