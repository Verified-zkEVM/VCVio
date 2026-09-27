/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.GenerateSeed

/-!
# Eager Random Oracle

The eager random oracle serves answers from a pre-generated `QuerySeed`, consuming values
sequentially and falling back to fresh uniform sampling when exhausted. Different calls to
the same oracle consume different seed values. State: `QuerySeed`.

This gives INDEPENDENT samples (each call consumes a different seed value), unlike
`randomOracle` which gives CONSISTENT samples (same input → same output via caching).
When averaged over a uniformly sampled seed, the eager version has the output measure of the
fresh independent-query semantics.
-/

@[expose] public section

open OracleComp OracleSpec

universe u v w

open scoped OracleSpec.PrimitiveQuery

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}

/-- The eager random oracle: serves answers from a pre-generated `QuerySeed`, consuming
seed values sequentially and falling back to fresh uniform sampling when exhausted.

Concretely, on query `t`:
- If `seed t` is non-empty, return the head and advance to the tail.
- If `seed t` is empty, sample `$ᵗ spec.Range t` uniformly and leave the seed unchanged.

**Important**: This gives INDEPENDENT samples (each call consumes a different seed value),
unlike `randomOracle` which gives CONSISTENT samples (same input → same output via caching).
The two models agree when no oracle index is queried more than once.

This is definitionally equal to `uniformSampleImpl.withPregen` (from `SeededOracle.lean`). -/
@[inline, reducible] def eagerRandomOracle {ι} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] :
    QueryImpl spec (StateT (QuerySeed spec) ProbComp) :=
  fun t => StateT.mk fun seed =>
    match seed t with
    | u :: us => pure (u, seed.update t us)
    | [] => (·, seed) <$> ($ᵗ spec.Range t)

namespace eagerRandomOracle

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

lemma apply_eq (t : spec₀.Domain) :
    (eagerRandomOracle (spec := spec₀)) t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, seed.update t us)
      | [] => (·, seed) <$> ($ᵗ spec₀.Range t) := rfl

/-- A seeded eager query consumes the head value through `QuerySeed.update`. -/
lemma run_cons {t : spec₀.Domain} {seed : QuerySeed spec₀} {u : spec₀.Range t}
    {us : List (spec₀.Range t)} (h : seed t = u :: us) :
    (eagerRandomOracle t).run seed = pure (u, seed.update t us) := by
  rw [apply_eq, StateT.run_mk, h]

/-- An eager query with no seed value samples uniformly and preserves the seed. -/
lemma run_nil {t : spec₀.Domain} {seed : QuerySeed spec₀} (h : seed t = []) :
    (eagerRandomOracle t).run seed = (·, seed) <$> ($ᵗ spec₀.Range t) := by
  rw [apply_eq, StateT.run_mk, h]

variable [∀ t, MeasurableSpace (spec₀.Range t)] [∀ t, DiscreteMeasurableSpace (spec₀.Range t)]
  [OracleSpec.IsUniformMeasureSpec spec₀]

/-- With an empty seed, the eager random oracle reduces to uniform sampling: every query falls
through to a fresh uniform answer with no state change. -/
theorem evalDist_simulateQ_run'_empty {α : Type} [MeasurableSpace α] (oa : OracleComp spec₀ α) :
    𝒟[(simulateQ (eagerRandomOracle (spec := spec₀)) oa).run' ∅] = 𝒟[oa] := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind t f ih =>
    rw [simulateQ_bind,
      show simulateQ eagerRandomOracle (liftM (query t)) = eagerRandomOracle t by
        rw [simulateQ_query]; simp [OracleQuery.cont_query, OracleQuery.input_query, id_map]]
    have hsimp : (eagerRandomOracle t >>= fun u =>
        simulateQ eagerRandomOracle (f u)).run' (∅ : QuerySeed spec₀) =
        $ᵗ spec₀.Range t >>= fun u => (simulateQ eagerRandomOracle (f u)).run' ∅ := by
      change Prod.fst <$> ((eagerRandomOracle t).run ∅ >>= fun p =>
          (simulateQ eagerRandomOracle (f p.1)).run p.2) =
        $ᵗ spec₀.Range t >>= fun u => Prod.fst <$> (simulateQ eagerRandomOracle (f u)).run ∅
      simp [eagerRandomOracle]
    rw [hsimp]
    exact evalDist_bind_eq_query_bind_of_uniform t _ SampleableType.evalDist_uniformSample _ f ih

end eagerRandomOracle

/-- Helper: the `run'` of the eager oracle bind reduces to uniform sampling
when `seed t = []`. -/
private lemma eagerRandomOracle_run'_nil {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]
    {α : Type} (t : spec₀.Domain) (f : spec₀.Range t → OracleComp spec₀ α)
    (seed : QuerySeed spec₀) (ht : seed t = []) :
    (eagerRandomOracle t >>= fun u => simulateQ eagerRandomOracle (f u)).run' seed =
    ($ᵗ spec₀.Range t) >>= fun u => (simulateQ eagerRandomOracle (f u)).run' seed := by
  change Prod.fst <$> ((eagerRandomOracle t).run seed >>= fun p =>
      (simulateQ eagerRandomOracle (f p.1)).run p.2) = _
  have h : (eagerRandomOracle (spec := spec₀) t).run seed =
      (fun u => (u, seed)) <$> ($ᵗ spec₀.Range t) := by
    exact eagerRandomOracle.run_nil ht
  rw [h]; simp

/-- Helper: the `run'` of the eager oracle bind consumes the head
when `seed t = u :: us`. -/
private lemma eagerRandomOracle_run'_cons {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀} [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]
    {α : Type} (t : spec₀.Domain) (f : spec₀.Range t → OracleComp spec₀ α)
    (seed : QuerySeed spec₀) (u : spec₀.Range t) (us : List (spec₀.Range t))
    (ht : seed t = u :: us) :
    (eagerRandomOracle t >>= fun v => simulateQ eagerRandomOracle (f v)).run' seed =
    (simulateQ eagerRandomOracle (f u)).run' (seed.update t us) := by
  change Prod.fst <$> ((eagerRandomOracle t).run seed >>= fun p =>
      (simulateQ eagerRandomOracle (f p.1)).run p.2) = _
  have h : (eagerRandomOracle (spec := spec₀) t).run seed =
      pure (u, seed.update t us) := by
    exact eagerRandomOracle.run_cons ht
  rw [h, pure_bind]
  exact (StateT.run'_eq (simulateQ eagerRandomOracle (f u)) (seed.update t us)).symm

/-- The eager random oracle, averaged over a uniformly sampled seed, has the output measure of
the fresh independent-query semantics: the pre-sampled seed values are independent uniform
answers, exactly matching fresh oracle queries.

This is the analog of `seededOracle.evalDist_liftComp_generateSeed_bind_simulateQ_run'` for
`eagerRandomOracle`, which falls back to `ProbComp` rather than `OracleComp spec`. -/
theorem eagerRandomOracle_evalDist_generateSeed_bind {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0, 0} ι₀}
    [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]
    [∀ t, MeasurableSpace (spec₀.Range t)] [∀ t, DiscreteMeasurableSpace (spec₀.Range t)]
    [OracleSpec.IsUniformMeasureSpec spec₀]
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec₀ α) (qc : ι₀ → ℕ) (js : List ι₀) :
    𝒟[do
      let seed ← generateSeed spec₀ qc js
      (simulateQ (eagerRandomOracle (spec := spec₀)) oa).run' seed] = 𝒟[oa] := by
  classical
  revert qc js
  induction oa using OracleComp.inductionOn with
  | pure a => intro qc js; simp
  | query_bind t f ih =>
    intro qc js
    have hsimQ : ∀ seed : QuerySeed spec₀,
        (simulateQ eagerRandomOracle (liftM (query t) >>= f)).run' seed =
        (eagerRandomOracle t >>= fun u => simulateQ eagerRandomOracle (f u)).run' seed :=
      fun _ => by congr 1
    simp_rw [hsimQ]
    by_cases hcount : qc t * js.count t = 0
    · -- Every generated seed is empty at `t`, so the query falls through to a fresh draw.
      rw [evalDist_bind_congr_of_support _ _
          (fun seed => $ᵗ spec₀.Range t >>= fun u =>
            (simulateQ eagerRandomOracle (f u)).run' seed) fun seed hs => by
          rw [eagerRandomOracle_run'_nil t f seed
            (eq_nil_of_mem_support_generateSeed spec₀ qc js seed t hs hcount)],
        OracleComp.evalDist_bind_bind_swap]
      exact evalDist_bind_eq_query_bind_of_uniform t _ SampleableType.evalDist_uniformSample _ f
        fun u => ih u qc js
    · -- Every generated seed starts with a uniform answer at `t`, consumed by the query.
      have hpos : 0 < qc t * js.count t := Nat.pos_of_ne_zero hcount
      rw [evalDist_bind_congr_of_evalDist_eq _ _
        (evalDist_generateSeed_eq_prependValues spec₀ qc js hpos)]
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_eq_query_bind_of_uniform t _ SampleableType.evalDist_uniformSample _ f
        fun u => ?_
      refine Eq.trans (evalDist_bind_congr _ _ _ fun s' => ?_) (ih u _ js.dedup)
      rw [eagerRandomOracle_run'_cons t f _ u (s' t) (QuerySeed.prependValues_singleton s' u)]
      simp only [QuerySeed.prependValues, List.singleton_append, QuerySeed.update_idem,
        QuerySeed.update_eq_self]
