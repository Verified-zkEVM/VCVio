/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.Coercions.SubSpec.Basic
public import VCVio.OracleComp.Constructions.GenerateSeed
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.QueryTracking.Structures

import VCVio.OracleComp.Coercions.SubSpec.Measure

/-!
# Pre-computing Results of Oracle Queries

This file defines a function `QueryImpl.withPregen` that modifies a query implementation
to take in a list of pre-chosen outputs to use when answering queries.
Uses `StateT` so that consumed seed values are threaded to subsequent queries.

Note that ordering is subtle, for example `so.withCaching.withPregen` will first check for seeds
and not cache the result if one is found, while `so.withPregen.withCaching` checks the cache first,
and include seed values into the cache after returning them.
-/

@[expose] public section

open OracleComp OracleSpec

universe u v w

open scoped OracleSpec.PrimitiveQuery

variable {ι : Type u} {spec : OracleSpec ι} [DecidableEq ι]

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Modify a `QueryImpl` to check for pregenerated responses for oracle queries first.
If a seed value is available for the query, it is used and the seed is consumed (the tail
replaces the head). When no seed remains, falls back to the underlying implementation. -/
def withPregen (so : QueryImpl spec m) :
    QueryImpl spec (StateT (QuerySeed spec) m) :=
  fun t => StateT.mk fun seed =>
    match seed t with
    | u :: us => pure (u, seed.update t us)
    | [] => (·, seed) <$> so t

@[simp, grind =]
lemma withPregen_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withPregen t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, seed.update t us)
      | [] => (·, seed) <$> so t := rfl

/-- Seed-hit: `withPregen` returns the head of the seed list without invoking `so`. -/
lemma withPregen_run_cons (so : QueryImpl spec m) {t : spec.Domain}
    {seed : QuerySeed spec} {u : spec.Range t} {us : List (spec.Range t)}
  (h : seed t = u :: us) :
    (so.withPregen t).run seed = pure (u, seed.update t us) := by
  rw [withPregen_apply, StateT.run_mk, h]

/-- Seed-miss: `withPregen` falls back to a single call of `so`, threading the seed unchanged. -/
lemma withPregen_run_nil (so : QueryImpl spec m) {t : spec.Domain}
    {seed : QuerySeed spec} (h : seed t = []) :
    (so.withPregen t).run seed = (·, seed) <$> so t := by
  rw [withPregen_apply, StateT.run_mk, h]

/-! ## Forward query bounds for `withPregen`

A wrapped step makes ≤ 1 underlying query (zero on a seed-hit, one on a seed-miss), so any
bound on `so t` transfers to `(so.withPregen t).run seed`. -/

section QueryBound

variable {ι' : Type u} {spec' : OracleSpec ι'}

lemma isQueryBoundP_run_withPregen
    (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain)
    {p : ι' → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP (so t) p n) (seed : QuerySeed spec) :
    OracleComp.IsQueryBoundP ((so.withPregen t).run seed) p n := by
  cases hseed : seed t with
  | nil =>
      rw [withPregen_run_nil _ hseed]
      exact (OracleComp.isQueryBoundP_map_iff (p := p) _ _ _).mpr h
  | cons u us =>
      rw [withPregen_run_cons _ hseed]
      trivial

lemma isTotalQueryBound_run_withPregen
    (so : QueryImpl spec (OracleComp spec')) (t : spec.Domain) {n : ℕ}
    (h : OracleComp.IsTotalQueryBound (so t) n) (seed : QuerySeed spec) :
    OracleComp.IsTotalQueryBound ((so.withPregen t).run seed) n := by
  cases hseed : seed t with
  | nil =>
      rw [withPregen_run_nil _ hseed]
      exact (OracleComp.isQueryBound_map_iff _ _ _ _ _).mpr h
  | cons u us =>
      rw [withPregen_run_cons _ hseed]
      trivial

lemma isPerIndexQueryBound_run_withPregen
    (so : QueryImpl spec (OracleComp spec)) (t : spec.Domain) {qb : ι → ℕ}
    (h : OracleComp.IsPerIndexQueryBound (so t) qb) (seed : QuerySeed spec) :
    OracleComp.IsPerIndexQueryBound ((so.withPregen t).run seed) qb := by
  cases hseed : seed t with
  | nil =>
      rw [withPregen_run_nil _ hseed]
      exact (OracleComp.isPerIndexQueryBound_map_iff _ _ _).mpr h
  | cons u us =>
      rw [withPregen_run_cons _ hseed]
      trivial

end QueryBound

end QueryImpl

/-! ### Parametric `simulateQ` lifts for `withPregen` -/

namespace OracleComp

variable {ι' : Type u} {spec' : OracleSpec ι'} {α : Type u}

theorem IsQueryBoundP.simulateQ_run_withPregen
    {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    (so : QueryImpl spec (OracleComp spec'))
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsQueryBoundP oa p n)
    (hstep_p : ∀ t, p t → IsQueryBoundP (so t) q 1)
    (hstep_np : ∀ t, ¬ p t → IsQueryBoundP (so t) q 0)
    (seed : QuerySeed spec) :
    IsQueryBoundP ((simulateQ so.withPregen oa).run seed) q n :=
  IsQueryBoundP.simulateQ_run_of_step h
    (fun t hp s' => QueryImpl.isQueryBoundP_run_withPregen so t (hstep_p t hp) s')
    (fun t hnp s' => QueryImpl.isQueryBoundP_run_withPregen so t (hstep_np t hnp) s')
    seed

theorem IsTotalQueryBound.simulateQ_run_withPregen
    (so : QueryImpl spec (OracleComp spec))
    {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n)
    (hstep : ∀ t, IsTotalQueryBound (so t) 1)
    (seed : QuerySeed spec) :
    IsTotalQueryBound ((simulateQ so.withPregen oa).run seed) n :=
  IsTotalQueryBound.simulateQ_run_of_step h
    (fun t s' => QueryImpl.isTotalQueryBound_run_withPregen so t (hstep t) s')
    seed

theorem IsPerIndexQueryBound.simulateQ_run_withPregen
    (so : QueryImpl spec (OracleComp spec))
    {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb)
    (hstep : ∀ t, IsPerIndexQueryBound (so t) (Function.update 0 t 1))
    (seed : QuerySeed spec) :
    IsPerIndexQueryBound ((simulateQ so.withPregen oa).run seed) qb :=
  IsPerIndexQueryBound.simulateQ_run_of_uniform_step h
    (fun t s' => QueryImpl.isPerIndexQueryBound_run_withPregen so t (hstep t) s')
    seed

end OracleComp

/-- Use pregenerated oracle responses for queries, falling back to the real oracle
when the seed is exhausted. Seed consumption is tracked via `StateT`. -/
def OracleSpec.seededOracle :
    QueryImpl spec (StateT (QuerySeed spec) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withPregen

namespace seededOracle

/-- Definitional unfold of `seededOracle` as the pregen handler over the lifting handler. -/
lemma eq_withPregen :
    (spec.seededOracle : QueryImpl spec (StateT (QuerySeed spec) (OracleComp spec))) =
      (QueryImpl.ofLift spec (OracleComp spec)).withPregen := rfl

/-- Seed-hit: `seededOracle t` returns the head of the seed list with no underlying query. -/
lemma run_cons {t : spec.Domain} {seed : QuerySeed spec} {u : spec.Range t}
    {us : List (spec.Range t)} (h : seed t = u :: us) :
    (seededOracle t).run seed = pure (u, seed.update t us) :=
  QueryImpl.withPregen_run_cons _ h

/-- Seed-miss: `seededOracle t` falls back to a single underlying `query t`. -/
lemma run_nil {t : spec.Domain} {seed : QuerySeed spec} (h : seed t = []) :
    (seededOracle t).run seed = (·, seed) <$> (liftM (query t) : OracleComp spec _) := by
  rw [eq_withPregen, QueryImpl.withPregen_run_nil _ h, QueryImpl.ofLift_apply]

@[simp]
lemma apply_eq (t : spec.Domain) :
    seededOracle t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, seed.update t us)
      | [] => (·, seed) <$> OracleSpec.query t := rfl

lemma run_bind_query_eq_pop {α : Type u}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) (seed : QuerySeed spec) :
    (((seededOracle t) >>= fun u => simulateQ seededOracle (mx u)).run seed) =
      match seed.pop t with
      | none => do
          let u ← spec.query t
          (simulateQ seededOracle (mx u)).run seed
      | some (u, seed') =>
          (simulateQ seededOracle (mx u)).run seed' := by
  cases hst : seed t <;>
    simp [seededOracle.apply_eq, StateT.run_bind, QuerySeed.pop, hst]

/-- `run'` form of `run_bind_query_eq_pop`: querying `t` then continuing splits on `seed.pop t`,
either falling back to a fresh `query t` or consuming the popped head. -/
lemma run'_bind_query_eq_pop {α : Type u}
    (t : spec.Domain) (mx : spec.Range t → OracleComp spec α) (seed : QuerySeed spec) :
    (((seededOracle t) >>= fun u => simulateQ seededOracle (mx u)).run' seed) =
      match seed.pop t with
      | none => liftM (query t) >>= fun u => (simulateQ seededOracle (mx u)).run' seed
      | some (u, s') => (simulateQ seededOracle (mx u)).run' s' := by
  change Prod.fst <$>
    (seededOracle t >>= fun u => simulateQ seededOracle (mx u)).run seed = _
  rw [run_bind_query_eq_pop]
  cases seed.pop t with
  | none => simp [map_bind]
  | some p => rfl

/-- A uniform answer draw lifted into the oracle computation keeps its uniform measure. -/
private lemma evalDist_liftComp_uniformSample {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀] [unifSpec ˡ⊂ₒ spec₀]
    [OracleSpec.UniformAnswerMeasure spec₀] (t : ι₀) [MeasurableSpace (spec₀.Range t)]
    [DiscreteMeasurableSpace (spec₀.Range t)] :
    𝒟[liftComp ($ᵗ spec₀.Range t) spec₀] = ProbabilityTheory.uniformOn Set.univ :=
  (evalDist_liftComp_uniform _).trans SampleableType.evalDist_uniformSample

section uniformSeeds

variable {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
  [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀] [unifSpec ˡ⊂ₒ spec₀]
  [OracleSpec.UniformAnswerMeasure spec₀]

/-- The lifted seed distribution splits off a uniform head answer at `t` whenever `t` has a
positive answer count, as `evalDistEq_generateSeed_prependValues` does before lifting. -/
private lemma evalDistEq_liftComp_generateSeed_prependValues (qc : ι₀ → ℕ) (js : List ι₀)
    {t : ι₀} (hpos : 0 < qc t * js.count t) :
    liftComp (generateSeed spec₀ qc js) spec₀ =ᵈ (do
      let u ← liftComp ($ᵗ spec₀.Range t) spec₀
      let s' ← liftComp (generateSeed spec₀
        (Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1)) js.dedup) spec₀
      return s'.prependValues [u]) := by
  refine evalDistEq_iff_evalDist_eq.mpr ?_
  let : MeasurableSpace (QuerySeed spec₀) := ⊤
  have hlift : (liftComp (do
      let u ← $ᵗ spec₀.Range t
      let s' ← generateSeed spec₀
        (Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1)) js.dedup
      return s'.prependValues [u]) spec₀ : OracleComp spec₀ (QuerySeed spec₀)) = (do
      let u ← liftComp ($ᵗ spec₀.Range t) spec₀
      let s' ← liftComp (generateSeed spec₀
        (Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1)) js.dedup) spec₀
      return s'.prependValues [u]) := by
    simp only [liftComp_bind, liftComp_pure]
  rw [← hlift, evalDist_liftComp_uniform, evalDist_liftComp_uniform]
  exact evalDistEq_iff_evalDist_eq.mp (evalDistEq_generateSeed_prependValues spec₀ qc js hpos)

/-- Running a computation against the seeded oracle on a uniformly generated seed has the output
measure of the computation itself: pre-generated answers are fresh uniform answers. -/
theorem evalDist_liftComp_generateSeed_bind_simulateQ_run' (qc : ι₀ → ℕ) (js : List ι₀)
    {α : Type} [MeasurableSpace α] (oa : OracleComp spec₀ α) :
    𝒟[(do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      (simulateQ seededOracle oa).run' seed : OracleComp spec₀ α)] = 𝒟[oa] := by
  classical
  revert qc js
  induction oa using OracleComp.inductionOn with
  | pure x => intro qc js; simp
  | query_bind t mx ih =>
    let : MeasurableSpace (spec₀.Range t) := ⊤
    intro qc js
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map]
    simp_rw [run'_bind_query_eq_pop t mx]
    by_cases hcount : qc t * js.count t = 0
    · -- Every generated seed is empty at `t`, so the query goes to the oracle.
      rw [evalDist_bind_congr_of_support _ _
          (fun s => (liftM (query t) : OracleComp spec₀ _) >>= fun u =>
            (simulateQ seededOracle (mx u)).run' s) fun s hs => by
          rw [support_liftComp] at hs
          rw [(QuerySeed.pop_eq_none_iff s t).mpr
            (eq_nil_of_mem_support_generateSeed spec₀ qc js s t hs hcount)],
        OracleComp.evalDist_bind_bind_swap]
      exact evalDist_bind_congr _ _ _ fun u => ih u qc js
    · -- Every generated seed starts with a uniform answer at `t`, consumed by the query.
      have hpos : 0 < qc t * js.count t := Nat.pos_of_ne_zero hcount
      rw [((evalDistEq_liftComp_generateSeed_prependValues qc js hpos).bind_left _).evalDist_eq]
      simp only [bind_assoc, pure_bind, QuerySeed.pop_prependValues_singleton]
      exact evalDist_bind_eq_query_bind_of_uniform t _
        (evalDist_liftComp_uniformSample t) _ _ fun u => ih u _ js.dedup

private lemma pop_addValue_self_nil_aux {seed : QuerySeed spec} {i : ι} (h : seed i = [])
    (v : spec.Range i) : (seed.addValue i v).pop i = some (v, seed) := by
  have hlist : (seed.addValue i v) i = [v] := by
    simp [QuerySeed.addValue, QuerySeed.addValues, h]
  rw [QuerySeed.pop_eq_some_of_cons _ _ v [] hlist]
  exact congrArg (fun rest => some (v, rest)) <| by
    simpa only [QuerySeed.addValue, QuerySeed.update_addValues_same, h] using
      QuerySeed.update_eq_self seed i

private lemma pop_addValue_self_cons_aux {seed : QuerySeed spec} {i : ι} {u₀ : spec.Range i}
    {rest : List (spec.Range i)} (h : seed i = u₀ :: rest) (v : spec.Range i) :
    (seed.addValue i v).pop i =
      some (u₀, QuerySeed.addValue (seed.update i rest) i v) := by
  have hlist : (seed.addValue i v) i = u₀ :: (rest ++ [v]) := by
    simp [QuerySeed.addValue, QuerySeed.addValues, h]
  rw [QuerySeed.pop_eq_some_of_cons _ _ u₀ (rest ++ [v]) hlist]
  simp [QuerySeed.addValue, QuerySeed.addValues]

private lemma pop_addValue_of_ne_nil_aux {seed : QuerySeed spec} {i t : ι} (hti : t ≠ i)
    (h : seed t = []) (v : spec.Range i) : (seed.addValue i v).pop t = none := by
  rw [QuerySeed.pop_eq_none_iff]
  exact (QuerySeed.addValues_of_ne seed [_] hti).trans h

private lemma pop_addValue_of_ne_cons_aux {seed : QuerySeed spec} {i t : ι} {u₀ : spec.Range t}
    {rest : List (spec.Range t)} (hti : t ≠ i) (h : seed t = u₀ :: rest) (v : spec.Range i) :
    (seed.addValue i v).pop t =
      some (u₀, QuerySeed.addValue (seed.update t rest) i v) := by
  have hlist : (seed.addValue i v) t = u₀ :: rest :=
    (QuerySeed.addValues_of_ne seed [_] hti).trans h
  rw [QuerySeed.pop_eq_some_of_cons _ _ u₀ rest hlist]
  exact congrArg (fun next => some (u₀, next)) <|
    QuerySeed.update_addValues_comm seed (Ne.symm hti) [v] rest

/-- Adding a uniform value at index `i` to a seed does not change the output measure of running
a computation with the seeded oracle: the extra value replaces what would otherwise be a fresh
uniform oracle response. -/
theorem evalDist_liftComp_uniformSample_bind_simulateQ_run'_addValue
    (σ : QuerySeed spec₀) (i : ι₀) {α : Type} [MeasurableSpace α] (oa : OracleComp spec₀ α) :
    𝒟[(do
      let u ← liftComp ($ᵗ spec₀.Range i) spec₀
      (simulateQ seededOracle oa).run' (σ.addValue i u) : OracleComp spec₀ α)] =
    𝒟[((simulateQ seededOracle oa).run' σ : OracleComp spec₀ α)] := by
  revert σ
  induction oa using OracleComp.inductionOn with
  | pure x => intro σ; simp
  | query_bind t mx ih =>
    let : MeasurableSpace (spec₀.Range t) := ⊤
    intro σ
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map]
    simp_rw [run'_bind_query_eq_pop t mx]
    by_cases hti : t = i
    · subst hti
      cases hσt : σ t with
      | nil =>
        simp_rw [pop_addValue_self_nil_aux hσt, (QuerySeed.pop_eq_none_iff σ t).mpr hσt]
        exact evalDist_bind_eq_query_bind_of_uniform t _
          (evalDist_liftComp_uniformSample t) _ _ fun _ => rfl
      | cons u₀ rest =>
        simp_rw [pop_addValue_self_cons_aux hσt, QuerySeed.pop_eq_some_of_cons σ t u₀ rest hσt]
        exact ih u₀ (σ.update t rest)
    · cases hσt : σ t with
      | nil =>
        simp_rw [pop_addValue_of_ne_nil_aux hti hσt, (QuerySeed.pop_eq_none_iff σ t).mpr hσt]
        rw [OracleComp.evalDist_bind_bind_swap]
        exact evalDist_bind_congr _ _ _ fun r => ih r σ
      | cons u₀ rest =>
        simp_rw [pop_addValue_of_ne_cons_aux hti hσt,
          QuerySeed.pop_eq_some_of_cons σ t u₀ rest hσt]
        exact ih u₀ (σ.update t rest)

private lemma takeAtIndex_prependValues_singleton_self_aux {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    [DecidableEq ι₀] (t : ι₀) (k : ℕ) (hk : 0 < k) (u₀ : spec₀.Range t) (s' : QuerySeed spec₀) :
    (s'.prependValues [u₀]).takeAtIndex t k =
      (s'.takeAtIndex t (k - 1)).prependValues [u₀] := by
  funext j; by_cases hj : j = t
  · subst hj
    simp only [QuerySeed.takeAtIndex_apply_self, QuerySeed.prependValues_singleton]
    conv_lhs => rw [show k = (k - 1) + 1 from (Nat.succ_pred_eq_of_pos hk).symm]
    rw [List.take_succ_cons]
  · simp [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hj, QuerySeed.prependValues_of_ne _ _ hj]

private lemma takeAtIndex_prependValues_singleton_of_ne_aux {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    [DecidableEq ι₀] (t i₀ : ι₀) (hti : t ≠ i₀) (k : ℕ) (u₀ : spec₀.Range t)
    (s' : QuerySeed spec₀) :
    (s'.prependValues [u₀]).takeAtIndex i₀ k = (s'.takeAtIndex i₀ k).prependValues [u₀] := by
  funext j; by_cases hji : j = i₀
  · subst hji
    simp [QuerySeed.takeAtIndex_apply_self, QuerySeed.prependValues_of_ne _ _ (Ne.symm hti)]
  · rw [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hji]
    by_cases hjt : j = t
    · subst hjt; simp [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hti]
    · simp [QuerySeed.prependValues_of_ne _ _ hjt, QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hji]

private lemma takeAtIndex_zero_prependValues_singleton_aux {ι₀ : Type} {spec₀ : OracleSpec ι₀}
    [DecidableEq ι₀] (t : ι₀) (u₀ : spec₀.Range t) (s' : QuerySeed spec₀) :
    (s'.prependValues [u₀]).takeAtIndex t 0 = s'.takeAtIndex t 0 := by
  funext j; by_cases hj : j = t
  · subst hj; simp [QuerySeed.takeAtIndex_apply_self]
  · simp [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hj, QuerySeed.prependValues_of_ne _ _ hj]

/-- Truncating a uniformly generated seed after the `k`-th answer at `i₀` does not change the joint
distribution of that prefix and the seeded run's output: the discarded answers are fresh uniform
values, exactly as the oracle would answer after the truncated seed runs out. -/
theorem evalDistEq_liftComp_generateSeed_takeAtIndex_run' (qc : ι₀ → ℕ) (js : List ι₀)
    (i₀ : ι₀) (k : ℕ) {α : Type} (oa : OracleComp spec₀ α) :
    letI : MeasurableSpace (QuerySeed spec₀ × α) := ⊤
    𝒟[(do
      let σ ← liftComp (generateSeed spec₀ qc js) spec₀
      let z ← (simulateQ seededOracle oa).run' σ
      return (σ.takeAtIndex i₀ k, z) : OracleComp spec₀ (QuerySeed spec₀ × α))] =
    𝒟[(do
      let σ ← liftComp (generateSeed spec₀ qc js) spec₀
      let z ← (simulateQ seededOracle oa).run' (σ.takeAtIndex i₀ k)
      return (σ.takeAtIndex i₀ k, z) : OracleComp spec₀ (QuerySeed spec₀ × α))] := by
  classical
  let : MeasurableSpace (QuerySeed spec₀ × α) := ⊤
  revert qc js k
  induction oa using OracleComp.inductionOn with
  | pure a => intro qc js k; simp
  | query_bind t mx ih =>
    let : MeasurableSpace (spec₀.Range t) := ⊤
    intro qc js k
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map]
    simp_rw [run'_bind_query_eq_pop t mx]
    by_cases hcount : qc t * js.count t = 0
    · -- No generated seed has an answer at `t`, before or after truncation.
      have hnil : ∀ s ∈ support (liftComp (generateSeed spec₀ qc js) spec₀), s t = [] :=
        fun s hs => eq_nil_of_mem_support_generateSeed spec₀ qc js s t
          (by rwa [support_liftComp] at hs) hcount
      have htake : ∀ s ∈ support (liftComp (generateSeed spec₀ qc js) spec₀),
          (s.takeAtIndex i₀ k) t = [] := by
        intro s hs
        by_cases hti : t = i₀
        · subst hti; simp [QuerySeed.takeAtIndex, hnil s hs]
        · rw [QuerySeed.takeAtIndex_apply_of_ne _ _ _ _ hti]; exact hnil s hs
      refine Eq.trans (evalDist_bind_congr_of_support _ _
          (fun s => (liftM (query t) : OracleComp spec₀ _) >>= fun u =>
            (simulateQ seededOracle (mx u)).run' s >>= fun z => pure (s.takeAtIndex i₀ k, z))
          fun s hs => by rw [(QuerySeed.pop_eq_none_iff s t).mpr (hnil s hs), bind_assoc])
        (Eq.trans ?_ (evalDist_bind_congr_of_support _ _
          (fun s => (liftM (query t) : OracleComp spec₀ _) >>= fun u =>
            (simulateQ seededOracle (mx u)).run' (s.takeAtIndex i₀ k) >>= fun z =>
              pure (s.takeAtIndex i₀ k, z))
          fun s hs => by
            rw [(QuerySeed.pop_eq_none_iff _ t).mpr (htake s hs), bind_assoc]).symm)
      rw [OracleComp.evalDist_bind_bind_swap]
      conv_rhs => rw [OracleComp.evalDist_bind_bind_swap]
      exact evalDist_bind_congr _ _ _ fun u => by simpa only [bind_assoc] using ih u qc js k
    · -- Every generated seed starts with a uniform answer at `t`.
      have hpos : 0 < qc t * js.count t := Nat.pos_of_ne_zero hcount
      rw [((evalDistEq_liftComp_generateSeed_prependValues qc js hpos).bind_left _).evalDist_eq,
        ((evalDistEq_liftComp_generateSeed_prependValues qc js hpos).bind_left _).evalDist_eq]
      simp only [bind_assoc, pure_bind, QuerySeed.pop_prependValues_singleton]
      set qc' := Function.update (fun i => qc i * js.count i) t (qc t * js.count t - 1)
      -- Transport the inductive hypothesis along a relabelling of the observed prefix.
      have hmap : ∀ (u : spec₀.Range t) (k' : ℕ) (F : QuerySeed spec₀ → QuerySeed spec₀),
          𝒟[liftComp (generateSeed spec₀ qc' js.dedup) spec₀ >>= fun s' =>
            (simulateQ seededOracle (mx u)).run' s' >>= fun z =>
              pure (F (s'.takeAtIndex i₀ k'), z)] =
          𝒟[liftComp (generateSeed spec₀ qc' js.dedup) spec₀ >>= fun s' =>
            (simulateQ seededOracle (mx u)).run' (s'.takeAtIndex i₀ k') >>= fun z =>
              pure (F (s'.takeAtIndex i₀ k'), z)] := by
        intro u k' F
        have h := ((EvalDistEq.of_evalDist_eq (ih u qc' js.dedup k')).map
          (fun p : QuerySeed spec₀ × α => (F p.1, p.2))).evalDist_eq
        simpa only [map_bind, map_pure] using h
      by_cases hti : t = i₀
      · subst hti
        by_cases hk : k = 0
        · -- The truncated seed has no answer at `t`: the query goes to the oracle.
          subst hk
          have hpop0 : ∀ s' : QuerySeed spec₀, (s'.takeAtIndex t 0).pop t = none := fun s' =>
            (QuerySeed.pop_eq_none_iff _ t).mpr (by simp [QuerySeed.takeAtIndex])
          simp only [takeAtIndex_zero_prependValues_singleton_aux, hpop0, bind_assoc]
          conv_rhs => rw [OracleComp.evalDist_bind_const, OracleComp.evalDist_bind_bind_swap]
          exact evalDist_bind_eq_query_bind_of_uniform t _
            (evalDist_liftComp_uniformSample t) _ _ fun u =>
            hmap u 0 id
        · -- Both runs consume the head answer; the prefix shortens by one.
          have hk' : 0 < k := Nat.pos_of_ne_zero hk
          simp only [takeAtIndex_prependValues_singleton_self_aux t k hk',
            QuerySeed.pop_prependValues_singleton]
          exact evalDist_bind_congr _ _ _ fun u =>
            hmap u (k - 1) fun τ => τ.prependValues [u]
      · -- Both runs consume the head answer at `t ≠ i₀`; the prefix is unchanged.
        simp only [takeAtIndex_prependValues_singleton_of_ne_aux t i₀ hti k,
          QuerySeed.pop_prependValues_singleton]
        exact evalDist_bind_congr _ _ _ fun u => hmap u k fun τ => τ.prependValues [u]

end uniformSeeds

section queryBounds

variable {α : Type u}

/-- If a pre-generated seed already supplies all but `residual t` of the answers allowed by the
structural per-index query bound `qb`, then running `oa` against `seededOracle` can make at most
those residual live queries.

This theorem is the core replay-cost statement for seeded simulations: a large enough seed turns
most oracle interactions into deterministic table lookups, leaving only the uncovered suffix of
the computation as genuine oracle queries. -/
theorem isPerIndexQueryBound_run'_of_seedCoverage
    {oa : OracleComp spec α} {qb residual : ι → ℕ} {seed : QuerySeed spec}
    (hqb : IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t - residual t ≤ (seed t).length) :
    IsPerIndexQueryBound ((simulateQ seededOracle oa).run' seed) residual := by
  revert qb residual seed
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro qb residual seed _ _
      simp
  | query_bind t mx ih =>
      intro qb residual seed hqb hcover
      rw [isPerIndexQueryBound_query_bind_iff] at hqb
      rw [show (simulateQ seededOracle (liftM (query t) >>= mx)).run' seed =
            ((seededOracle t >>= fun r => simulateQ seededOracle (mx r)).run' seed) by simp,
        run'_bind_query_eq_pop t mx seed]
      cases hpop : seed.pop t with
      | none =>
          rw [isPerIndexQueryBound_query_bind_iff]
          have hres_pos : 0 < residual t := by
            have hcov_t := hcover t
            rw [QuerySeed.pop_eq_none_iff] at hpop
            simp [hpop] at hcov_t
            lia
          refine ⟨hres_pos, ?_⟩
          intro u
          simpa using
            (ih u
              (qb := Function.update qb t (qb t - 1))
              (residual := Function.update residual t (residual t - 1))
              (seed := seed)
              (hqb := hqb.2 u)
              (by
                intro j
                have hcov_j := hcover j
                by_cases hj : j = t
                · subst hj
                  simp only [Function.update_self]
                  lia
                · simpa [Function.update_of_ne hj, hj] using hcov_j))
      | some p =>
          rcases p with ⟨u, seed'⟩
          simpa using
            (ih u
              (qb := Function.update qb t (qb t - 1))
              (residual := residual)
              (seed := seed')
              (hqb := hqb.2 u)
              (by
                intro j
                have hcov_j := hcover j
                by_cases hj : j = t
                · subst hj
                  have hlen : (seed j).length = (seed' j).length + 1 := by
                    rw [← QuerySeed.cons_of_pop_eq_some seed j u seed' hpop, List.length_cons]
                  simp only [Function.update_self]
                  lia
                · rw [QuerySeed.rest_eq_update_tail_of_pop_eq_some seed t u seed' hpop]
                  simpa [Function.update_of_ne hj, hj] using hcov_j))

/-- A seed that covers the full structural query bound eliminates all live oracle queries. -/
theorem isPerIndexQueryBound_run'_zero
    {oa : OracleComp spec α} {qb : ι → ℕ} {seed : QuerySeed spec}
    (hqb : IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t ≤ (seed t).length) :
    IsPerIndexQueryBound ((simulateQ seededOracle oa).run' seed) 0 :=
  isPerIndexQueryBound_run'_of_seedCoverage (oa := oa) (qb := qb) (residual := 0)
    (seed := seed) hqb fun t => by simpa using hcover t

/-- If the seed stores only the first `k` answers for oracle `i`, then the replay can make live
queries only to `i`, and at most `qb i - k` of them remain.

This is the structural query-bound form of the usual forking-lemma intuition: after rewinding to
the `k`-th query to oracle `i`, every earlier answer is fixed by the prefix seed, so only the
suffix after the fork point can still hit the live oracle. -/
theorem isPerIndexQueryBound_run'_takeAtIndex
    {oa : OracleComp spec α} {qb : ι → ℕ} {seed : QuerySeed spec} {i : ι} {k : ℕ}
    (hqb : IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t ≤ (seed t).length)
    (hk : k ≤ qb i) :
    IsPerIndexQueryBound
      ((simulateQ seededOracle oa).run' (seed.takeAtIndex i k))
      (Function.update 0 i (qb i - k)) := by
  refine isPerIndexQueryBound_run'_of_seedCoverage
    (oa := oa) (qb := qb) (residual := Function.update 0 i (qb i - k))
    (seed := seed.takeAtIndex i k) hqb ?_
  intro t
  grind [QuerySeed.takeAtIndex_apply_self, QuerySeed.takeAtIndex_apply_of_ne,
    Function.update_of_ne]

/-- After rewinding to query index `s` and appending one fresh answer at oracle `i`, the replayed
run can still make live queries only to `i`, with at most `qb i - (s + 1)` such queries left. -/
theorem isPerIndexQueryBound_run'_takeAtIndex_addValue
    {oa : OracleComp spec α} {qb : ι → ℕ} {seed : QuerySeed spec} {i : ι}
    (hqb : IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t ≤ (seed t).length)
    (s : Fin (qb i + 1)) (u : spec.Range i) :
    IsPerIndexQueryBound
      ((simulateQ seededOracle oa).run' ((seed.takeAtIndex i ↑s).addValue i u))
      (Function.update 0 i (qb i - (↑s + 1))) := by
  refine isPerIndexQueryBound_run'_of_seedCoverage
    (oa := oa) (qb := qb) (residual := Function.update 0 i (qb i - (↑s + 1)))
    (seed := (seed.takeAtIndex i ↑s).addValue i u) hqb ?_
  intro t
  by_cases ht : t = i
  · subst ht
    have hs' : ↑s ≤ (seed t).length := le_trans (Nat.lt_succ_iff.mp s.2) (hcover t)
    simp [QuerySeed.addValue, QuerySeed.addValues]
    omega
  · simp [QuerySeed.addValue, QuerySeed.addValues, ht, hcover t]

end queryBounds

/-! ### Forward query bounds for `seededOracle`

Forward only — the reverse fails because pregenerated values strictly reduce the count. -/

theorem isTotalQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
    {α : Type} {oa : OracleComp spec₀ α} {n : ℕ}
    (h : OracleComp.IsTotalQueryBound oa n) (seed : QuerySeed spec₀) :
    OracleComp.IsTotalQueryBound ((simulateQ spec₀.seededOracle oa).run seed) n := by
  rw [eq_withPregen]
  exact OracleComp.IsTotalQueryBound.simulateQ_run_withPregen _ h
    (fun t => (OracleComp.isQueryBound_query_iff t 1 _ _).mpr Nat.one_pos) seed

theorem isQueryBoundP_run_simulateQ {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
    {α : Type} {oa : OracleComp spec₀ α}
    {p : ι₀ → Prop} [DecidablePred p] {n : ℕ}
    (h : OracleComp.IsQueryBoundP oa p n) (seed : QuerySeed spec₀) :
    OracleComp.IsQueryBoundP ((simulateQ spec₀.seededOracle oa).run seed) p n := by
  rw [eq_withPregen]
  exact OracleComp.IsQueryBoundP.simulateQ_run_withPregen _ h
    (fun t _ => (OracleComp.isQueryBoundP_query_iff p t 1).mpr (fun _ => Nat.one_pos))
    (fun t hnp => (OracleComp.isQueryBoundP_query_iff p t 0).mpr (fun hpt => absurd hpt hnp))
    seed

theorem isPerIndexQueryBound_run_simulateQ {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
    {α : Type} {oa : OracleComp spec₀ α} {qb : ι₀ → ℕ}
    (h : OracleComp.IsPerIndexQueryBound oa qb) (seed : QuerySeed spec₀) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.seededOracle oa).run seed) qb := by
  rw [eq_withPregen]
  refine OracleComp.IsPerIndexQueryBound.simulateQ_run_withPregen _ h ?_ seed
  intro t
  rw [QueryImpl.ofLift_apply]
  exact (OracleComp.isPerIndexQueryBound_query_iff t (Function.update 0 t 1)).mpr (by
    simp [Function.update_self])

/-- State-preserving variant of `isPerIndexQueryBound_run'_zero`: when the seed covers `qb`
at every index, the simulation makes zero further queries even with the seed in scope. -/
theorem isPerIndexQueryBound_run_simulateQ_zero
    {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
    {α : Type}
    {oa : OracleComp spec₀ α} {qb : ι₀ → ℕ} {seed : QuerySeed spec₀}
    (hqb : OracleComp.IsPerIndexQueryBound oa qb)
    (hseed : ∀ t, qb t ≤ (seed t).length) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.seededOracle oa).run seed) 0 := by
  have h := isPerIndexQueryBound_run'_zero (oa := oa) (qb := qb) (seed := seed) hqb hseed
  rw [StateT.run'] at h
  exact (OracleComp.isPerIndexQueryBound_map_iff _ Prod.fst 0).mp h

/-- State-preserving variant of `isPerIndexQueryBound_run'_of_seedCoverage`: any uncovered
suffix of the seed becomes the residual budget in the result spec. -/
theorem isPerIndexQueryBound_run_simulateQ_of_seedCoverage
    {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
    {α : Type}
    {oa : OracleComp spec₀ α} {qb residual : ι₀ → ℕ} {seed : QuerySeed spec₀}
    (hqb : OracleComp.IsPerIndexQueryBound oa qb)
    (hcover : ∀ t, qb t - residual t ≤ (seed t).length) :
    OracleComp.IsPerIndexQueryBound ((simulateQ spec₀.seededOracle oa).run seed) residual := by
  have h := isPerIndexQueryBound_run'_of_seedCoverage (oa := oa) (qb := qb)
    (residual := residual) (seed := seed) hqb hcover
  rw [StateT.run'] at h
  exact (OracleComp.isPerIndexQueryBound_map_iff _ Prod.fst residual).mp h

end seededOracle
