/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/

module
public import VCVio.OracleComp.QueryTracking.Collision
public import ToMathlib.Data.ENNReal.Gauss
public import VCVio.OracleComp.EvalDist.Measure

/-!
# ROM Birthday Bound

Per-pair collision bounds and union bound birthday argument for random oracle
collision probability under uniform measure semantics. Covers both log-based and cache-based
collision bounds, with per-index corollaries.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal Finset

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

section logCollision

variable [IsUniformMeasureSpec spec] [∀ t, Fintype (spec.Range t)]

/-! ## Per-Pair Collision Bound (Textbook Step 3)

For each pair (i,j) of positions in the log with distinct inputs,
Pr[outputs equal] ≤ 1/|C|, because each query returns an independent uniform sample. -/

/-- A single uniform query hits a fixed sigma-typed entry with probability at most the inverse
cardinality of that entry's response type. -/
private lemma prEvent_query_mk_eq_le (t : spec.Domain)
    (entry : (t : spec.Domain) × spec.Range t) :
    Pr{let u ← (query t : OracleComp spec (spec.Range t))}[Sigma.mk t u = entry] ≤
      (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨t', v⟩ := entry
  by_cases ht : t = t'
  · subst ht
    rw [prEvent_liftM_query_eq_card_div]
    have hfilter : (Finset.univ.filter fun u : spec.Range t =>
        (⟨t, u⟩ : (t : spec.Domain) × spec.Range t) = ⟨t, v⟩) = {v} := by
      ext u; simp
    rw [hfilter, Finset.card_singleton, Nat.cast_one, one_div]
  · exact le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun u h =>
      ht (congrArg Sigma.fst h)) bot_le

/-- **ROM uniformity at a log position**: For any `loggingOracle` trace, the
probability that the k-th log entry matches a fixed sigma-typed value `⟨t, v⟩`
is at most `1/|Range t|`. Each query response is an independent uniform draw. -/
theorem prEvent_log_entry_eq_le {α : Type}
    (oa : OracleComp spec α)
    (k : ℕ) (entry : (t : spec.Domain) × spec.Range t) :
    Pr{let z ← (simulateQ loggingOracle oa).run}[z.2[k]? = some entry] ≤
      (Fintype.card (spec.Range entry.1) : ℝ≥0∞)⁻¹ := by
  classical
  induction oa using OracleComp.inductionOn generalizing k with
  | pure x =>
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_) bot_le
    simp only [simulateQ_pure, WriterT.run_pure', List.empty_eq, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; simp at h
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind]
    cases k with
    | zero =>
      refine (prEvent_bind_le_prEvent_of_forall_eq_zero _ _
        (fun u => (⟨t, u⟩ : (t : spec.Domain) × spec.Range t) = entry) _
        fun u hu => ?_).trans (prEvent_query_mk_eq_le t entry)
      rw [prEvent_map]
      exact prEvent_eq_zero_of_forall_not _ _ fun z h => hu (by simpa using h)
    | succ k' =>
      refine prEvent_bind_le_of_forall_le _ _ _ fun u => ?_
      rw [prEvent_map]
      simpa only [List.getElem?_cons_succ] using ih u k'

/-- **Uniformized log entry bound**: the probability that position `k` of a `loggingOracle`
trace equals a fixed sigma-typed entry is at most `1/|Range default|`, assuming `|Range default|`
is minimal across all oracle indices.

This is a corollary of `prEvent_log_entry_eq_le` (which gives `1/|Range entry.1|`) combined
with the `hrange` monotonicity hypothesis. -/
theorem prEvent_log_output_heq_le {α : Type}
    [Inhabited ι]
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (oa : OracleComp spec α)
    (k : ℕ) (entry : (t : spec.Domain) × spec.Range t) :
    Pr{let z ← (simulateQ loggingOracle oa).run}[z.2[k]? = some entry] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ :=
  (prEvent_log_entry_eq_le oa k entry).trans
    (ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (hrange entry.1)))

/-- Probability that the k-th log entry's output is HEq to a fixed value `u₀ : spec.Range t₀`.
Unlike `prEvent_log_entry_eq_le` which matches the full sigma entry, this only constrains
the output component. The bound uses `hrange` to get `1/|Range default|`. -/
theorem prEvent_log_output_match_le {α : Type}
    [Inhabited ι]
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (oa : OracleComp spec α)
    (k : ℕ) (t₀ : spec.Domain) (u₀ : spec.Range t₀) :
    Pr{let z ← (simulateQ loggingOracle oa).run}[∃ (s : spec.Domain) (v : spec.Range s),
        z.2[k]? = some (⟨s, v⟩ : (t : spec.Domain) × spec.Range t) ∧ HEq u₀ v] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  classical
  induction oa using OracleComp.inductionOn generalizing k with
  | pure x =>
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_) bot_le
    simp only [simulateQ_pure, WriterT.run_pure', List.empty_eq, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨s, v, hlog, _⟩ := h; simp at hlog
  | query_bind t mx ih =>
    rw [run_simulateQ_loggingOracle_query_bind]
    cases k with
    | zero =>
      refine (prEvent_bind_le_prEvent_of_forall_eq_zero _ _ (fun u => HEq u₀ u) _
        fun u hu => ?_).trans ?_
      · rw [prEvent_map]
        refine prEvent_eq_zero_of_forall_not _ _ fun z ⟨s, v, hlog, hheq⟩ => hu ?_
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hlog
        cases hlog; exact hheq
      · rw [prEvent_liftM_query_eq_card_div]
        have hcard : (Finset.univ.filter fun u : spec.Range t => HEq u₀ u).card ≤ 1 :=
          Finset.card_le_one.mpr fun a ha b hb => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            exact eq_of_heq (ha.symm.trans hb)
        calc ((Finset.univ.filter fun u : spec.Range t => HEq u₀ u).card : ℝ≥0∞) /
              Fintype.card (spec.Range t)
            ≤ 1 / Fintype.card (spec.Range t) := by gcongr; exact_mod_cast hcard
          _ ≤ (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
            rw [one_div]; exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hrange t)
    | succ k' =>
      refine prEvent_bind_le_of_forall_le _ _ _ fun u => ?_
      rw [prEvent_map]
      simpa only [List.getElem?_cons_succ] using ih u k'

/-- **Per-pair collision bound**: For any two positions in a `loggingOracle` trace
with distinct inputs, the probability that their outputs are HEq-equal is ≤ 1/|C|.

This is the core ROM property: distinct oracle inputs yield independent uniform outputs.
The `hrange` hypothesis ensures `|Range default|` is minimal across all oracle indices,
so the bound holds uniformly with `|C| = |Range default|`. -/
theorem prEvent_pair_collision_le {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (i j : Fin n) (hij : i ≠ j) :
    Pr{let z ← (simulateQ loggingOracle oa).run}[z.2.length > i.val ∧ z.2.length > j.val ∧
        z.2[i]?.bind (fun ei : (t : spec.Domain) × spec.Range t => z.2[j]?.map
          (fun ej : (t : spec.Domain) × spec.Range t => ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) =
            some true] ≤
      (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  refine le_trans (prEvent_mono _ _ _ fun z h => h.2.2) ?_
  suffices h : ∀ (β : Type) (ob : OracleComp spec β) (i j : ℕ) (_ : i ≠ j),
      Pr{let z ← (simulateQ loggingOracle ob).run}[z.2[i]?.bind
        (fun ei : (t : spec.Domain) × spec.Range t => z.2[j]?.map
          (fun ej : (t : spec.Domain) × spec.Range t => ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) =
            some true] ≤
        (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ from
    h α oa i.val j.val (Fin.val_ne_of_ne hij)
  intro β ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
    intro i j _
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_) bot_le
    simp only [simulateQ_pure, WriterT.run_pure', List.empty_eq, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz; simp at h
  | query_bind t mx ih =>
    intro i j hij
    rw [run_simulateQ_loggingOracle_query_bind]
    -- The matched output lives at position `k` in the log; both end cases reduce to
    -- `prEvent_log_output_match_le` after extracting the sigma entry.
    have key : ∀ (u : spec.Range t) (k : ℕ) (e : β × QueryLog spec → Prop),
        (∀ z, e z → ∃ s v, z.2[k]? = some ⟨s, v⟩ ∧ HEq u v) →
        Pr{let z ← (simulateQ loggingOracle (mx u)).run}[e z] ≤
          (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := fun u k e he =>
      (prEvent_mono _ _ _ he).trans (prEvent_log_output_match_le hrange (mx u) k t u)
    refine prEvent_bind_le_of_forall_le _ _ _ fun u => ?_
    rw [prEvent_map]
    match i, j, hij with
    | 0, 0, hij => exact absurd rfl hij
    | 0, j' + 1, _ =>
      refine key u j' _ fun z hev => ?_
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.bind_some] at hev
      match hz : z.2[j']? with
      | none => simp [hz] at hev
      | some ⟨s, v⟩ =>
        simp only [hz, Option.map_some] at hev
        change some (t ≠ s ∧ HEq u v) = some (true = true) at hev
        have hp : t ≠ s ∧ HEq u v := (Option.some.inj hev).symm ▸ rfl
        exact ⟨s, v, rfl, hp.2⟩
    | i' + 1, 0, _ =>
      refine key u i' _ fun z hev => ?_
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hev
      match hz : z.2[i']? with
      | none => simp [hz] at hev
      | some ⟨s, v⟩ =>
        simp only [hz, Option.bind_some, Option.map_some] at hev
        change some (s ≠ t ∧ HEq v u) = some (true = true) at hev
        have hp : s ≠ t ∧ HEq v u := (Option.some.inj hev).symm ▸ rfl
        exact ⟨s, v, rfl, hp.2.symm⟩
    | i' + 1, j' + 1, hij =>
      simpa only [List.getElem?_cons_succ] using ih u i' j' (by lia)

/-! ## Union Bound Birthday (Textbook Steps 4-5)

Collision = ∃ pair with collision. Union bound over C(n,2) pairs gives n²/(2|C|). -/

/-- **Tight birthday bound for `loggingOracle`** (total query bound):
The probability of a collision in the query log is ≤ `C(n,2)/|C|`, where `C(n,2)`
is the exact number of unordered pairs of query positions. -/
theorem prEvent_logCollision_le_birthday_total_tight {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr{let z ← (simulateQ loggingOracle oa).run}[LogHasCollision z.2] ≤
      (Nat.choose n 2 : ℝ≥0∞) / (Fintype.card (spec.Range default)) := by
  let E : Fin n × Fin n → α × QueryLog spec → Prop := fun ij z =>
    z.2.length > ij.1.val ∧ z.2.length > ij.2.val ∧
      z.2[ij.1]?.bind (fun ei => z.2[ij.2]?.map (fun ej =>
        ei.1 ≠ ej.1 ∧ HEq ei.2 ej.2)) = some true
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)
  calc Pr{let z ← (simulateQ loggingOracle oa).run}[LogHasCollision z.2]
      ≤ ∑ _ij ∈ pairs, (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
        refine le_trans (prEvent_mono_of_support _ _ (fun z => ∃ ij ∈ pairs, E ij z) ?_) ?_
        · intro z hz hcoll
          obtain ⟨i, j, hij, hdist, heq⟩ := hcoll
          have hlen := log_length_le_of_mem_support_run_simulateQ hbound hz
          have hi_lt : i.val < n := i.isLt.trans_le hlen
          have hj_lt : j.val < n := j.isLt.trans_le hlen
          have key : ∀ (a b : Fin z.2.length) (ha : a.val < n) (hb : b.val < n),
              a.val < b.val → z.2[a].1 ≠ z.2[b].1 → HEq z.2[a].2 z.2[b].2 →
              ∃ ij ∈ pairs, E ij z := fun a b ha hb hab hd he =>
            ⟨(⟨a.val, ha⟩, ⟨b.val, hb⟩), by simpa [pairs] using hab, a.isLt, b.isLt, by
              rw [show z.2[(⟨a.val, ha⟩ : Fin n)]? = some z.2[a] by simp,
                show z.2[(⟨b.val, hb⟩ : Fin n)]? = some z.2[b] by simp]
              simp_all⟩
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · exact key i j hi_lt hj_lt hlt hdist heq
          · exact key j i hj_lt hi_lt hgt hdist.symm heq.symm
        · refine (prEvent_exists_finset_le pairs _ E).trans (Finset.sum_le_sum ?_)
          intro ⟨i, j⟩ hij
          simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij
          exact prEvent_pair_collision_le oa n hrange i j (Fin.ne_of_lt hij)
    _ = (Nat.choose n 2 : ℝ≥0∞) / (Fintype.card (spec.Range default)) := by
        rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, Fintype.card_product_filter_lt,
          Fintype.card_fin]

/-- **Birthday bound for `loggingOracle`** (total query bound):
The probability of a collision in the query log is ≤ n²/(2|C|).

A loose corollary of `prEvent_logCollision_le_birthday_total_tight`. -/
theorem prEvent_logCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr{let z ← (simulateQ loggingOracle oa).run}[LogHasCollision z.2] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  calc Pr{let z ← (simulateQ loggingOracle oa).run}[LogHasCollision z.2]
      ≤ (Nat.choose n 2 : ℝ≥0∞) / (Fintype.card (spec.Range default)) :=
        prEvent_logCollision_le_birthday_total_tight oa n hbound hrange
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
        rw [← ENNReal.mul_div_mul_left (c := 2) (↑(Nat.choose n 2))
          (↑(Fintype.card (spec.Range default))) (by norm_num) (by norm_num)]
        gcongr
        exact_mod_cast (show 2 * Nat.choose n 2 ≤ n ^ 2 by
          rw [Nat.choose_two_right, pow_two]
          exact (Nat.mul_div_le (n * (n - 1)) 2).trans (by gcongr; lia))

end logCollision

/-! ## Cache Collisions -/

section cacheCollision

variable [DecidableEq ι]

open Classical in
/-- At a fresh query, the number of responses that would create a cache collision is at most
the number of keys known to be populated in the current collision-free cache.

The finite set `S` need only cover the populated keys; it may be a convenient external bound
rather than the cache's exact support. This form is intended for adaptive birthday arguments,
where `S` grows by one after each cache miss. -/
theorem card_responses_creating_cacheCollision_le [∀ t, Fintype (spec.Range t)]
    {cache₀ : QueryCache spec} {t : spec.Domain}
    {S : Finset spec.Domain} (hnocoll : ¬CacheHasCollision cache₀)
    (hSmem : ∀ t', cache₀ t' ≠ none → t' ∈ S) :
    (Finset.univ.filter (fun u => CacheHasCollision (cache₀.cacheQuery t u))).card ≤ S.card := by
  have hmust : ∀ u, CacheHasCollision (cache₀.cacheQuery t u) →
      ∃ t' : spec.Domain, t' ≠ t ∧ ∃ v : spec.Range t', cache₀ t' = some v ∧ HEq u v := by
    intro u ⟨t₁, t₂, u₁, u₂, hne, h1, h2, hequ⟩
    by_cases ht1 : t₁ = t
    · subst ht1
      refine ⟨t₂, hne.symm, u₂, by rwa [QueryCache.cacheQuery_of_ne _ _ hne.symm] at h2, ?_⟩
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at h1
      subst h1; exact hequ
    · by_cases ht2 : t₂ = t
      · subst ht2
        refine ⟨t₁, hne, u₁, by rwa [QueryCache.cacheQuery_of_ne _ _ ht1] at h1, ?_⟩
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at h2
        subst h2; exact hequ.symm
      · exact absurd ⟨t₁, t₂, u₁, u₂, hne, by rwa [QueryCache.cacheQuery_of_ne _ _ ht1] at h1,
          by rwa [QueryCache.cacheQuery_of_ne _ _ ht2] at h2, hequ⟩ hnocoll
  let f : spec.Range t → spec.Domain := fun u =>
    if h : CacheHasCollision (cache₀.cacheQuery t u) then (hmust u h).choose else t
  refine Finset.card_le_card_of_injOn f (fun u hu => ?_) (fun u₁ hu₁ u₂ hu₂ hfeq => ?_)
  · have hu' := (Finset.mem_filter.mp hu).2
    obtain ⟨_, v, hcache, _⟩ := (hmust u hu').choose_spec
    rw [show f u = _ from dite_eq_left hu']
    exact hSmem _ (hcache ▸ Option.some_ne_none v)
  · have hu₁' := (Finset.mem_filter.mp hu₁).2
    have hu₂' := (Finset.mem_filter.mp hu₂).2
    rw [show f u₁ = _ from dite_eq_left hu₁', show f u₂ = _ from dite_eq_left hu₂'] at hfeq
    obtain ⟨_, v₁, hcache₁, heq₁⟩ := (hmust u₁ hu₁').choose_spec
    obtain ⟨_, v₂, hcache₂, heq₂⟩ := (hmust u₂ hu₂').choose_spec
    suffices aux : ∀ (a b : spec.Domain) (va : spec.Range a) (vb : spec.Range b),
        cache₀ a = some va → cache₀ b = some vb → a = b → HEq va vb from
      eq_of_heq (heq₁.trans ((aux _ _ _ _ hcache₁ hcache₂ hfeq).trans heq₂.symm))
    intro a b va vb ha hb hab
    subst hab; rw [ha] at hb; exact heq_of_eq (Option.some.inj hb)

private lemma run_simulateQ_cachingOracle_query_bind_of_hit {α : Type} {t : spec.Domain}
    {mx : spec.Range t → OracleComp spec α} {cache₀ : QueryCache spec} {v : spec.Range t}
    (hv : cache₀ t = some v) :
    (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
      (simulateQ cachingOracle (mx v)).run cache₀ := by
  simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
  have hcache : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
      pure (v, cache₀) := by
    simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
      StateT.run_bind, StateT.run_get, hv, pure_bind, StateT.run_pure]
  rw [hcache, pure_bind]
  simp [OracleQuery.cont_query]

private lemma run_simulateQ_cachingOracle_query_bind_of_miss {α : Type} {t : spec.Domain}
    {mx : spec.Range t → OracleComp spec α} {cache₀ : QueryCache spec}
    (ht_none : cache₀ t = none) :
    (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
      liftM (query t) >>= fun u =>
        (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u) := by
  simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
  have hstep : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
      (liftM (query t) >>= fun u => pure (u, cache₀.cacheQuery t u) : OracleComp spec _) := by
    simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
      StateT.run_bind, StateT.run_get, pure_bind, ht_none]
    change (StateT.lift (PFunctor.FreeM.lift (P := spec.toPFunctor) t) cache₀ >>= _) = _
    simp only [StateT.lift, monad_norm, modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run]; rfl
  rw [hstep]; simp [monad_norm]

variable [IsUniformMeasureSpec spec] [∀ t, Fintype (spec.Range t)]

/-- **Cache-collision induction core**: running any computation `ob` (bounded by `m` queries)
through `cachingOracle` starting from a collision-free cache `cache₀` whose populated keys fit
in a set of size at most `k` produces a collision with probability at most
`∑ j ∈ range m, (k + j) / |Range default|`.

Generalizing over the starting cache and its key budget `k` lets the bound thread through each
fresh query: a cache miss enlarges the support set by one and shifts the per-step factor from
`k` to `k + 1`. The `hrange` hypothesis ensures `|Range default|` is minimal across oracle
indices, so the uniform per-query bound `1/|Range t|` is dominated by `1/|Range default|`.
This is the inductive engine behind `prEvent_cacheCollision_le_birthday_total_tight`. -/
private lemma prEvent_cacheCollision_run_le_sum_aux [Inhabited ι]
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    {β : Type} (ob : OracleComp spec β) (m k : ℕ)
    (hm : IsTotalQueryBound ob m)
    (cache₀ : QueryCache spec)
    (hnocoll : ¬CacheHasCollision cache₀)
    (hbnd : ∃ S : Finset spec.Domain, S.card ≤ k ∧ ∀ t, cache₀ t ≠ none → t ∈ S) :
    Pr{let z ← (simulateQ cachingOracle ob).run cache₀}[CacheHasCollision z.2] ≤
      ∑ j ∈ range m, ((k + j : ℕ) : ℝ≥0∞) *
        (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  let C := (Fintype.card (spec.Range default) : ℝ≥0∞)
  induction ob using OracleComp.inductionOn generalizing m k cache₀ with
  | pure x =>
    rw [simulateQ_pure]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_) bot_le
    change z ∈ support (pure (x, cache₀) : OracleComp _ _) at hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hnocoll h
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hm
    obtain ⟨hpos, hrest⟩ := hm
    by_cases ht : ∃ v, cache₀ t = some v
    · obtain ⟨v, hv⟩ := ht
      rw [run_simulateQ_cachingOracle_query_bind_of_hit hv]
      calc Pr{let z ← (simulateQ cachingOracle (mx v)).run cache₀}[CacheHasCollision z.2]
          ≤ ∑ j ∈ range (m - 1), ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
            ih v (m - 1) k (hrest v) cache₀ hnocoll hbnd
        _ ≤ ∑ j ∈ range m, ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
            Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le m 1))
    · push Not at ht
      have ht_none : cache₀ t = none := Option.eq_none_iff_forall_ne_some.mpr ht
      rw [run_simulateQ_cachingOracle_query_bind_of_miss ht_none]
      have hε₁ : Pr{let u ← (query t : OracleComp spec (spec.Range t))}[CacheHasCollision
          (cache₀.cacheQuery t u)] ≤ (k : ℝ≥0∞) * C⁻¹ := by
        classical
        obtain ⟨S, hScard, hSmem⟩ := hbnd
        rw [prEvent_liftM_query_eq_card_div]
        have hbad_le_k :=
          (card_responses_creating_cacheCollision_le (t := t) hnocoll hSmem).trans hScard
        calc (↑(Finset.univ.filter (fun u => CacheHasCollision (cache₀.cacheQuery t u))).card :
                ℝ≥0∞) / ↑(Fintype.card (spec.Range t))
            ≤ (k : ℝ≥0∞) / ↑(Fintype.card (spec.Range t)) :=
              ENNReal.div_le_div_right (by exact_mod_cast hbad_le_k) _
          _ ≤ (k : ℝ≥0∞) * C⁻¹ := by
              rw [ENNReal.div_eq_inv_mul, mul_comm]
              gcongr
              change (Fintype.card (spec.Range default) : ℝ≥0∞) ≤ ↑(Fintype.card (spec.Range t))
              exact_mod_cast hrange t
      have hε₂ : ∀ u ∈ support (query t : OracleComp spec (spec.Range t)),
          ¬CacheHasCollision (cache₀.cacheQuery t u) →
          Pr{let z ← (simulateQ cachingOracle (mx u)).run
                 (cache₀.cacheQuery t u)}[CacheHasCollision z.2] ≤
              ∑ j ∈ range (m - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) * C⁻¹ := by
        intro u _ hnocoll'
        apply ih u (m - 1) (k + 1) (hrest u) _ hnocoll'
        obtain ⟨S, hScard, hSmem⟩ := hbnd
        exact ⟨insert t S,
          le_trans (Finset.card_insert_le t S) (by lia),
          fun t' ht' => by
            by_cases heq : t' = t
            · exact heq ▸ Finset.mem_insert_self _ S
            · rw [QueryCache.cacheQuery_of_ne cache₀ _ heq] at ht'
              exact Finset.mem_insert_of_mem (hSmem t' ht')⟩
      calc Pr{let z ← (query t : OracleComp spec (spec.Range t)) >>= fun u =>
              (simulateQ cachingOracle (mx u)).run
                (cache₀.cacheQuery t u)}[CacheHasCollision z.2]
          ≤ (k : ℝ≥0∞) * C⁻¹ + ∑ j ∈ range (m - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
            (prEvent_bind_le_prEvent_add_of_support _ _
              (fun u => CacheHasCollision (cache₀.cacheQuery t u)) _ hε₂).trans
              (add_le_add hε₁ le_rfl)
        _ = ∑ j ∈ range m, ((k + j : ℕ) : ℝ≥0∞) * C⁻¹ := by
            conv_rhs => rw [show m = (m - 1) + 1 from by lia]
            rw [Finset.sum_range_succ' (fun j => ((k + j : ℕ) : ℝ≥0∞) * C⁻¹)]
            simp only [Nat.add_zero]
            rw [add_comm, Finset.sum_congr rfl fun j _ => by
              rw [show k + 1 + j = k + (j + 1) from by lia]]

/-- **Tight birthday bound for `cachingOracle`** (total query bound):
The probability of a collision in the cache is ≤ n*(n-1)/(2|C|). -/
theorem prEvent_cacheCollision_le_birthday_total_tight {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr{let z ← (simulateQ cachingOracle oa).run ∅}[CacheHasCollision z.2] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  let C := (Fintype.card (spec.Range default) : ℝ≥0∞)
  calc Pr{let z ← (simulateQ cachingOracle oa).run ∅}[CacheHasCollision z.2]
      ≤ ∑ j ∈ range n, ((0 + j : ℕ) : ℝ≥0∞) * C⁻¹ :=
        prEvent_cacheCollision_run_le_sum_aux hrange oa n 0 hbound ∅
          (by intro ⟨t₁, _, _, _, _, h1, _, _⟩; simp at h1)
          ⟨∅, by simp, fun t ht => absurd (by simp : (∅ : QueryCache spec) t = none) ht⟩
    _ = ∑ j ∈ range n, (j : ℝ≥0∞) * C⁻¹ := by simp
    _ = ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * C) := ENNReal.gauss_sum_inv_eq n C

/-- **Loose birthday bound for `cachingOracle`** (total query bound):
The probability of a collision in the cache is ≤ n²/(2|C|).

A loose corollary of `prEvent_cacheCollision_le_birthday_total_tight`. -/
theorem prEvent_cacheCollision_le_birthday_total {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ)
    (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr{let z ← (simulateQ cachingOracle oa).run ∅}[CacheHasCollision z.2] ≤
      (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  calc Pr{let z ← (simulateQ cachingOracle oa).run ∅}[CacheHasCollision z.2]
      ≤ ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) :=
        prEvent_cacheCollision_le_birthday_total_tight oa n hbound hrange
    _ ≤ (n ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
        gcongr; exact_mod_cast (show n * (n - 1) ≤ n ^ 2 by rw [pow_two]; gcongr; lia)

/-! ## Per-Index Bound Versions -/

/-- Birthday bound for `cachingOracle` with per-index query bound. -/
theorem prEvent_cacheCollision_le_birthday {α : Type} {t : ℕ}
    [Inhabited ι] [Fintype ι]
    (oa : OracleComp spec α)
    (hbound : IsPerIndexQueryBound oa (fun _ => t))
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t)) :
    Pr{let z ← (simulateQ cachingOracle oa).run ∅}[CacheHasCollision z.2] ≤
      ((Fintype.card ι * t) ^ 2 : ℝ≥0∞) / (2 * Fintype.card (spec.Range default)) := by
  have htotal := IsTotalQueryBound.of_perIndex hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at htotal
  exact_mod_cast prEvent_cacheCollision_le_birthday_total oa _ htotal hrange

end cacheCollision

end OracleComp
