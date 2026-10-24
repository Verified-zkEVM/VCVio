/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.CommitmentScheme.Hiding.Defs
public import VCVio.ProgramLogic.Library

/-!
# Specifications for the commitment hiding handlers

Specifications for the four handlers of `Examples.CommitmentScheme.Hiding.Defs` under the
necessary reading of `OracleComp` (`open scoped OracleComp.Necessary`): the real handler
`hidingImpl₁ s`, the bridge `hidingImpl₂ s`, the simulator `hidingImplSim s` (all caching
oracles with a miss counter at salt `s`), and the per-salt counter `hidingImplCountAll`.

* *Support.* The redirect of `hidingImpl₂` and `hidingImplSim` queries the underlying oracle at
  another point, whose support is the same, so the three counted handlers share one support
  description: a hit keeps the state; a miss caches any answer and counts it if its salt is `s`
  (`mem_support_hidingImpl₁_run_iff` and its two siblings, in `simulateQ_nf`).
* *One query.* `*_wp` (`spec high`) are exact and have one branch: they quantify over the answer
  and final state that the support description allows.
* *Whole runs.* All four only grow their cache and their counters: `QueryImpl.MonotoneState` for
  the product order, so `vcgen` frames an opaque adversary, and `MonotoneState.rel_of_mem_support`
  reads off that a run's cache and counters only grow.
* *Relations.* A counted handler with its counter dropped is `cachingOracle`
  (`map_run_simulateQ_hidingImpl₁_eq_cachingOracle`), and every reachable real step caches its
  answer (`hidingImpl₁_cache_self`).
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

variable {M S C : Type} [DecidableEq M] [DecidableEq S]

local notation "HState" => QueryCache (CMOracle M S C) × ℕ

section counted

variable (s : S)

/-- A reachable real hiding step is a hit, or a miss caching any answer and counting salt `s`. -/
@[simulateQ_nf]
theorem mem_support_hidingImpl₁_run_iff {ms : M × S} {st st' : HState} {u : C} :
    (u, st') ∈ support ((hidingImpl₁ s ms).run st) ↔ (st.1 ms = some u ∧ st' = st) ∨
      (st.1 ms = none ∧ st' = (st.1.cacheQuery ms u, if ms.2 = s then st.2 + 1 else st.2)) := by
  obtain ⟨cache, cnt⟩ := st
  cases h : cache ms <;> simp [hidingImpl₁, h, StateT.run_bind, StateT.run_get, StateT.run_set,
    StateT.run_monadLift] <;> aesop

/-- A reachable simulator step has the same description: the redirected query has full support. -/
@[simulateQ_nf]
theorem mem_support_hidingImplSim_run_iff [Inhabited M] [Inhabited S] {ms : M × S}
    {st st' : HState} {u : C} :
    (u, st') ∈ support ((hidingImplSim s ms).run st) ↔ (st.1 ms = some u ∧ st' = st) ∨
      (st.1 ms = none ∧ st' = (st.1.cacheQuery ms u, if ms.2 = s then st.2 + 1 else st.2)) := by
  obtain ⟨cache, cnt⟩ := st
  cases h : cache ms <;> simp [hidingImplSim, h, StateT.run_bind, StateT.run_get,
    StateT.run_set, StateT.run_monadLift] <;> aesop

/-- A reachable bridge step has the same description as a real step. -/
@[simulateQ_nf]
theorem mem_support_hidingImpl₂_run_iff [Inhabited M] [Inhabited S] {ms : M × S}
    {st st' : HState} {u : C} :
    (u, st') ∈ support ((hidingImpl₂ s ms).run st) ↔ (st.1 ms = some u ∧ st' = st) ∨
      (st.1 ms = none ∧ st' = (st.1.cacheQuery ms u, if ms.2 = s then st.2 + 1 else st.2)) := by
  obtain ⟨cache, cnt⟩ := st
  cases h : cache ms <;> simp [hidingImpl₂, h, StateT.run_bind, StateT.run_get,
    StateT.run_set, StateT.run_monadLift] <;> aesop

/-- One real hiding query, exactly: the stored answer on a hit, any answer on a miss, cached and
counted at salt `s`. -/
@[spec high]
theorem hidingImpl₁_wp (ms : M × S) (post : C → HState → Prop) {epost : EStack⟨⟩} :
    ⦃ fun st => ∀ u st', ((st.1 ms = some u ∧ st' = st) ∨ (st.1 ms = none ∧
        st' = (st.1.cacheQuery ms u, if ms.2 = s then st.2 + 1 else st.2))) → post u st' ⦄
      hidingImpl₁ s ms ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u st' hz =>
    h u st' ((mem_support_hidingImpl₁_run_iff s).1 hz)

/-- One simulator query, exactly; the same rule as `hidingImpl₁_wp`. -/
@[spec high]
theorem hidingImplSim_wp [Inhabited M] [Inhabited S] (ms : M × S) (post : C → HState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun st => ∀ u st', ((st.1 ms = some u ∧ st' = st) ∨ (st.1 ms = none ∧
        st' = (st.1.cacheQuery ms u, if ms.2 = s then st.2 + 1 else st.2))) → post u st' ⦄
      hidingImplSim s ms ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u st' hz =>
    h u st' ((mem_support_hidingImplSim_run_iff s).1 hz)

/-- One bridge query, exactly; the same rule as `hidingImpl₁_wp`. -/
@[spec high]
theorem hidingImpl₂_wp [Inhabited M] [Inhabited S] (ms : M × S) (post : C → HState → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun st => ∀ u st', ((st.1 ms = some u ∧ st' = st) ∨ (st.1 ms = none ∧
        st' = (st.1.cacheQuery ms u, if ms.2 = s then st.2 + 1 else st.2))) → post u st' ⦄
      hidingImpl₂ s ms ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u st' hz =>
    h u st' ((mem_support_hidingImpl₂_run_iff s).1 hz)

/-- A counted caching step only grows its cache and its counter. -/
private theorem le_of_counted_step {ms : M × S} {st st' : HState} {u : C}
    (h : (st.1 ms = some u ∧ st' = st) ∨
      (st.1 ms = none ∧ st' = (st.1.cacheQuery ms u, if ms.2 = s then st.2 + 1 else st.2))) :
    st ≤ st' := by
  rcases h with ⟨-, rfl⟩ | ⟨hc, rfl⟩
  · exact le_rfl
  · refine ⟨QueryCache.le_cacheQuery _ hc, ?_⟩
    dsimp only; split_ifs <;> omega

/-- The real hiding handler only grows its cache and its counter. -/
instance monotoneState_hidingImpl₁ : (hidingImpl₁ (M := M) (C := C) s).MonotoneState (· ≤ ·) :=
  .of_le fun _ _ ⟨_, _⟩ hz => le_of_counted_step s ((mem_support_hidingImpl₁_run_iff s).1 hz)

/-- The simulator only grows its cache and its counter. -/
instance monotoneState_hidingImplSim [Inhabited M] [Inhabited S] :
    (hidingImplSim (M := M) (C := C) s).MonotoneState (· ≤ ·) :=
  .of_le fun _ _ ⟨_, _⟩ hz => le_of_counted_step s ((mem_support_hidingImplSim_run_iff s).1 hz)

/-- The bridge only grows its cache and its counter. -/
instance monotoneState_hidingImpl₂ [Inhabited M] [Inhabited S] :
    (hidingImpl₂ (M := M) (C := C) s).MonotoneState (· ≤ ·) :=
  .of_le fun _ _ ⟨_, _⟩ hz => le_of_counted_step s ((mem_support_hidingImpl₂_run_iff s).1 hz)

/-- A reachable real hiding step caches its answer at the queried point. -/
theorem hidingImpl₁_cache_self {ms : M × S} {st : HState} {z : C × HState}
    (hz : z ∈ support ((hidingImpl₁ s ms).run st)) : z.2.1 ms = some z.1 := by
  obtain ⟨u, st'⟩ := z
  rcases (mem_support_hidingImpl₁_run_iff s).1 hz with ⟨h, rfl⟩ | ⟨-, rfl⟩
  exacts [h, QueryCache.cacheQuery_self _ _ _]

/-- Dropping the counter of a real hiding step gives a `cachingOracle` step. -/
theorem hidingImpl₁_proj_eq_cachingOracle (ms : M × S) (st : HState) :
    Prod.map id Prod.fst <$> (hidingImpl₁ s ms).run st =
      ((CMOracle M S C).cachingOracle ms).run st.1 := by
  rw [← hidingImplCountAll_proj_eq_cachingOracle ms (st.1, fun _ => st.2),
    ← congrArg (Prod.map id Prod.fst <$> ·)
      (hidingImplCountAll_proj_eq_hidingImpl₁ s ms (st.1, fun _ => st.2)), Functor.map_map]
  rfl

/-- Dropping the counter of a real hiding run gives a `cachingOracle` run. -/
theorem map_run_simulateQ_hidingImpl₁_eq_cachingOracle {α : Type}
    (oa : OracleComp (CMOracle M S C) α) (st : HState) :
    Prod.map id Prod.fst <$> (simulateQ (hidingImpl₁ s) oa).run st =
      (simulateQ cachingOracle oa).run st.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (hidingImpl₁_proj_eq_cachingOracle s) oa st

end counted

/-! ## The per-salt counter `hidingImplCountAll` -/

/-- A reachable per-salt counted step is a hit, or a miss caching any answer and counting its
salt. -/
@[simulateQ_nf]
theorem mem_support_hidingImplCountAll_run_iff {ms : M × S}
    {st st' : QueryCache (CMOracle M S C) × (S → ℕ)} {u : C} :
    (u, st') ∈ support ((hidingImplCountAll ms).run st) ↔ (st.1 ms = some u ∧ st' = st) ∨
      (st.1 ms = none ∧
        st' = (st.1.cacheQuery ms u, Function.update st.2 ms.2 (st.2 ms.2 + 1))) := by
  obtain ⟨cache, cnt⟩ := st
  cases h : cache ms <;> simp [hidingImplCountAll, h, StateT.run_bind, StateT.run_get,
    StateT.run_set, StateT.run_monadLift] <;> aesop

/-- One per-salt counted query, exactly. -/
@[spec high]
theorem hidingImplCountAll_wp (ms : M × S)
    (post : C → QueryCache (CMOracle M S C) × (S → ℕ) → Prop) {epost : EStack⟨⟩} :
    ⦃ fun st => ∀ u st', ((st.1 ms = some u ∧ st' = st) ∨ (st.1 ms = none ∧
        st' = (st.1.cacheQuery ms u, Function.update st.2 ms.2 (st.2 ms.2 + 1)))) → post u st' ⦄
      hidingImplCountAll ms ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun _ h u st' hz =>
    h u st' (mem_support_hidingImplCountAll_run_iff.1 hz)

/-- The per-salt counted handler only grows its cache and every counter. -/
instance monotoneState_hidingImplCountAll :
    (hidingImplCountAll (M := M) (S := S) (C := C)).MonotoneState (· ≤ ·) :=
  .of_le fun ms _ ⟨_, _⟩ hz => by
    rcases mem_support_hidingImplCountAll_run_iff.1 hz with ⟨-, rfl⟩ | ⟨hc, rfl⟩
    · exact le_rfl
    · refine ⟨QueryCache.le_cacheQuery _ hc, fun s' => ?_⟩
      rcases eq_or_ne s' ms.2 with rfl | h <;> simp [*]
