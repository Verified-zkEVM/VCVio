/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Adaptive programs over paired cache rows

Private randomness passes through unchanged.
Each public query reads both rows and returns the reconstructed full answer.
-/

public section

open OracleComp OracleSpec
open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.RandomOraclePairedValue

variable {L Full Half : Type} (e : Full ≃ Half × Half)

/-- A populated cache row supplies both halves of its full value. -/
@[expose] def splitCache (cache : (L →ₒ Full).QueryCache) : ((L ⊕ L) →ₒ Half).QueryCache :=
  QueryCache.ofFn (Sum.elim
    (fun key => (cache key).map (fun word => (e word).1))
    (fun key => (cache key).map (fun word => (e word).2)))

/-- Two populated rows recover the full cached value. -/
@[expose] def joinCache (cache : ((L ⊕ L) →ₒ Half).QueryCache) : (L →ₒ Full).QueryCache :=
  QueryCache.ofFn fun key => do
    let left ← cache (.inl key)
    let right ← cache (.inr key)
    pure (e.symm (left, right))

/-- Splitting and reading back keeps every original row. -/
theorem joinCache_splitCache (cache : (L →ₒ Full).QueryCache) :
    joinCache e (splitCache e cache) = cache := by
  ext key
  cases h : cache key <;> simp [joinCache, splitCache, h]

/-- Joining a full word requires both projections at the same key. -/
theorem joinCache_eq_some_iff (cache : ((L ⊕ L) →ₒ Half).QueryCache) (key : L) (word : Full) :
    joinCache e cache key = some word ↔
      cache (.inl key) = some (e word).1 ∧ cache (.inr key) = some (e word).2 := by
  constructor
  · intro h
    change ((cache (.inl key)).bind fun l =>
      (cache (.inr key)).bind fun r => some (e.symm (l, r))) = some word at h
    obtain ⟨l, left, rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, right, pair⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj pair
    simpa only [Equiv.apply_symm_apply] using And.intro left right
  · rintro ⟨left, right⟩
    simp [joinCache, left, right]

/-- Splitting is left adjoint to joining for the partial order of cache extension.
The half cache may contain rows whose other half has not been drawn. -/
theorem gc_splitCache_joinCache :
    GaloisConnection (splitCache (L := L) e) (joinCache e) := by
  intro words rows
  constructor
  · intro both key word stored
    apply (joinCache_eq_some_iff e rows key word).2
    exact ⟨both (by simp [splitCache, stored]), both (by simp [splitCache, stored])⟩
  · intro represented q value stored
    cases q with
    | inl key =>
      obtain ⟨word, present, rfl⟩ := Option.map_eq_some_iff.mp stored
      exact ((joinCache_eq_some_iff e rows key word).1 (represented present)).1
    | inr key =>
      obtain ⟨word, present, rfl⟩ := Option.map_eq_some_iff.mp stored
      exact ((joinCache_eq_some_iff e rows key word).1 (represented present)).2

/-- Private draws are forwarded and public replies are reconstructed after both reads. -/
@[expose] def readHalves :
    QueryImpl (unifSpec + (L →ₒ Full)) (OracleComp (unifSpec + ((L ⊕ L) →ₒ Half))) :=
  Sum.rec (fun n => liftM ((unifSpec + ((L ⊕ L) →ₒ Half)).query (.inl n))) fun key => do
    let left ← liftM ((unifSpec + ((L ⊕ L) →ₒ Half)).query (.inr (.inl key)))
    let right ← liftM ((unifSpec + ((L ⊕ L) →ₒ Half)).query (.inr (.inr key)))
    pure (e.symm (left, right))

variable [DecidableEq L] [SampleableType Full] [SampleableType Half]

/-- Read one full cached word through two coherently cached projections. -/
theorem run_pair_macro_evalDistEq_full_joint
    (label : L)
    (initial : (L →ₒ Full).QueryCache) :
    (fun z : Full × (L →ₒ Full).QueryCache => (z.1, z.2, splitCache e z.2)) <$>
        ((L →ₒ Full).randomOracle label).run initial =ᵈ
      (fun z : Full × ((L ⊕ L) →ₒ Half).QueryCache =>
        (z.1, joinCache e z.2, z.2)) <$>
        (simulateQ ((L ⊕ L) →ₒ Half).randomOracle (do
          let left ← liftM (((L ⊕ L) →ₒ Half).query (.inl label))
          let right ← liftM (((L ⊕ L) →ₒ Half).query (.inr label))
          pure (e.symm (left, right)))).run (splitCache e initial) := by
  have image_update (cache : (L →ₒ Full).QueryCache) (word : Full) :
      splitCache e (cache.cacheQuery label word) =
        ((splitCache e cache).cacheQuery (.inl label) (e word).1).cacheQuery
          (.inr label) (e word).2 := by
    apply QueryCache.ext
    rintro (key | key)
    · have cross : (Sum.inl key : L ⊕ L) ≠ .inr label := by simp
      rw [QueryCache.cacheQuery_of_ne _ _ cross]
      by_cases h : key = label
      · subst key
        simp only [splitCache, QueryCache.ofFn_apply, Sum.elim_inl,
          QueryCache.cacheQuery_self, Option.map_some]
      · have different : (Sum.inl key : L ⊕ L) ≠ .inl label := by simpa using h
        rw [QueryCache.cacheQuery_of_ne _ _ different]
        simp only [splitCache, QueryCache.ofFn_apply, Sum.elim_inl,
          QueryCache.cacheQuery_of_ne _ _ h]
    · by_cases h : key = label
      · subst key
        simp only [splitCache, QueryCache.ofFn_apply, Sum.elim_inr,
          QueryCache.cacheQuery_self, Option.map_some]
      · have different : (Sum.inr key : L ⊕ L) ≠ .inr label := by simpa using h
        have cross : (Sum.inr key : L ⊕ L) ≠ .inl label := by simp
        rw [QueryCache.cacheQuery_of_ne _ _ different, QueryCache.cacheQuery_of_ne _ _ cross]
        simp only [splitCache, QueryCache.ofFn_apply, Sum.elim_inr,
          QueryCache.cacheQuery_of_ne _ _ h]
  -- The two cache rows are filled together before any original continuation resumes.
  have run_macro :
      (simulateQ ((L ⊕ L) →ₒ Half).randomOracle (do
        let left ← liftM (((L ⊕ L) →ₒ Half).query (.inl label))
        let right ← liftM (((L ⊕ L) →ₒ Half).query (.inr label))
        pure (e.symm (left, right)))).run (splitCache e initial) =
      (match initial label with
      | some word => pure (word, splitCache e initial)
      | none => do
        let left ← ($ᵗ Half : ProbComp Half)
        let right ← ($ᵗ Half : ProbComp Half)
        let word := e.symm (left, right)
        pure (word, splitCache e (initial.cacheQuery label word))) := by
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      StateT.run_bind, StateT.run_pure]
    cases hc : initial label with
    | some word =>
      have hl : splitCache e initial (.inl label) = some (e word).1 := by simp [splitCache, hc]
      have hr : splitCache e initial (.inr label) = some (e word).2 := by simp [splitCache, hc]
      simp only [randomOracle.run_eq, hl, hr, pure_bind]
      change pure (e.symm (e word), splitCache e initial) = _
      rw [e.symm_apply_apply]
    | none =>
      have hl : splitCache e initial (.inl label) = none := by simp [splitCache, hc]
      simp only [randomOracle.run_eq, hl, bind_assoc, pure_bind]
      apply bind_congr
      intro left
      have hr : ((splitCache e initial).cacheQuery (.inl label) left) (.inr label) = none := by
        simp [splitCache, hc]
      rw [hr]
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro right
      congr 1
      rw [image_update]
      simp
  rw [run_macro]
  cases hc : initial label with
  | some word =>
    simp only [randomOracle.run_eq, hc, map_pure, joinCache_splitCache]
    exact EvalDistEq.refl _
  | none =>
    -- Transport the single full draw to a product draw, then expose its two coordinates.
    have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective).map
      (fun pair : Half × Half =>
        (e.symm pair, initial.cacheQuery label (e.symm pair),
          splitCache e (initial.cacheQuery label (e.symm pair))))
    simpa only [randomOracle.run_eq, hc, Functor.map_map, Function.comp_def,
      Equiv.symm_apply_apply, SampleableType.uniformSample_prod_eq_bind,
      map_bind, map_pure, bind_pure_comp, joinCache_splitCache] using h

/-- The public cache is represented by its two rows throughout one world step. -/
private theorem world_step
    (input : (unifSpec + (L →ₒ Full)).Domain) (cache : (L →ₒ Full).QueryCache) :
    (simulateQ ((L ⊕ L) →ₒ Half).romImpl
      (readHalves e input)).run (splitCache e cache) =ᵈ
    Prod.map id (splitCache e) <$>
      ((L →ₒ Full).romImpl input).run cache := by
  cases input with
  | inl n =>
    simp only [readHalves, OracleSpec.romImpl, simulateQ_spec_query, roSim.run_apply_inl]
    simp [Functor.map_map, Prod.map]
  | inr key =>
    have h := (run_pair_macro_evalDistEq_full_joint e key cache).symm.map
      (fun z : Full × (L →ₒ Full).QueryCache × ((L ⊕ L) →ₒ Half).QueryCache => (z.1, z.2.2))
    have hmap : (Prod.map id (splitCache e) : Full × (L →ₒ Full).QueryCache → _) =
        (fun value => (value.1, splitCache e value.2)) := by
      funext value
      cases value
      rfl
    change _ =ᵈ (Prod.map (@id Full) (splitCache e)) <$> ((L →ₒ Full).randomOracle key).run cache
    rw [hmap]
    simp only [Functor.map_map, Prod.mk.eta, id_map',
      simulateQ_bind, simulateQ_pure, simulateQ_spec_query] at h
    simp only [readHalves, OracleSpec.romImpl, simulateQ_bind, simulateQ_pure, simulateQ_spec_query,
      QueryImpl.add_apply_inr, splitCache]
    exact h

/-- The reply of an adaptive program and both forms of its final cache have the same joint law. -/
theorem evalDist_world_run_joint {α : Type}
    (program : OracleComp (unifSpec + (L →ₒ Full)) α) (initial : (L →ₒ Full).QueryCache) :
    (fun z : α × (L →ₒ Full).QueryCache => (z.1, z.2, splitCache e z.2)) <$>
      (simulateQ (L →ₒ Full).romImpl program).run initial =ᵈ
    (fun z : α × ((L ⊕ L) →ₒ Half).QueryCache => (z.1, joinCache e z.2, z.2)) <$>
      (simulateQ ((L ⊕ L) →ₒ Half).romImpl
        (simulateQ (readHalves e) program)).run (splitCache e initial) := by
  have h := evalDistEq_map_run_simulateQ_eq_of_query_evalDistEq_map_eq
    (L →ₒ Full).romImpl
    (QueryImpl.compose ((L ⊕ L) →ₒ Half).romImpl
      (readHalves e))
    (splitCache e) (fun key cache => (world_step e key cache).symm) program initial
  have joint := h.map (fun z => (z.1, joinCache e z.2, z.2))
  simpa only [QueryImpl.simulateQ_compose, Functor.map_map, Function.comp_def, Prod.map,
    id_eq, joinCache_splitCache] using joint

end OracleComp.RandomOraclePairedValue
