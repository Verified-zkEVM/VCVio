/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Completeness
public import VCVio.OracleComp.CanReturn
public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQueryInfinite

/-!
# Completeness of vector commitments in the random oracle model

Completeness (`VectorCommitment.PerfectlyCompleteForAll`) is stated against every fixed oracle
function, while position binding and hiding are stated against the lazily sampled random oracle
`ProbCompRuntime.rom (X →ₒ Y)`. This file transfers completeness to that oracle, so that a scheme's
completeness and its security are stated in the same model.

Every realized lazy execution also arises in an execution against a fixed table
(`OracleComp.mem_support_fixedTableLoggedRun_of_randomOracle`), and caching a fixed table answers
every query with the table's value. So every output of the honest experiment under the lazy oracle
is an output against some fixed function, where it is accepted.

## Main results

* `VectorCommitment.mem_support_fixedOracleImpl_of_mem_support_fixedTableLoggedRun`: an output of
  a cached fixed-table execution, from a cache that agrees with the table, is an output of the
  same computation against the table as a fixed function.
* `VectorCommitment.PerfectlyCompleteForAll.evalDist_rom_completenessExp`: completeness against
  every fixed function gives acceptance with probability one under the lazily sampled random
  oracle.
-/

public section

open OracleComp OracleSpec MeasureTheory

universe uM

namespace VectorCommitment

variable {X Y : Type} [DecidableEq X]

/-- An output of a cached execution against the fixed table `g`, started from a cache that agrees
with `g`, is an output of the same computation with every oracle query answered by `g`. -/
theorem mem_support_fixedOracleImpl_of_mem_support_fixedTableLoggedRun {α : Type}
    (oa : OracleComp (unifSpec + (X →ₒ Y)) α) (g : X → Y) (cache : (X →ₒ Y).QueryCache)
    (hcache : ∀ t v, cache t = some v → v = g t)
    (z : (α × QueryLog (X →ₒ Y)) × (X →ₒ Y).QueryCache)
    (hz : z ∈ support (fixedTableLoggedRun oa g cache)) :
    z.1.1 ∈ support (simulateQ (fixedOracleImpl g) oa) := by
  induction oa using OracleComp.inductionOn generalizing cache z with
  | pure a =>
    simp only [fixedTableLoggedRun, QueryImpl.passthrough_add, simulateQ_pure, WriterT.run_pure,
      List.empty_eq, StateT.run_pure, MonadAttach.support_pure, Set.mem_singleton_iff] at hz
    simp [hz]
  | query_bind t k ih =>
    rw [fixedTableLoggedRun_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [support_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    rw [simulateQ_bind, mem_support_bind_iff]
    cases t with
    | inl n =>
      rw [fixedTableLoggedRun_uniformQuery] at hp
      simp only [add_apply_inl, HasQuery.toQueryImpl_apply, HasQuery.instOfMonadLift_query,
        MonadAttach.support_map, support_liftM, OracleQuery.input_query, OracleQuery.cont_query,
        Set.range_id, Set.image_univ, Set.mem_range] at hp
      obtain ⟨y, rfl⟩ := hp
      refine ⟨y, ?_, ih y cache hcache q hq⟩
      simp only [fixedOracleImpl, simulateQ_query]
      exact OracleComp.mem_support_query (spec := unifSpec) n y
    | inr x =>
      rw [fixedTableLoggedRun_hashQuery] at hp
      refine ⟨g x, ?_, ?_⟩
      · simp only [fixedOracleImpl, simulateQ_query]
        exact (MonadAttach.canReturn_pure_iff (m := ProbComp)).mpr rfl
      rcases hcx : cache.toFn x with _ | u
      · simp only [add_apply_inr, QueryImpl.withCaching_apply, PFunctor.Handler.liftTarget_apply,
          ofPFunctor_toPFunctor, QueryImpl.ofFn_apply, StateT.run_bind, StateT.run_get, pure_bind,
          hcx, StateT.run_monadLift, monadLift_self, bind_pure_comp, StateT.run_modifyGet,
          Functor.map_map, MonadAttach.support_map, Set.mem_image, MonadAttach.mem_support] at hp
        obtain ⟨y, hy, rfl⟩ := hp
        rw [OracleComp.canReturn_iff_mem_support] at hy
        simp only [MonadAttach.mem_support] at hy
        subst hy
        refine ih _ _ ?_ q hq
        intro t v hv
        by_cases htx : t = x
        · subst htx
          simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hv
          exact hv.symm
        · simp only [ne_eq, htx, not_false_eq_true, QueryCache.cacheQuery_of_ne] at hv
          exact hcache t v hv
      · simp only [add_apply_inr, QueryImpl.withCaching_apply, PFunctor.Handler.liftTarget_apply,
          ofPFunctor_toPFunctor, QueryImpl.ofFn_apply, StateT.run_bind, StateT.run_get, pure_bind,
          hcx, StateT.run_pure, map_pure, MonadAttach.support_pure, Set.mem_singleton_iff] at hp
        subst hp
        obtain rfl : u = g x := hcache x u hcx
        exact ih _ cache hcache q hq

/-- **Completeness in the random oracle model.** A scheme that is complete against every fixed
function accepts the honest opening of every message and query set with probability one under the
lazily sampled random oracle. -/
theorem PerfectlyCompleteForAll.evalDist_rom_completenessExp [SampleableType Y]
    {Msg : Type uM} {Cm Td Pf : Type} {ℓ : ℕ} {vc : VectorCommitment X Y Msg Cm Td Pf ℓ}
    (h : vc.PerfectlyCompleteForAll) (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)) :
    (ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.completenessExp m Q) {true} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton, prEvent_eq_one_iff]
  intro b hb
  rw [StateT.run'_eq, support_map] at hb
  obtain ⟨⟨b', s⟩, hbs, rfl⟩ := hb
  rw [← randomOracleLoggedRun_project, support_map] at hbs
  obtain ⟨z, hz, hzeq⟩ := hbs
  obtain ⟨g, hg⟩ := mem_support_fixedTableLoggedRun_of_randomOracle _ ∅ z hz
  have hfix := mem_support_fixedOracleImpl_of_mem_support_fixedTableLoggedRun _ g ∅ (by simp) z hg
  rw [show z.1.1 = b' from congrArg Prod.fst hzeq] at hfix
  exact h g m Q b' hfix

end VectorCommitment
