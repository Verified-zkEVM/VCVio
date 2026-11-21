/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Mixed

import all VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Mixed
import all VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.GraphCost
import all VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Presence

/-!
# Full public words outside a canonical graph

If neither half can name a graph point, a miss samples an independent full word.
A hit reuses the old word, including in the presence of pending internal graph work.
-/

public section

open OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery
namespace CanonicalGraph.PairedQueries

variable {L H F X K : Type} (G : CanonicalGraph (PairedSpec L H) X K H) (e : F ≃ H × H)
  [DecidableEq L] [DecidableEq X] [DecidableEq K] [SampleableType H]

/-- Neither tag is reachable as a canonical graph point at this physical input. -/
@[expose] def OrdinaryAt (b : L) : Prop :=
  ∀ st, ¬ Ready G st (.inl b) ∧ ¬ Ready G st (.inr b)

private theorem ordinary_row (row : L ⊕ L) (st : DeferredState L H X K)
    (off : ¬ Ready G st.1 row) :
    ((G.deferredImpl (.inl (.inl (.inr row)))).run st) =
      (fun z => (z.1, (z.2, st.1.2), st.2)) <$>
        (((PairedSpec L H).randomOracle row).run st.1.1) := by
  rw [G.deferredImpl_run_inl, G.relabelImpl_run_pub_of_not_exists off]
  simp [Functor.map_map]

/-- At a noncanonical input both full-word stages use the ordinary cache in order. -/
theorem ordinary_run (b : L) (off : OrdinaryAt G b) (st : DeferredState L H X K) :
    ((callerImpl G e (.inr b)).run st) = (do
      let low ← ((PairedSpec L H).randomOracle (.inl b)).run st.1.1
      let high ← ((PairedSpec L H).randomOracle (.inr b)).run low.2
      return (e.symm (low.1, high.1), (high.2, st.1.2), st.2)) := by
  simp only [callerImpl, QueryImpl.compose, RandomOraclePairedValue.readHalves, simulateQ_bind,
    simulateQ_pure, simulateQ_spec_query, liftPublic, simulateQ_HasQuery_query, StateT.run_bind,
    StateT.run_pure, ordinary_row G (.inl b) _ (off _).1, bind_map_left]
  apply bind_congr
  intro low
  rw [ordinary_row G (.inr b) _ (off _).2]
  simp only [bind_map_left]

/-- Record both halves without changing a graph label or the list of pending cells. -/
@[expose] def recordWord (b : L) (w : F) (st : DeferredState L H X K) : DeferredState L H X K :=
  (((st.1.1.cacheQuery (.inl b) (e w).1).cacheQuery (.inr b) (e w).2, st.1.2), st.2)

/-- On an ordinary cold query, the complete returned word is an independent fresh draw. -/
theorem ordinary_fresh [SampleableType F] (b : L) (off : OrdinaryAt G b)
    (st : DeferredState L H X K)
    (low : st.1.1 (.inl b) = none) (high : st.1.1 (.inr b) = none) :
    (fun w => (w, recordWord e b w st)) <$> ($ᵗ F) =ᵈ ((callerImpl G e (.inr b)).run st) := by
  rw [ordinary_run G e b off st]
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective).map
    (fun pair : H × H => (e.symm pair, recordWord e b (e.symm pair) st))
  simpa only [randomOracle.run_eq, low, high, QueryCache.cacheQuery_of_ne _ _ (Sum.inr_ne_inl),
    Functor.map_map, Function.comp_def, Equiv.symm_apply_apply,
    SampleableType.uniformSample_prod_eq_bind, map_bind, map_pure, bind_assoc, bind_map_left,
    pure_bind, bind_pure_comp, recordWord, Equiv.apply_symm_apply] using h

/-- A complete ordinary hit has no random effect and returns the existing word. -/
theorem ordinary_warm (b : L) (off : OrdinaryAt G b) (st : DeferredState L H X K) (w : F)
    (low : st.1.1 (.inl b) = some (e w).1) (high : st.1.1 (.inr b) = some (e w).2) :
    ((callerImpl G e (.inr b)).run st) = pure (w, st) := by
  rw [ordinary_run G e b off st]
  simp [low, high]

/-- Ordinary halves are present together at this input; other rows may be partial. -/
@[expose] def occupiedTogether (b : L) (s : DeferredState L H X K) : Prop :=
  (s.1.1 (.inl b)).isSome = (s.1.1 (.inr b)).isSome

/-- All mixed graph traffic preserves paired occupancy at an input outside the graph. -/
theorem ordinary_occupancy (b : L) (off : OrdinaryAt G b) :
    (QueryImpl.compose G.deferredImpl (expand e)).PreservesInv (occupiedTogether b) := by
  rintro ((u | a) | op) s prior z hz
  · simp only [QueryImpl.compose, expand, RandomOraclePairedValue.readHalves, simulateQ_spec_query,
      liftPublic, simulateQ_HasQuery_query, G.deferredImpl_run_inl,
      CanonicalGraph.relabelImpl_run_unif, Functor.map_map, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    exact prior
  · simp only [QueryImpl.compose, expand, RandomOraclePairedValue.readHalves, simulateQ_bind,
      simulateQ_pure, simulateQ_spec_query, liftPublic, simulateQ_HasQuery_query, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨lo, hl, hi, hh, rfl⟩ := hz
    unfold occupiedTogether at prior ⊢
    by_cases same : a = b
    · subst a
      rw [off_update G _ _ (off _).2 hh, QueryCache.cacheQuery_of_ne _ _ Sum.inl_ne_inr,
        off_update G _ _ (off _).1 hl]
      simp
    · have fl := public_frame G _ _ hl
      have fh := public_frame G _ _ hh
      rw [fh _ Sum.inl_ne_inr, fh _ (by simpa using Ne.symm same),
        fl _ (by simpa using Ne.symm same), fl _ Sum.inr_ne_inl]
      exact prior
  · change z ∈ support ((simulateQ G.deferredImpl (internalRead op)).run s) at hz
    simpa only [occupiedTogether, internal_frame G op s hz] using prior

/-- A cold-start stopped or completed mixed program cannot leave just one ordinary half. -/
theorem ordinary_run_occupancy {α : Type} (b : L) (off : OrdinaryAt G b)
    (p : OracleComp (Mixed L F X K H) α) (st : DeferredState L H X K)
    (prior : occupiedTogether b st) {z}
    (hz : z ∈ support ((simulateQ G.deferredImpl (simulateQ (expand e) p)).run st)) :
    occupiedTogether b z.2 := by
  rw [← QueryImpl.simulateQ_compose] at hz
  exact simulateQ_run_preservesInv _ _ (ordinary_occupancy G e b off) p st prior z hz

end CanonicalGraph.PairedQueries
