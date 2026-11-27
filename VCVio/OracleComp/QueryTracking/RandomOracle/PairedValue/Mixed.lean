/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Presence
import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.Cost

/-!
# Public and internal queries in one adaptive caller

A full public query can enlarge the ordinary cache at one physical input.
Private cell derivation, a lazy touch and a node read change only the graph's internal state.
Interleaving those operations therefore preserves the bound on the public cache footprint.
-/

public section

open OracleComp OracleSpec
namespace CanonicalGraph.PairedQueries

/-- Internal calls derive a private word, touch a cell or read its node. -/
abbrev Internal (X K H : Type) := (X →ₒ H) + labelOps X K H

/-- A caller can interleave full public queries with the internal operations of the graph. -/
abbrev Mixed (L F X K H : Type) := FullWorld L F + Internal X K H

variable {L H F X K : Type} (G : CanonicalGraph (PairedSpec L H) X K H) (e : F ≃ H × H)
  [DecidableEq L] [DecidableEq X] [DecidableEq K] [SampleableType H]

/-- Forward the three internal requests to the graph interpreter. -/
@[expose] def internalRead :
    QueryImpl (Internal X K H) (OracleComp ((PairedSpec L H).withLabels X K H)) :=
  Sum.rec (fun x => query (spec := (PairedSpec L H).withLabels X K H) (.inl (.inr x)))
    (fun op => query (spec := (PairedSpec L H).withLabels X K H) (.inr op))

/-- Expand each public word into its two rows and forward each internal request. -/
@[expose] def expand :
    QueryImpl (Mixed L F X K H) (OracleComp ((PairedSpec L H).withLabels X K H)) :=
  Sum.rec (fun t => simulateQ liftPublic (RandomOraclePairedValue.readHalves e t))
    (fun t => internalRead t)

/-- Charge each physical public query once and internal requests at their given rate. -/
abbrev mixedCost (internalCost : (Internal X K H).Domain → Nat) :
    (Mixed L F X K H).Domain → Nat := Sum.elim rawCost internalCost

/-- Internal work may carry any nonnegative physical charge assigned to it by the calling scheme. -/
@[expose] def runMixed {α : Type} (internalCost : (Internal X K H).Domain → Nat)
    (body : OracleComp (Mixed L F X K H) α) :
    OracleComp ((PairedSpec L H).withLabels X K H) (α × Nat) :=
  simulateQ (expand e)
    (simulateQ ((QueryImpl.id' _).withAddCost (mixedCost internalCost)) body).runAdd

private theorem internal_frame (t : (Internal X K H).Domain) (s : DeferredState L H X K)
    {z} (hz : z ∈ support ((simulateQ G.deferredImpl (internalRead t)).run s)) :
    z.2.1.1 = s.1.1 := by
  rcases t with x | c | k
  · simp only [internalRead, simulateQ_HasQuery_query, G.deferredImpl_run_inl,
      G.relabelImpl_apply_inr, RelabelState.drawCell_run, Functor.map_map, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    rfl
  · simp only [internalRead, simulateQ_HasQuery_query, G.deferredImpl_run_touch,
      mem_support_pure_iff] at hz
    cases hz
    rfl
  · simp only [internalRead, simulateQ_HasQuery_query, G.deferredImpl_run_read,
      RelabelState.drawCell_run, Functor.map_map, support_map] at hz
    obtain ⟨_, _, rfl⟩ := hz
    rfl

/-- On every adaptive run only charged full queries can enlarge the ordinary physical cache. -/
theorem mixed_footprint {α : Type} (internalCost : (Internal X K H).Domain → Nat)
    (body : OracleComp (Mixed L F X K H) α) (s : DeferredState L H X K) (z)
    (hz : z ∈ support ((simulateQ G.deferredImpl (runMixed e internalCost body)).run s)) :
    (physicalInputs z.2.1.1).encard ≤ (physicalInputs s.1.1).encard + z.1.2 := by
  unfold runMixed at hz
  rw [← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_withAddCost_runAdd_fusion] at hz
  apply QueryImpl.resource_le_runAdd _ (fun q => (physicalInputs q.1.1).encard) _ _ body s z hz
  rintro (t | t) st w h
  · exact caller_step_cost G e t st h
  · have eqn := internal_frame G t st h
    simp [eqn]

/-- Under the paired readiness hypothesis, every occupied high row still has an occupied low row
after an adaptive mixed run. -/
theorem mixed_present {α : Type} (internalCost : (Internal X K H).Domain → Nat)
    (body : OracleComp (Mixed L F X K H) α) (s : DeferredState L H X K) (inv : PresentTogether s)
    (paired : ∀ st b, Ready G st (.inl b) → Ready G st (.inr b)) (z)
    (hz : z ∈ support ((simulateQ G.deferredImpl (runMixed e internalCost body)).run s)) :
    PresentTogether z.2 := by
  unfold runMixed at hz
  rw [← QueryImpl.simulateQ_compose] at hz
  refine simulateQ_run_preservesInv _ _ ?_ _ s inv _ hz
  rintro (t | t) st ok w h
  · exact caller_preserves_presence G e paired t st ok w h
  · simpa only [PresentTogether, internal_frame G t st h] using ok

end CanonicalGraph.PairedQueries
