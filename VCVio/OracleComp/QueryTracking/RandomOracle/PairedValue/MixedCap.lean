/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Mixed
public import VCVio.OracleComp.QueryTracking.WeightedCap.Resource
import all VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Mixed

/-!
# Physical inputs under an operational cutoff on mixed graph queries

The cutoff charges one original full request before splitting it into its low and high halves.
Free internal graph operations may create pending touches on paths ending in refusal.
-/

public section
open OracleComp OracleSpec
namespace CanonicalGraph.PairedQueries

variable {L H F X K : Type} (G : CanonicalGraph (PairedSpec L H) X K H) (e : F ≃ H × H)
  [DecidableEq L] [DecidableEq X] [DecidableEq K] [SampleableType H]

/-- An operational cutoff before the full-word expansion bounds every physical footprint,
including refusals with nonempty lists of deferred touches.
Internal reads and touches are free unless the caller assigns them a charge. -/
theorem capped_footprint {α : Type} (cost : (Internal X K H).Domain → Nat)
    (body : OracleComp (Mixed L F X K H) α) (limit : Nat) (s : DeferredState L H X K) {z}
    (hz : z ∈ support ((simulateQ G.deferredImpl
      (simulateQ (expand e) (WeightedCap.capCompOpt
        (mixedCost (F := F) cost) limit body))).run s)) :
    (physicalInputs z.2.1.1).encard ≤ (physicalInputs s.1.1).encard + limit := by
  rw [← QueryImpl.simulateQ_compose] at hz
  apply WeightedCap.resource_le _ _ (fun q => (physicalInputs q.1.1).encard) _ body limit s hz
  rintro (t | t) st w h
  · exact caller_step_cost G e t st h
  · simp only [physicalInputs, internal_frame G t st h]
    exact le_self_add

/-- The same stopped computation keeps the occupancy invariant even after free lazy touches. -/
theorem capped_present {α : Type} (cost : (Internal X K H).Domain → Nat)
    (body : OracleComp (Mixed L F X K H) α) (limit : Nat) (s : DeferredState L H X K)
    (present : PresentTogether s) (paired : ∀ st b, Ready G st (.inl b) → Ready G st (.inr b)) {z}
    (hz : z ∈ support ((simulateQ G.deferredImpl
      (simulateQ (expand e) (WeightedCap.capCompOpt
        (mixedCost (F := F) cost) limit body))).run s)) :
    PresentTogether z.2 := by
  rw [← QueryImpl.simulateQ_compose] at hz
  refine simulateQ_run_preservesInv _ _ ?_ _ s present _ hz
  rintro (t | t) st ok w h
  · exact caller_preserves_presence G e paired t st ok w h
  · simpa only [PresentTogether, internal_frame G t st h] using ok

end CanonicalGraph.PairedQueries
