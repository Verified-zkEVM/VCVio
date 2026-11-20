/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.GraphCost
public import VCVio.OracleComp.QueryTracking.RandomOracle.ProjectedHazards

/-!
# Projected hits under the physical query count

When only one row of each pair names a target, each physical input contributes at most one entry.
The two coordinates of the same full query therefore share one budget.
-/

public section
open OracleComp OracleSpec
open scoped ENNReal
namespace CanonicalGraph.PairedQueries

variable {L H F X K : Type} (G : CanonicalGraph (PairedSpec L H) X K H) (e : F ≃ H × H)
  [SampleableType H]

/-- Charging only the low row assigns at most one projected target to any physical input. -/
theorem potential_le_physical (keys : G.ProjKeys) (high : ∀ b : L, keys.node (.inr b) = none)
    (s : RelabelState (PairedSpec L H) X K H) :
    keys.potential s ≤ ((physicalInputs s.1).encard : ℝ≥0∞) / Nat.card H := by
  have sub : keys.keyEntries s.1 ⊆ Sum.inl '' physicalInputs s.1 := by
    rintro (b | b) ⟨present, target⟩
    · exact ⟨b, Or.inl present, rfl⟩
    · simp [high] at target
  apply (keys.potential_le s).trans
  gcongr
  exact (Set.encard_le_encard sub).trans (Set.encard_image_le _ _)

variable [DecidableEq L] [DecidableEq X] [DecidableEq K]

/-- The probability of a projected hit within the measured budget is at most one uniform
label per paid query, including all queries in a setup followed by an adaptive caller. -/
theorem prEvent_hit_afterSetup_and_cost {α β : Type}
    (keys : G.ProjKeys) (high : ∀ b : L, keys.node (.inr b) = none)
    (setup : OracleComp ((PairedSpec L H).withLabels X K H) (β × Nat))
    (caller : β → OracleComp (FullWorld L F) α)
    (paid : ∀ z ∈ support ((simulateQ G.deferredImpl setup).run ((∅, ∅), [])),
      (physicalInputs z.2.1.1).encard ≤ z.1.2)
    (q : Nat) :
    Pr{let z ← G.deferredFillDraw (pure ()) (afterSetup e setup caller)}[
      keys.ProjHazard z.2.1 ∧ z.1.1.2 ≤ q] ≤ (q : ℝ≥0∞) / Nat.card H := by
  classical
  have pos : 0 < (Nat.card H : ℝ≥0∞) := by exact_mod_cast (Nat.card_pos (α := H))
  let bound (c : (PairedSpec L H).QueryCache) := ((physicalInputs c).encard : ℝ≥0∞) / Nat.card H
  have charge := keys.isCharged.prEvent_deferredFillDraw_and_le
    keys.not_projHazard_empty bound (potential_le_physical G keys high) (pure ())
    (fun _ _ => False) (fun _ => 0) (fun _ => by simp) (afterSetup e setup caller)
    ((q : ℝ≥0∞) / Nat.card H) (by finiteness)
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) charge
  rintro z hz ⟨hit, budget⟩
  obtain ⟨before, filled, _⟩ := G.mem_support_deferredFillDraw_iff.mp hz
  refine ⟨Or.inl hit, ?_⟩
  dsimp [bound]
  rw [add_zero, RelabelState.fst_eq_of_mem_support_endFill filled]
  gcongr
  exact_mod_cast (afterSetup_footprint G e setup caller paid _ before).trans
    (Nat.cast_le.mpr budget)

end CanonicalGraph.PairedQueries
