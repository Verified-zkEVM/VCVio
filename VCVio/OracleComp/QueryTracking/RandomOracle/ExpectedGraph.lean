/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedPotential
public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential

/-!
# A deferred graph hazard charged to its expected public footprint

The pending cells depend on the full adaptive run.
The public cache is unchanged when the graph fills those cells.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace CanonicalGraph

variable {ι X K R α : Type} {pub : OracleSpec ι} {G : CanonicalGraph pub X K R}
  [DecidableEq ι] [DecidableEq X] [DecidableEq K]
  [SampleableType R] [∀ t, SampleableType (pub.Range t)]
  {P : RelabelState pub X K R → Prop} {Φ : RelabelState pub X K R → ℝ≥0∞}

/-- The user may stop adaptively with an arbitrary list of pending cells.
The hazard after filling them is priced by the expected public charge before that fill. -/
theorem IsCharged.prEvent_deferredFillDraw_le_expected (h : G.IsCharged P Φ)
    (clean : ¬ P (∅, ∅)) (U : pub.QueryCache → ℝ≥0∞) (upper : ∀ s, Φ s ≤ U s.1)
    (oa : OracleComp (pub.withLabels X K R) α) :
    Pr{let z ← G.deferredFillDraw (pure ()) oa}[P z.2.1] ≤
      ∑' z, Pr{let u ← (simulateQ G.deferredImpl oa).run ((∅, ∅), [])}[u = z] * U z.2.1.1 := by
  classical
  let m := (simulateQ G.deferredImpl oa).run ((∅, ∅), [])
  have start := h.isPotentialStep_deferredImpl.expected_credit oa ((∅, ∅), [])
  have one : 1 ≤ ∑' z, Pr{let u ← m}[u = z] * (Φ z.2.1 + if P z.2.1 then 0 else 1) := by
    exact (by simp [clean] : 1 ≤ Φ (∅, ∅) + (if P (∅, ∅) then 0 else 1)).trans start
  have fill (z : α × RelabelState pub X K R × List (X ⊕ K)) :
      Φ z.2.1 + (if P z.2.1 then 0 else 1) ≤
      ∑' s, Pr{let v ← RelabelState.endFill z.2}[v = s] * (Φ s + if P s then 0 else 1) := by
    rw [RelabelState.endFill_eq_simulateQ_cellImpl, tsum_prEvent_map_mul]
    exact h.isPotentialStep_cellImpl.expected_credit (((X ⊕ K) →ₒ R).queryAll z.2.2) z.2.1
  have credit : 1 ≤ ∑' z, Pr{let u ← G.deferredFillDraw (pure ()) oa}[u = z] *
      (Φ z.2.1 + if P z.2.1 then 0 else 1) := by
    simp only [deferredFillDraw, pure_bind, tsum_prEvent_bind_mul, tsum_prEvent_pure_mul]
    exact one.trans (tsum_le_tsum fun z => mul_le_mul_of_nonneg_left (fill z) zero_le)
  apply (prEvent_le_expected_of_credit (G.deferredFillDraw (pure ()) oa)
    (fun z => P z.2.1) (fun z => Φ z.2.1) credit).trans
  simp only [deferredFillDraw, pure_bind, tsum_prEvent_bind_mul, tsum_prEvent_pure_mul]
  apply tsum_le_tsum
  intro z
  apply mul_le_mul_of_nonneg_left _ zero_le
  have fixed := tsum_prEvent_mul_of_const_on_support (RelabelState.endFill z.2)
    (f := fun s => U s.1) (c := U z.2.1.1)
    (fun _ hs => congrArg U (RelabelState.fst_eq_of_mem_support_endFill hs))
  rw [← fixed]
  exact tsum_le_tsum fun s => mul_le_mul_of_nonneg_left (upper s) zero_le

end CanonicalGraph
