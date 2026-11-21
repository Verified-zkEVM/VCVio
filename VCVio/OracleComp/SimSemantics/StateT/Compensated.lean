/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Accumulating a compensated increase along an adaptive caller

A one-query inequality can compare two changes without subtracting nonnegative masses.
The intermediate expected reserve is finite and cancels when the caller continues.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace QueryImpl

private noncomputable abbrev avg {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞) :=
  ∑' x, Pr{let u ← p}[u = x] * f x

private theorem avg_add {α : Type} (p : ProbComp α) (f g : α → ℝ≥0∞) :
    avg p (fun x => f x + g x) = avg p f + avg p g := by
  simp only [avg, mul_add, tsum_add]

private theorem avg_fin {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞)
    (fin : ∀ x ∈ support p, f x ≠ ⊤) : avg p f ≠ ⊤ := by
  classical
  let vals := (OracleComp.support_finite p).toFinset
  rw [avg, tsum_eq_sum (s := vals) (fun x h => by
    rw [prEvent_eq_zero_of_not_mem_support p (by simpa [vals] using h), zero_mul])]
  exact ENNReal.sum_ne_top.mpr fun x hx =>
    ENNReal.mul_ne_top (prEvent_ne_top _) (fin x (by simpa [vals] using hx))

/-- A reserve paying the gain at each individual query pays the accumulated gain of any caller.
Both expected values refer to the same complete resulting state, even after an adaptive stop. -/
theorem run_compensated {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (I : σ → Prop) (preserves : impl.PreservesInv I) (value reserve : σ → ℝ≥0∞)
    (finite : ∀ s, I s → reserve s ≠ ⊤)
    (step : ∀ t s, I s →
      (∑' z, Pr{let u ← (impl t).run s}[u = z] * value z.2) + reserve s ≤
        value s + ∑' z, Pr{let u ← (impl t).run s}[u = z] * reserve z.2)
    (caller : OracleComp spec α) (s : σ) (initial : I s) :
    let run := (simulateQ impl caller).run s
    (∑' z, Pr{let u ← run}[u = z] * value z.2) + reserve s ≤
      value s + ∑' z, Pr{let u ← run}[u = z] * reserve z.2 := by
  induction caller using OracleComp.inductionOn generalizing s with
  | pure a =>
    dsimp only
    rw [simulateQ_pure, StateT.run_pure, tsum_prEvent_pure_mul, tsum_prEvent_pure_mul]
  | query_bind t k ih =>
    dsimp only
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      tsum_prEvent_bind_mul, tsum_prEvent_bind_mul]
    let first := (impl t).run s
    let E (f : σ → ℝ≥0∞) (z : spec.Range t × σ) :=
      avg ((simulateQ impl (k z.1)).run z.2) (fun u => f u.2)
    let old := fun z : spec.Range t × σ => value z.2
    let cost := fun z : spec.Range t × σ => reserve z.2
    have fin : avg first cost ≠ ⊤ := avg_fin first cost fun z hz =>
      finite z.2 (preserves t s initial z hz)
    have tails : avg first (E value) + avg first cost ≤ avg first old + avg first (E reserve) := by
      rw [← avg_add, ← avg_add]
      apply tsum_le_tsum
      intro z
      by_cases reached : z ∈ support first
      · exact mul_le_mul_right (ih z.1 z.2 (preserves t s initial z reached)) _
      · simp only [prEvent_eq_zero_of_not_mem_support first reached, zero_mul, le_refl]
    apply ENNReal.le_of_add_le_add_right fin
    change avg first (E value) + reserve s + avg first cost ≤
      value s + avg first (E reserve) + avg first cost
    calc
      _ = (avg first (E value) + avg first cost) + reserve s := by ac_rfl
      _ ≤ (avg first old + avg first (E reserve)) + reserve s := add_le_add_left tails _
      _ = (avg first old + reserve s) + avg first (E reserve) := by ac_rfl
      _ ≤ (value s + avg first cost) + avg first (E reserve) := add_le_add_left (step t s initial) _
      _ = _ := by ac_rfl

end QueryImpl
