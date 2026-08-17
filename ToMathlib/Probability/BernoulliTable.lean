/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Independent Bernoulli tables

`PMF.bernoulliTable p hp` is the distribution on `C → Bool` in which entry `c` is `true` with
probability `p c`, independently across `c`. Neither Mathlib nor this repository has a general
product of distributions over a `Fintype`-indexed family, so it is built directly from
`PMF.ofFintype` with the product weight; `Fintype.prod_sum` turns the total mass into a product of
per-entry masses, each of which is `p c + (1 - p c) = 1`.

The two facts a caller needs are the pointwise weight (`bernoulliTable_apply`, definitionally the
product) and the marginal of a single entry (`sum_filter_bernoulliTable`).

A coordinate-wise table bound holds pointwise, so *averaging* it needs only the marginals and no
independence. Choosing this particular coupling is nonetheless a modelling decision, not a
consequence: the averaged quantity depends on the whole joint distribution. Independent entries
are the coupling used by the analytic multi-round recurrence; this file does not connect them to
executions of an oracle extractor. `sum_filter_bernoulliTable` is where the product structure is
actually used.
-/

@[expose] public section

open Finset

open scoped ENNReal

namespace PMF

variable {C : Type*} [Fintype C] [DecidableEq C] {p : C → ℝ≥0∞}

/-- The weight of a single table entry: `p c` for `true`, and the remaining mass for `false`. -/
def tableWeight (p : C → ℝ≥0∞) (c : C) (b : Bool) : ℝ≥0∞ :=
  if b then p c else 1 - p c

omit [Fintype C] [DecidableEq C] in
@[simp] theorem tableWeight_true (c : C) : tableWeight p c true = p c := rfl

omit [Fintype C] [DecidableEq C] in
@[simp] theorem tableWeight_false (c : C) : tableWeight p c false = 1 - p c := rfl

omit [Fintype C] [DecidableEq C] in
theorem sum_tableWeight (hp : ∀ c, p c ≤ 1) (c : C) : ∑ b : Bool, tableWeight p c b = 1 := by
  rw [Fintype.sum_bool, tableWeight_true, tableWeight_false, add_tsub_cancel_of_le (hp c)]

/-- The distribution on `C → Bool` making entry `c` true with probability `p c`, independently
across entries. -/
noncomputable def bernoulliTable (p : C → ℝ≥0∞) (hp : ∀ c, p c ≤ 1) : PMF (C → Bool) :=
  PMF.ofFintype (fun ρ => ∏ c, tableWeight p c (ρ c)) <| by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun c _ => sum_tableWeight hp c

theorem bernoulliTable_apply (hp : ∀ c, p c ≤ 1) (ρ : C → Bool) :
    bernoulliTable p hp ρ = ∏ c, tableWeight p c (ρ c) := rfl

/-- The construction depends only on the bias family, not on the proof that it is one. -/
theorem bernoulliTable_congr {q : C → ℝ≥0∞} (hp : ∀ c, p c ≤ 1) (hq : ∀ c, q c ≤ 1)
    (h : p = q) : bernoulliTable p hp = bernoulliTable q hq := by
  subst h; rfl

/-- The marginal of a single entry is exactly its intended bias.

The false branch at `c₀` is zeroed out, which turns the sum over tables into a product of
per-entry masses in which every entry but `c₀` contributes `1`. -/
theorem sum_filter_bernoulliTable (hp : ∀ c, p c ≤ 1) (c₀ : C) :
    ∑ ρ ∈ Finset.univ.filter fun ρ : C → Bool => ρ c₀ = true, bernoulliTable p hp ρ = p c₀ := by
  classical
  -- The weight family with the `false` branch at `c₀` deleted.
  set w : C → Bool → ℝ≥0∞ :=
    fun c b => if c = c₀ then (if b then p c₀ else 0) else tableWeight p c b with hw
  have hsum : ∀ c : C, ∑ b : Bool, w c b = if c = c₀ then p c₀ else 1 := by
    intro c
    by_cases hc : c = c₀
    · simp [hw, hc]
    · simp only [hw, if_neg hc]
      exact sum_tableWeight hp c
  -- Deleting that branch is exactly restricting the sum to tables accepting at `c₀`.
  have hrestrict : ∀ ρ : C → Bool,
      (∏ c, w c (ρ c)) = if ρ c₀ = true then ∏ c, tableWeight p c (ρ c) else 0 := by
    intro ρ
    by_cases hρ : ρ c₀ = true
    · refine (if_pos hρ) ▸ Finset.prod_congr rfl fun c _ => ?_
      by_cases hc : c = c₀
      · subst hc; simp [hw, hρ]
      · simp [hw, hc]
    · have hρ' : ρ c₀ = false := by simpa using hρ
      rw [if_neg hρ]
      exact Finset.prod_eq_zero (Finset.mem_univ c₀) (by simp [hw, hρ'])
  calc ∑ ρ ∈ Finset.univ.filter fun ρ : C → Bool => ρ c₀ = true, bernoulliTable p hp ρ
      = ∑ ρ : C → Bool, if ρ c₀ = true then ∏ c, tableWeight p c (ρ c) else 0 := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun ρ _ => by rw [bernoulliTable_apply]
    _ = ∑ ρ : C → Bool, ∏ c, w c (ρ c) := (Finset.sum_congr rfl fun ρ _ => hrestrict ρ).symm
    _ = ∏ c, ∑ b : Bool, w c b := (Fintype.prod_sum _).symm
    _ = p c₀ := by rw [Finset.prod_congr rfl fun c _ => hsum c]; simp

/-- Two entries: the weight really is the product of the per-entry biases, so the construction is
independent rather than merely correct on marginals. -/
example (p : Fin 2 → ℝ≥0∞) (hp : ∀ c, p c ≤ 1) :
    bernoulliTable p hp ![true, false] = p 0 * (1 - p 1) := by
  simp [bernoulliTable, tableWeight, Fin.prod_univ_two]

end PMF
