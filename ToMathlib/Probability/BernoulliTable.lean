/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.Fin.VecNotation
public import ToMathlib.Probability.ProbabilityMassFunction.Pi

/-!
# Independent Bernoulli tables

`PMF.bernoulliTable p hp` is the distribution on `C → Bool` in which entry `c` is `true` with
probability `p c`, independently across `c`. It is the `Bool`-valued instance of the general
independent product `PMF.pi`, with per-entry weights `tableWeight`.

The two facts a caller needs are the pointwise weight (`bernoulliTable_apply`, definitionally the
product) and the marginal of a single entry (`sum_filter_bernoulliTable`), which is `PMF.pi`'s
marginal read at `true`.

A coordinate-wise table bound holds pointwise, so *averaging* it needs only the marginals and no
independence. Choosing this particular coupling is nonetheless a modelling decision, not a
consequence: the averaged quantity depends on the whole joint distribution. Independent entries
are the coupling used by the analytic multi-round recurrence; this file does not connect them to
executions of an oracle extractor.
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

/-- The single-entry distribution: `true` with probability `p c`. -/
noncomputable def bernoulliEntry (p : C → ℝ≥0∞) (hp : ∀ c, p c ≤ 1) (c : C) : PMF Bool :=
  PMF.ofFintype (tableWeight p c) (sum_tableWeight hp c)

omit [Fintype C] [DecidableEq C] in
@[simp] theorem bernoulliEntry_apply (hp : ∀ c, p c ≤ 1) (c : C) (b : Bool) :
    bernoulliEntry p hp c b = tableWeight p c b := rfl

/-- The distribution on `C → Bool` making entry `c` true with probability `p c`, independently
across entries. -/
noncomputable def bernoulliTable (p : C → ℝ≥0∞) (hp : ∀ c, p c ≤ 1) : PMF (C → Bool) :=
  PMF.pi (bernoulliEntry p hp)

theorem bernoulliTable_apply (hp : ∀ c, p c ≤ 1) (ρ : C → Bool) :
    bernoulliTable p hp ρ = ∏ c, tableWeight p c (ρ c) := rfl

/-- The construction depends only on the bias family, not on the proof that it is one. -/
theorem bernoulliTable_congr {q : C → ℝ≥0∞} (hp : ∀ c, p c ≤ 1) (hq : ∀ c, q c ≤ 1)
    (h : p = q) : bernoulliTable p hp = bernoulliTable q hq := by
  subst h; rfl

/-- The marginal of a single entry is exactly its intended bias. -/
theorem sum_filter_bernoulliTable (hp : ∀ c, p c ≤ 1) (c₀ : C) :
    ∑ ρ ∈ Finset.univ.filter fun ρ : C → Bool => ρ c₀ = true, bernoulliTable p hp ρ = p c₀ :=
  PMF.sum_filter_pi (bernoulliEntry p hp) c₀ true

/-- Two entries: the weight really is the product of the per-entry biases, so the construction is
independent rather than merely correct on marginals. -/
example (p : Fin 2 → ℝ≥0∞) (hp : ∀ c, p c ≤ 1) :
    bernoulliTable p hp ![true, false] = p 0 * (1 - p 1) := by
  simp [bernoulliTable_apply, tableWeight, Fin.prod_univ_two]

end PMF
