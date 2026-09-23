/-
Copyright (c) 2026 Quang Dao, Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.CompleteLatticeIntervals

/-!
# Bounded probability assertions

The lower interval of nonnegative extended reals bounded by one, with its inherited lattice
and indicator assertions.
-/

public section

open ENNReal

/-! ## The `Prob` carrier

`Prob` is the closed unit interval `[0, 1] ⊆ ℝ≥0∞`. It is a complete
bounded lattice under the inherited `≤` from `ℝ≥0∞`, with sup of any
predicate-encoded subset given by `sSup` (clamped at `1`, but the bound
follows for free since every element is already `≤ 1`).
-/

/-- The closed unit interval `[0, 1]` as a subtype of `ℝ≥0∞`.

Used as the carrier for the probabilistic `Std.Internal.Do.WP` interpretation of
`OracleComp` (see `OracleComp.Probabilistic.instWP_prob`). The
`Subtype.val` coercion to `ℝ≥0∞` is free, so probabilistic statements
re-export to the quantitative carrier without duplication. -/
abbrev Prob : Type := Set.Iic (1 : ℝ≥0∞)

namespace Prob

/-- Underlying `ℝ≥0∞` value. -/
@[expose, coe] def val (p : Prob) : ℝ≥0∞ := p.1

instance : Coe Prob ℝ≥0∞ := ⟨val⟩

@[ext] theorem ext {p q : Prob} (h : p.val = q.val) : p = q := Subtype.ext h

/-- The `≤ 1` witness for any `Prob`. -/
theorem val_le_one (p : Prob) : p.val ≤ 1 := p.2

instance : Zero Prob := ⟨⟨(0 : ℝ≥0∞), show (0 : ℝ≥0∞) ≤ 1 from zero_le_one⟩⟩
instance : One Prob := ⟨⟨(1 : ℝ≥0∞), show (1 : ℝ≥0∞) ≤ 1 from le_rfl⟩⟩

@[simp] theorem val_zero : (0 : Prob).val = 0 := rfl
@[simp] theorem val_one : (1 : Prob).val = 1 := rfl

/-- Indicator coercion from a decidable proposition to `Prob`: `1` if `p`
holds, `0` otherwise. Used to lift a qualitative post `α → Prop` into a
probabilistic post `α → Prob`, as in
`OracleComp.WP.Coherence.wp_qual_iff_wp_prob_indicator_eq_one`. -/
@[expose] def indicator (p : Prop) [Decidable p] : Prob :=
  ⟨if p then 1 else 0, by split_ifs <;> simp⟩

@[simp] theorem val_indicator (p : Prop) [Decidable p] :
    (indicator p).val = if p then 1 else 0 := rfl

end Prob
