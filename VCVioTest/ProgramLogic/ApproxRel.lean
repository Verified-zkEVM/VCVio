/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.Relational

/-!
# Approximate relational triples

The composition rules of `ApproxRelTriple`: returned values, weakening, sequencing with the
errors adding, and transitivity of approximate equality. `by_approx` states an approximate triple
as the quantitative `RelTriple` that `rvcgen` decomposes, and `by_dist hybrid` runs a hybrid
argument on an advantage bound.
-/

public section

open ENNReal OracleSpec OracleComp OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic OracleComp.Rel.Quantitative

namespace VCVioTest.ProgramLogic.ApproxRel

variable {α β γ δ : Type}

/-- Returned values related by `R` are related with any error. -/
example (a : α) (b : β) (R : RelPost α β) (h : R a b) :
    ApproxRelTriple 0 (pure a : ProbComp α) (pure b : ProbComp β) R :=
  approxRelTriple_pure a b h 0

/-- The relation and the error weaken. -/
example (oa : ProbComp α) (ob : ProbComp β) (R : RelPost α β) (ε : ℝ≥0∞)
    (h : ApproxRelTriple ε oa ob R) : ApproxRelTriple (ε + 1 / 2) oa ob fun _ _ => True :=
  approxRelTriple_mono h (fun _ _ _ => trivial) le_self_add

/-- Sequencing adds the errors. -/
example (oa : ProbComp α) (ob : ProbComp β) (fa : α → ProbComp γ) (fb : β → ProbComp δ)
    (R : RelPost α β) (S : RelPost γ δ) (ε₁ ε₂ : ℝ≥0∞) (h₁ : ApproxRelTriple ε₁ oa ob R)
    (h₂ : ∀ a b, R a b → ApproxRelTriple ε₂ (fa a) (fb b) S) :
    ApproxRelTriple (ε₁ + ε₂) (oa >>= fa) (ob >>= fb) S :=
  approxRelTriple_bind h₁ h₂

/-- Approximate equality is transitive, with the errors adding. -/
example (oa ob oc : ProbComp α) (ε₁ ε₂ : ℝ≥0∞) (h₁ : ApproxRelTriple ε₁ oa ob (EqRel α))
    (h₂ : ApproxRelTriple ε₂ ob oc (EqRel α)) : ApproxRelTriple (ε₁ + ε₂) oa oc (EqRel α) :=
  approxRelTriple_eqRel_trans h₁ h₂

/-- An approximate triple of returned values through the quantitative carrier: `by_approx`
leaves the quantitative triple, whose precondition `rvcgen` computes from the returned values,
and the comparison of that precondition with `1 - ε`. -/
example (a : ℕ) : ApproxRelTriple 0 (pure a : ProbComp ℕ) (pure a : ProbComp ℕ) (EqRel ℕ) := by
  by_approx
  · rvcgen
  · simp [RelPost.indicator, EqRel]

/-- The same for a uniform draw coupled with itself: the identity coupling relates the draws. -/
example : ApproxRelTriple 0 ($ᵗ Bool : ProbComp Bool) ($ᵗ Bool : ProbComp Bool) (EqRel Bool) := by
  by_approx
  · rvcgen
  · simp [RelPost.indicator, EqRel]

/-- A hybrid argument on an advantage bound: the last game's bound plus the steps. -/
example (games : ℕ → ProbComp Bool) (n : ℕ) (ε : ℝ≥0∞) (step : ℕ → ℝ≥0∞)
    (hbound : AdvBound (games n) ε)
    (hstep : ∀ i < n, etvDist (games i) (games (i + 1)) ≤ step i) :
    AdvBound (games 0) (ε + ∑ i ∈ Finset.range n, step i) := by
  by_dist hybrid games n
  · exact hbound
  · exact hstep

end VCVioTest.ProgramLogic.ApproxRel
