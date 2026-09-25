/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Devon Tuma
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Pointwise polynomial bounds

`PolyBound f` says that `f` is bounded at every input by a natural polynomial. The definition and
its algebraic closure results retain Bolton Bailey's formulation from complexitylib in a namespace
isolated for VCVio's concrete backend package.

The asymptotic `BigO` conversion is outside this module. Exact pointwise accounting is sufficient
for the backend interface and avoids coupling it to a particular asymptotic-notation adapter.
-/

@[expose] public section

namespace VCVioComplexity

/-- Pointwise domination by the evaluation of a natural polynomial. -/
def PolyBound (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ inputLength, f inputLength ≤ p.eval inputLength

namespace PolyBound

theorem const (value : ℕ) : PolyBound (fun _ ↦ value) :=
  ⟨Polynomial.C value, fun _ ↦ by simp⟩

theorem id : PolyBound (fun inputLength ↦ inputLength) :=
  ⟨Polynomial.X, fun _ ↦ by simp⟩

theorem add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength ↦ f inputLength + g inputLength) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun inputLength ↦ by
    rw [Polynomial.eval_add]
    exact Nat.add_le_add (hp inputLength) (hq inputLength)⟩

theorem mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength ↦ f inputLength * g inputLength) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun inputLength ↦ by
    rw [Polynomial.eval_mul]
    exact Nat.mul_le_mul (hp inputLength) (hq inputLength)⟩

theorem mono {f g : ℕ → ℕ} (hg : PolyBound g)
    (hle : ∀ inputLength, f inputLength ≤ g inputLength) : PolyBound f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun inputLength ↦ le_trans (hle inputLength) (hp inputLength)⟩

theorem max {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength ↦ max (f inputLength) (g inputLength)) :=
  (hf.add hg).mono fun _ ↦ Nat.max_le.mpr
    ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

theorem eval (p : Polynomial ℕ) :
    PolyBound (fun inputLength ↦ p.eval inputLength) :=
  ⟨p, fun _ ↦ le_rfl⟩

theorem pow {f : ℕ → ℕ} (hf : PolyBound f) (exponent : ℕ) :
    PolyBound (fun inputLength ↦ f inputLength ^ exponent) := by
  induction exponent with
  | zero => simpa using const 1
  | succ exponent ih => simpa [pow_succ] using ih.mul hf

end PolyBound

end VCVioComplexity
