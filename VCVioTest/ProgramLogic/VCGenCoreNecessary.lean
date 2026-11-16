/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics

/-!
# `pvcgen` on core `vcgen` in the necessary reading

Exhaustive `pvcgen` hands a core triple in the necessary reading (`open scoped
OracleComp.Necessary`) to core `vcgen`, opening only that reading, and does the same for a
support statement `∀ x ∈ support oa, post x`, which it first restates as the triple
`⦃ True ⦄ oa ⦃ post ⦄` (`OracleComp.Necessary.triple_true_iff_forall_support`). Core descends
through queries, uniform draws, binds and conditionals, a draw returning any value; `pvcgen`
closes the verification conditions that `simp_all` closes and reads the weakest precondition of
an opaque sub-program back as a support statement. Triples whose precondition is in `ℝ≥0∞` keep
the lower reading, and `vcstep` stays a single step.
-/

public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP ENNReal

namespace VCVioTest.ProgramLogic.VCGenCoreNecessary

variable {ι : Type} {spec : OracleSpec ι}

/-! ## Support statements -/

example (t : spec.Domain) (f : spec.Range t → Bool) :
    ∀ r ∈ support (do
      let u ← (query t : OracleComp spec _)
      if f u then
        let v ← (query t : OracleComp spec _)
        pure (f u || f v)
      else pure true : OracleComp spec Bool), r = true := by
  pvcgen

example (n : ℕ) :
    ∀ r ∈ support (do
      let i ← $[0..n]
      let b ← $ᵗ Bool
      if b then pure i.val else pure 0 : ProbComp ℕ), r ≤ n := by
  pvcgen
  omega

example : ∀ xs ∈ support (do
      let b ← $ᵗ Bool
      let xs ← ($ᵗ Bool).replicate 3
      pure (b :: xs) : ProbComp (List Bool)), xs.length = 4 := by
  pvcgen

/-- A support statement under a binder: `pvcgen` introduces `k` and then hands the statement to
core. -/
example : ∀ k : ℕ, ∀ r ∈ support (do
      let b ← $ᵗ Bool
      pure (if b then k else k) : ProbComp ℕ), r = k := by
  pvcgen

/-- An opaque sub-program has no rule: its weakest precondition is read back as a support
statement, and the next passes introduce its output and continue into the rest. -/
example (oa : ProbComp ℕ) (h : ∀ n ∈ support oa, n < 5) :
    ∀ r ∈ support (do
      let n ← oa
      let b ← $ᵗ Bool
      pure (if b then n else 0)), r < 5 := by
  pvcgen

/-! ## Core triples in the necessary reading -/

section Necessary

open scoped OracleComp.Necessary

example (t : spec.Domain) (p : spec.Range t → spec.Range t → Prop) (hp : ∀ u v, p u v) :
    ⦃ True ⦄ (do
      let u ← (query t : OracleComp spec _)
      let v ← (query t : OracleComp spec _)
      pure (u, v)) ⦃ fun uv => p uv.1 uv.2 ⦄ := by
  pvcgen

example (n : ℕ) (P : Prop) (h : P → 3 ≤ n) :
    ⦃ P ⦄ (do
      let b ← $ᵗ Bool
      if b then pure 3 else pure 0 : ProbComp ℕ) ⦃ fun r => r ≤ n ⦄ := by
  pvcgen

/-- A triple in the local context is a rule for core. -/
example (oa : ProbComp ℕ) (h : ⦃ True ⦄ oa ⦃ fun n => n < 5 ⦄) :
    ⦃ True ⦄ (do
      let n ← oa
      let b ← $ᵗ Bool
      pure (if b then n else 0)) ⦃ fun r => r < 5 ⦄ := by
  pvcgen
  split <;> omega

/-- Core's transformer layers over the necessary reading. -/
example : ⦃ fun n => n = 0 ⦄
    (do let b ← liftM ($ᵗ Bool); modify (· + 1); pure b : StateT ℕ ProbComp Bool)
    ⦃ fun _ n => n = 1 ⦄ := by
  pvcgen

/-- `vcstep` takes one step and does not hand the triple to core. -/
example : ⦃ True ⦄ (do let b ← $ᵗ Bool; let c ← $ᵗ Bool; pure (b || c || true) : ProbComp Bool)
    ⦃ fun r => r = true ⦄ := by
  vcstep
  exact ⟨fun _ _ _ => trivial⟩

end Necessary

/-! ## The lower reading -/

/-- A fractional bound still takes the exact rules of the lower reading, which leave the averages
of the draws. -/
example : (4⁻¹ : ℝ≥0∞) ≤ Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b && c) = true] := by
  pvcgen
  guard_target = (4⁻¹ : ℝ≥0∞) ≤
    (∑' a : Bool, (∑' x : Bool, if (a && x) = true then 1 else 0) / (Nat.card Bool : ℝ≥0∞)) /
      (Nat.card Bool : ℝ≥0∞)
  norm_num [ENNReal.div_eq_inv_mul, Finset.filter_insert, Finset.filter_singleton,
    ← ENNReal.mul_inv]

/-- A probability-one event still takes the pointwise rules of the lower reading. -/
example : Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b || c || true) = true] = 1 := by
  pvcgen

set_option vcvio.vcgen.core false in
/-- With the delegation switched off, a support statement is introduced and left to the caller. -/
example : ∀ r ∈ support (do
      let b ← $ᵗ Bool
      pure (b || true) : ProbComp Bool), r = true := by
  pvcgen
  simp_all

end VCVioTest.ProgramLogic.VCGenCoreNecessary
