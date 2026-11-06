/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.SchwartzZippel
public import Mathlib.Algebra.Field.ZMod

/-! ## Schwartz–Zippel sampling API tests

Concrete coordinate polynomials over `ZMod 5` exercise finite variable types and `Fin`-indexed
callers of the uniform probability bound.
-/

public section

open scoped ENNReal

namespace SchwartzZippelTest

/-- A uniformly sampled Boolean-indexed assignment zeros a coordinate polynomial with
probability at most `1 / 5`. -/
theorem bool_coordinate :
    Pr{let x ← $ᵗ (Bool → ZMod 5)}[
      MvPolynomial.eval x (MvPolynomial.X true : MvPolynomial Bool (ZMod 5)) = 0] ≤
      (1 : ℝ≥0∞) / 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  simpa using prob_eval_zero_univ_le_div
    (MvPolynomial.X true : MvPolynomial Bool (ZMod 5)) (MvPolynomial.X_ne_zero true)
    (d := 1) (by simp)

/-- A `Fin 2` coordinate polynomial over `ZMod 5` satisfies the uniform probability bound. -/
theorem fin_two_coordinate :
    Pr{let x ← $ᵗ (Fin 2 → ZMod 5)}[
      MvPolynomial.eval x (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod 5)) = 0] ≤
      (1 : ℝ≥0∞) / 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  simpa using prob_eval_zero_univ_le_div
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod 5)) (MvPolynomial.X_ne_zero 0)
    (d := 1) (by simp)

/-- The uniform probability bound specializes to abstract `Fin n` variables over a finite
integral domain, retaining the caller's function sampler. -/
theorem fin_compatibility
    {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R]
    {n d : ℕ} (P : MvPolynomial (Fin n) R) (h_nonzero : P ≠ 0)
    (h_deg : P.totalDegree ≤ d) :
    Pr{let r ← $ᵗ (Fin n → R)}[MvPolynomial.eval r P = 0] ≤
      (d : ℝ≥0∞) / Fintype.card R := open scoped Classical in by
  let : Field R := @Fintype.fieldOfDomain R _ _ (Classical.decEq R) _
  exact prob_eval_zero_univ_le_div P h_nonzero h_deg

end SchwartzZippelTest
