/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.SchwartzZippel
public import Mathlib.Algebra.Field.ZMod

/-! ## Schwartz–Zippel sampling API tests

Concrete coordinate polynomials over `ZMod 5` exercise finite variable types, `Fin`-indexed
callers of the uniform probability bound, and the subset form over the nonzero residues.
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
  simpa using prEvent_eval_eq_zero_univ_le_div
    (MvPolynomial.X true : MvPolynomial Bool (ZMod 5)) (MvPolynomial.X_ne_zero true)
    (d := 1) (by simp)

/-- A `Fin 2` coordinate polynomial over `ZMod 5` satisfies the uniform probability bound. -/
theorem fin_two_coordinate :
    Pr{let x ← $ᵗ (Fin 2 → ZMod 5)}[
      MvPolynomial.eval x (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod 5)) = 0] ≤
      (1 : ℝ≥0∞) / 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  simpa using prEvent_eval_eq_zero_univ_le_div
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod 5)) (MvPolynomial.X_ne_zero 0)
    (d := 1) (by simp)

/-- The uniform probability bound specializes to abstract `Fin n` variables over a finite
integral domain, retaining the caller's function sampler. -/
theorem fin_compatibility
    {R : Type} [CommRing R] [IsDomain R] [Fintype R] [SampleableType R]
    {n d : ℕ} (P : MvPolynomial (Fin n) R) (h_nonzero : P ≠ 0)
    (h_deg : P.totalDegree ≤ d) :
    Pr{let r ← $ᵗ (Fin n → R)}[MvPolynomial.eval r P = 0] ≤
      (d : ℝ≥0∞) / Fintype.card R :=
  prEvent_eval_eq_zero_univ_le_div P h_nonzero h_deg

/-- The nonzero residues of `ZMod 5`, the factor set of the subset form of the bound. -/
abbrev nonzeroResidues : Set (ZMod 5) := {x | x ≠ 0}

instance : Nonempty ↥nonzeroResidues := ⟨⟨1, by decide⟩⟩

/-- The subset form of the bound, over the four nonzero residues of `ZMod 5`. -/
theorem bool_coordinate_nonzero :
    Pr{let x ← $ᵗ (∀ _ : Bool, ↥nonzeroResidues)}[
      MvPolynomial.eval (fun i => (x i : ZMod 5))
        (MvPolynomial.X true : MvPolynomial Bool (ZMod 5)) = 0] ≤ (1 : ℝ≥0∞) / 4 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  simpa using prEvent_eval_eq_zero_le_div (S := fun _ => nonzeroResidues)
    (MvPolynomial.X true : MvPolynomial Bool (ZMod 5)) (MvPolynomial.X_ne_zero true) 1 4
    (by simp) (fun _ => by decide)

end SchwartzZippelTest
