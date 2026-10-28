/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

-- Enumeration entry points inspected by the per-module initialization sweep.
import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Pi

/-! # Affine representations and scalar extraction

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). An element's exponent is a known affine
function of a single hidden scalar. A nonzero verification gap reveals that scalar.
-/

public section

namespace GroupModel.LinearFunctional

/-- An affine expression in one hidden scalar, with a constant and a linear coefficient. -/
@[ext] structure AffineForm (F : Type*) where
  /-- The part independent of the hidden scalar. -/
  const : F
  /-- The coefficient of the hidden scalar. -/
  lin : F

/-- Evaluate an affine representation at a scalar. -/
@[expose] def AffineForm.eval {F : Type*} [Add F] [Mul F]
    (out : AffineForm F) (α : F) : F := out.const + out.lin * α

/-- A nonzero verification gap determines the hidden scalar from an affine representation. -/
theorem AffineForm.extract_secret {F : Type*} [Field F] {α c : F} {out : AffineForm F}
    (hverify : out.eval α = c * α) (hnondeg : out.lin ≠ c) :
    α = out.const / (c - out.lin) := by
  rw [eq_div_iff (sub_ne_zero.mpr hnondeg.symm)]
  simp only [AffineForm.eval] at hverify
  linear_combination -hverify

end GroupModel.LinearFunctional
