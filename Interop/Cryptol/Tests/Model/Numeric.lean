/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Model.Numeric

/-! # Numeric definedness and substitution regressions -/

public section

open Interop.Cryptol

example : NumericBinary.eval .sub (.finite 2) (.finite 3) = none := rfl
example : NumericBinary.eval .sub .infinite .infinite = none := rfl
example : NumericBinary.eval .mul (.finite 0) .infinite = some (.finite 0) := rfl
example : NumericBinary.eval .div .infinite (.finite 8) = none := rfl
example : NumericBinary.eval .ceilDiv .infinite (.finite 8) = some .infinite := rfl
example : NumericBinary.eval .ceilMod .infinite (.finite 8) = some (.finite 0) := rfl
example : NumericBinary.eval .ceilMod (.finite 9) .infinite = none := rfl
example : NumericBinary.eval .div (.finite 9) .infinite = some (.finite 0) := rfl
example : NumericBinary.eval .mod (.finite 9) .infinite = some (.finite 9) := rfl
example : NumericBinary.eval .exp (.finite 0) (.finite 0) = some (.finite 1) := rfl
example : NumericBinary.eval .exp (.finite 1) .infinite = some (.finite 1) := rfl
example : NumericUnary.eval .width (.finite 8) = .finite 4 := rfl
example : NumericUnary.eval .lg2 (.finite 8) = .finite 3 := rfl
example : NumericUnary.eval .lg2 (.finite 9) = .finite 4 := rfl
example : numericRangeLength (.finite 7) (.finite 5) (.finite 0) = some (.finite 4) := rfl
example : numericRangeLength (.finite 7) (.finite 5) (.finite 8) = some (.finite 0) := rfl
example : numericRangeLength (.finite 7) (.finite 7) (.finite 7) = none := rfl

example (e : NumericExpr 2) (σ : Fin 2 → NumericExpr 1) (ρ : Fin 1 → Option Length) :
    (e.subst σ).eval ρ = e.eval (fun i => (σ i).eval ρ) := e.eval_subst σ ρ

example : (NumericExpr.finite (n := 1) 7).eval (fun _ => none) = some (.finite 7) := rfl

example : ((NumericExpr.var (n := 1) 0).subst
    (fun _ => .binary .div (.finite 1) (.finite 0))).eval? Fin.elim0 = none := rfl
