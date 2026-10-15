/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Laws

/-!
# Structural zero

Zero constructs aggregate values recursively, including infinite sequences
and constant functions. It demands no input and preserves lazy components.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- Structural zero at a closed instantiated type. -/
@[expose] def Expr.zero {Γ : List ClosedTy} : (a : ClosedTy) → Expr Γ a
  | .var v => v.elim
  | .bit => .bit false
  | .integer => .integer 0
  | .unit => .unit
  | .seq l a => .generate l (.zero a)
  | .prod a b => .pair (.zero a) (.zero b)
  | .arrow _ b => .lam (.zero b)

/-- Independent reference meaning of structural zero. -/
@[expose] noncomputable def Semantics.zero : (a : ClosedTy) → Computation a
  | .var v => v.elim
  | .bit => .value ⟨false⟩
  | .integer => .value ⟨0⟩
  | .unit => .value ⟨()⟩
  | .seq _ a => .value (fun _ => zero a)
  | .prod a b => .value (zero a, zero b)
  | .arrow _ b => .value (.const (zero b))

/-- Core construction preserves zero at every closed type. -/
theorem Expr.denote_zero {Γ : List ClosedTy} (a : ClosedTy) (ρ : Environment Γ) :
    (zero a).denote ρ = Semantics.zero a := by
  induction a generalizing Γ with
  | var v => exact v.elim
  | bit | integer | unit => rfl
  | seq l a ih =>
      rw [zero, denote_generate]
      change DomainResult.value _ = DomainResult.value _
      apply congrArg DomainResult.value
      funext i
      exact ih _
  | prod a b iha ihb =>
      rw [zero, denote_pair, iha, ihb]
      rfl
  | arrow a b _ ih =>
      apply Expr.denote_lam_eq
      intro x
      exact ih _

end Interop.Cryptol
