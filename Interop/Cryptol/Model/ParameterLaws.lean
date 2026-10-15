/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Parameters

/-! # Assignment laws under numeric and type binders -/

public section

namespace Interop.Cryptol.ParameterAssignment

/-- Assignments are determined by their two components. -/
@[ext] theorem ext {n v : Nat} {ρ η : ParameterAssignment n v}
    (hn : ρ.numbers = η.numbers) (ht : ρ.types = η.types) : ρ = η := by
  cases ρ
  cases η
  cases hn
  cases ht
  rfl

@[simp] theorem pull_id {n v : Nat} (ρ : ParameterAssignment n v) :
    ρ.pull (ParameterSubstitution.id n v) = ρ := by
  apply ext <;> rfl

/-- Pulling assignments reverses composition of symbolic substitutions. -/
theorem pull_comp {n v m w k u : Nat} (ρ : ParameterAssignment k u)
    (σ : ParameterSubstitution n v m w) (τ : ParameterSubstitution m w k u) :
    ρ.pull (σ.comp τ) = (ρ.pull τ).pull σ := by
  apply ext
  · funext i
    exact NumExpr.eval_subst _ _ _
  · funext i
    exact apply_subst _ _ _

@[simp] theorem pull_weakenNum {n v : Nat} (ρ : ParameterAssignment n v) (l : Length) :
    (ρ.extendNum l).pull (ParameterSubstitution.weakenNum n v) = ρ := by
  apply ext <;> rfl

@[simp] theorem pull_weakenType {n v : Nat} (ρ : ParameterAssignment n v) (a : ClosedTy) :
    (ρ.extendType a).pull (ParameterSubstitution.weakenType n v) = ρ := by
  apply ext <;> rfl

@[simp] theorem apply_weakenNum {n v : Nat} (ρ : ParameterAssignment n v)
    (l : Length) (a : PolyTy n v) :
    (ρ.extendNum l).apply ((ParameterSubstitution.weakenNum n v).apply a) = ρ.apply a := by
  rw [apply_subst, pull_weakenNum]

@[simp] theorem apply_weakenType {n v : Nat} (ρ : ParameterAssignment n v)
    (t : ClosedTy) (a : PolyTy n v) :
    (ρ.extendType t).apply ((ParameterSubstitution.weakenType n v).apply a) = ρ.apply a := by
  rw [apply_subst, pull_weakenType]

/-- Lifting a substitution commutes with extending its numeric assignment. -/
theorem pull_liftNum {n v m w : Nat} (ρ : ParameterAssignment m w)
    (σ : ParameterSubstitution n v m w) (l : Length) :
    (ρ.extendNum l).pull σ.liftNum = (ρ.pull σ).extendNum l := by
  apply ext
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        change ((σ.numbers i).rename Fin.succ).eval (Fin.cases l ρ.numbers) = _
        rw [NumExpr.rename, NumExpr.eval_subst]
        rfl
  · funext i
    exact apply_weakenNum ρ l (σ.types i)

/-- Lifting a substitution commutes with extending its value-type assignment. -/
theorem pull_liftType {n v m w : Nat} (ρ : ParameterAssignment m w)
    (σ : ParameterSubstitution n v m w) (a : ClosedTy) :
    (ρ.extendType a).pull σ.liftType = (ρ.pull σ).extendType a := by
  apply ext
  · rfl
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact apply_weakenType ρ a (σ.types i)

/-- A numeric beta substitution evaluates by extending the parameter assignment. -/
theorem pull_singleNum {n v : Nat} (ρ : ParameterAssignment n v) (e : NumExpr n) :
    ρ.pull (ParameterSubstitution.singleNum (v := v) e) = ρ.extendNum (e.eval ρ.numbers) := by
  apply ext
  · funext i
    cases i using Fin.cases <;> rfl
  · rfl

/-- A type beta substitution evaluates by extending the parameter assignment. -/
theorem pull_singleType {n v : Nat} (ρ : ParameterAssignment n v) (a : PolyTy n v) :
    ρ.pull (ParameterSubstitution.singleType a) = ρ.extendType (ρ.apply a) := by
  apply ext
  · rfl
  · funext i
    cases i using Fin.cases <;> rfl

end Interop.Cryptol.ParameterAssignment
