/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Parameters

/-! # Substitution composition through both kinds of binders -/

public section

namespace Interop.Cryptol

namespace NumExpr

theorem subst_rename {n m k : Nat} (e : NumExpr n) (ρ : Fin n → Fin m)
    (σ : Fin m → NumExpr k) :
    (e.rename ρ).subst σ = e.subst (fun i => σ (ρ i)) := by
  rw [rename, subst_subst]
  rfl

theorem rename_subst {n m k : Nat} (e : NumExpr n) (σ : Fin n → NumExpr m)
    (ρ : Fin m → Fin k) :
    (e.subst σ).rename ρ = e.subst (fun i => (σ i).rename ρ) :=
  subst_subst e σ _

end NumExpr

namespace ParameterSubstitution

/-- Weakening before a lifted numeric substitution equals weakening its result. -/
theorem weakenNum_comp_liftNum {n v m w : Nat} (σ : ParameterSubstitution n v m w) :
    (weakenNum n v).comp σ.liftNum = σ.comp (weakenNum m w) := rfl

/-- Weakening before a lifted type substitution equals weakening its result. -/
theorem weakenType_comp_liftType {n v m w : Nat} (σ : ParameterSubstitution n v m w) :
    (weakenType n v).comp σ.liftType = σ.comp (weakenType m w) := by
  apply ext
  · funext i
    exact (NumExpr.subst_id _).symm
  · rfl

theorem apply_weakenNum {n v m w : Nat} (σ : ParameterSubstitution n v m w)
    (a : PolyTy n v) :
    σ.liftNum.apply ((weakenNum n v).apply a) = (weakenNum m w).apply (σ.apply a) := by
  rw [← apply_comp, weakenNum_comp_liftNum, apply_comp]

theorem apply_weakenType {n v m w : Nat} (σ : ParameterSubstitution n v m w)
    (a : PolyTy n v) :
    σ.liftType.apply ((weakenType n v).apply a) = (weakenType m w).apply (σ.apply a) := by
  rw [← apply_comp, weakenType_comp_liftType, apply_comp]

/-- Numeric lifting preserves composition. -/
theorem liftNum_comp {n v m w k u : Nat} (σ : ParameterSubstitution n v m w)
    (τ : ParameterSubstitution m w k u) : (σ.comp τ).liftNum = σ.liftNum.comp τ.liftNum := by
  apply ext
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        change ((σ.numbers i).subst τ.numbers).rename Fin.succ =
          ((σ.numbers i).rename Fin.succ).subst τ.liftNum.numbers
        rw [NumExpr.rename_subst, NumExpr.subst_rename]
        rfl
  · funext i
    exact (apply_weakenNum τ (σ.types i)).symm

/-- Type lifting preserves composition. -/
theorem liftType_comp {n v m w k u : Nat} (σ : ParameterSubstitution n v m w)
    (τ : ParameterSubstitution m w k u) : (σ.comp τ).liftType = σ.liftType.comp τ.liftType := by
  apply ext
  · rfl
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact (apply_weakenType τ (σ.types i)).symm

/-- Substituting a freshly introduced numeric argument cancels numeric weakening. -/
theorem weakenNum_comp_singleNum {n v : Nat} (e : NumExpr n) :
    (weakenNum n v).comp (singleNum e) = id n v := rfl

/-- Substituting a freshly introduced type argument cancels type weakening. -/
theorem weakenType_comp_singleType {n v : Nat} (a : PolyTy n v) :
    (weakenType n v).comp (singleType a) = id n v := rfl

/-- Numeric application commutes with substitution of the outer parameters. -/
theorem singleNum_comp {n v m w : Nat} (σ : ParameterSubstitution n v m w) (e : NumExpr n) :
    (singleNum e).comp σ = σ.liftNum.comp (singleNum (e.subst σ.numbers)) := by
  apply ext
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        change σ.numbers i = ((σ.numbers i).rename Fin.succ).subst _
        rw [NumExpr.subst_rename]
        exact (NumExpr.subst_id _).symm
  · funext i
    change σ.types i = (singleNum (e.subst σ.numbers)).apply
      ((weakenNum m w).apply (σ.types i))
    rw [← apply_comp, weakenNum_comp_singleNum, apply_id]

/-- Type application commutes with substitution of the outer parameters. -/
theorem singleType_comp {n v m w : Nat} (σ : ParameterSubstitution n v m w) (a : PolyTy n v) :
    (singleType a).comp σ = σ.liftType.comp (singleType (σ.apply a)) := by
  apply ext
  · funext i
    exact (NumExpr.subst_id _).symm
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        change σ.types i = (singleType (σ.apply a)).apply ((weakenType m w).apply (σ.types i))
        rw [← apply_comp, weakenType_comp_singleType, apply_id]

end ParameterSubstitution

namespace Constraint

@[simp] theorem subst_id {n : Nat} (c : Constraint n) : c.subst .var = c := by
  cases c <;> simp only [subst, NumExpr.subst_id]

theorem subst_subst {n m k : Nat} (c : Constraint n) (σ : Fin n → NumExpr m)
    (τ : Fin m → NumExpr k) :
    (c.subst σ).subst τ = c.subst (fun i => (σ i).subst τ) := by
  cases c <;> simp only [subst, NumExpr.subst_subst]

end Constraint
end Interop.Cryptol
