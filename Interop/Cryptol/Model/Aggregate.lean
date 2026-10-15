/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.SequenceLaws
public import Interop.Cryptol.Model.WordSemantics

/-!
# Concrete aggregate arithmetic and integer comparison

Array arithmetic demands both outer constructors from left to right and then
suspends the element operations, including at length zero. This differs from
a comprehension, which constructs its result without demanding its generator.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- Integer comparison with explicit left-to-right demands. -/
@[expose] def Expr.intLe {Γ : List ClosedTy} (x y : Expr Γ .integer) : Expr Γ .bit :=
  .force x (.force y (.bitNot (.intLt y x)))

/-- Direct integer less-than-or-equal semantics. -/
@[expose] noncomputable def Semantics.intLe : Computation .integer →𝒄
    (Computation .integer →𝒄 Computation .bit) :=
  binary (fun x y : Int => .ok (decide (x ≤ y)))

/-- The represented integer comparison. -/
@[simp] theorem Semantics.intLe_values (x y : Int) :
    intLe (.value ⟨x⟩) (.value ⟨y⟩) = .value ⟨decide (x ≤ y)⟩ := rfl

/-- The lowering retains errors and bottom as well as total comparisons. -/
theorem Expr.denote_intLe {Γ : List ClosedTy} (x y : Expr Γ .integer) (ρ : Environment Γ) :
    (intLe x y).denote ρ = Semantics.intLe (x.denote ρ) (y.denote ρ) := by
  change DomainResult.force (x.denote ρ) (DomainResult.force (y.denote ρ)
    (Semantics.bitNot (Semantics.binary (fun a b : Int => .ok (decide (a < b)))
      (y.denote ρ) (x.denote ρ)))) = _
  generalize x.denote ρ = dx
  generalize y.denote ρ = dy
  induction dx using DomainResult.inductionOn with
  | bot => rfl
  | error e => rfl
  | value a =>
      induction dy using DomainResult.inductionOn with
      | bot => rfl
      | error e => rfl
      | value b =>
          change DomainResult.value ⟨!(decide (b.value < a.value))⟩ =
            (DomainResult.value ⟨decide (a.value ≤ b.value)⟩ : Computation .bit)
          apply congrArg DomainResult.value
          apply congrArg DiscreteOrder.mk
          by_cases h : a.value ≤ b.value
          · have hn : ¬ b.value < a.value := by omega
            simp [h, hn]
          · have hn : b.value < a.value := by omega
            simp [h, hn]

/-- Pointwise word arithmetic with strict outer array demands. -/
@[expose] noncomputable def Semantics.wordArrayArithmetic (count width : Nat) (op : IntOp) :
    Computation (.seq (.finite count) (wordTy width)) →𝒄
      (Computation (.seq (.finite count) (wordTy width)) →𝒄
        Computation (.seq (.finite count) (wordTy width))) :=
  .ofFun (fun x => .ofFun (fun y => DomainResult.force x (DomainResult.force y
    (DomainResult.valueContinuous (fun i : Fin count =>
      wordArithmetic width op (indexAt x i.val) (indexAt y i.val))))))

/-- Lower concrete array arithmetic without changing the aggregate demand order. -/
@[expose] def Expr.wordArrayArithmetic {Γ : List ClosedTy} {count width : Nat} (op : IntOp)
    (x y : Expr Γ (.seq (.finite count) (wordTy width))) :
    Expr Γ (.seq (.finite count) (wordTy width)) :=
  .force x (.force y (.generate (.finite count)
    (.wordOp op (.index x.weaken (.var .zero)) (.index y.weaken (.var .zero)))))

/-- Concrete aggregate arithmetic lowers correctly on arbitrary partial inputs. -/
theorem Expr.denote_wordArrayArithmetic {Γ : List ClosedTy} {count width : Nat} (op : IntOp)
    (x y : Expr Γ (.seq (.finite count) (wordTy width))) (ρ : Environment Γ) :
    (wordArrayArithmetic op x y).denote ρ =
      Semantics.wordArrayArithmetic count width op (x.denote ρ) (y.denote ρ) := by
  simp only [wordArrayArithmetic, denote_force, denote_generate,
    denote_wordArithmetic_sem, denote_index, denote_weaken, denote_var]
  rfl

end Interop.Cryptol
