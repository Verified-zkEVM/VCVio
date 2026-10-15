/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.Finite.Basic
public import PolyFun.IPFunctor.Scoped.Size
public import Mathlib.Algebra.BigOperators.Fin
public import ToCslib.Order.PrefixRecursion
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Shared finite recurrence and iteration descriptions

Compilation binds each computed entry before extending the table. Each step
appears once in the syntax and the native evaluator retains the computed word.
A singleton extension stores one reference to its prefix. Description size grows
linearly in the number and stored sizes of the steps.
The entry binding is necessary for sharing: the function-valued array extension
can otherwise recompute its element when the array is indexed repeatedly.
-/

public section

namespace Interop.Cryptol.Finite

/-- Compute entries in order, retaining the preceding prefix. -/
@[expose] def prefixValues {α : Type} (step : (n : Nat) → (Fin n → α) → α) :
    (n : Nat) → Fin n → α
  | 0 => Fin.elim0
  | n + 1 =>
      let xs := prefixValues step n
      let x := step n xs
      Fin.snoc xs x

/-- Every computed coordinate satisfies its strict-prefix equation. -/
theorem prefixValues_apply {α : Type} (step : (n : Nat) → (Fin n → α) → α)
    (n : Nat) (i : Fin n) :
    prefixValues step n i = step i.val (fun j =>
      prefixValues step n ⟨j.val, j.isLt.trans i.isLt⟩) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [prefixValues, Fin.snoc_last, Fin.val_last]
        congr 1
        funext j
        simp [Fin.snoc, j.isLt]
      · rw [prefixValues, Fin.snoc_castSucc, ih i]
        congr 1
        funext j
        simp [Fin.snoc, j.isLt.trans i.isLt]

/-- The shared computation is the unique solution of the prefix equations. -/
theorem prefixValues_eq_prefixRecursion {α : Type}
    (step : (n : Nat) → (Fin n → α) → α) (n : Nat) :
    prefixValues step n = Function.prefixRecursion (fun i : Fin n => step i.val) := by
  apply Function.UsesPrefix.fixedPoint_unique
    (f := fun xs i => step i.val (fun j => xs ⟨j.val, j.isLt.trans i.isLt⟩))
  · intro i x y h
    apply congrArg (step i.val)
    funext j
    exact h ⟨j.val, j.isLt.trans i.isLt⟩ j.isLt
  · funext i
    exact (prefixValues_apply step n i).symm
  · funext i
    exact (Function.prefixRecursion_apply _ i).symm

/-- Compile a prefix recurrence with one binding for each prefix and each new value. -/
@[expose] def Term.prefixTable {Γ : List Ty} {a : Ty}
    (step : (n : Nat) → Term (.seq n a :: Γ) a) : (n : Nat) → Term Γ (.seq n a)
  | 0 => .sequence 0 Fin.elim0
  | n + 1 => .letE (prefixTable step n)
      (.letE (step n) (.snoc (.var (.succ .zero)) (.var .zero)))

/-- Native evaluation computes the finite recurrence without expanding its dependencies. -/
theorem Term.denote_prefixTable {Γ : List Ty} {a : Ty}
    (step : (n : Nat) → Term (.seq n a :: Γ) a) (n : Nat) (ρ : Env Γ) :
    (prefixTable step n).denote ρ = prefixValues (fun k xs => (step k).denote (ρ.extend xs)) n := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      simp only [prefixTable, denote_letE, denote_snoc, denote_var,
        Env.extend_zero, Env.extend_succ, ih]
      rfl

/-- Native syntax size counts stored variables and constructor nodes. -/
@[expose] def Term.nodeCount {Γ : List Ty} {a : Ty} (t : Term Γ a) : Nat :=
  IPFunctor.ScopedSignature.Term.nodeCount (σ := signature) t

@[simp] theorem Term.nodeCount_var {Γ : List Ty} {a : Ty} (v : Var Γ a) :
    (Term.var v).nodeCount = 1 := rfl

@[simp] theorem Term.nodeCount_letE {Γ : List Ty} {a b : Ty}
    (x : Term Γ a) (body : Term (a :: Γ) b) :
    (Term.letE x body).nodeCount = 1 + x.nodeCount + body.nodeCount := by
  simp [nodeCount, Term.letE, IPFunctor.ScopedSignature.Term.nodeCount,
    IPFunctor.IFreeM.fold_liftBind, Fin.sum_univ_two, Nat.add_assoc]
  rfl

@[simp] theorem Term.nodeCount_snoc {Γ : List Ty} {a : Ty} {n : Nat}
    (xs : Term Γ (.seq n a)) (x : Term Γ a) :
    (Term.snoc xs x).nodeCount = 1 + xs.nodeCount + x.nodeCount := by
  simp [nodeCount, Term.snoc, IPFunctor.ScopedSignature.Term.nodeCount,
    IPFunctor.IFreeM.fold_liftBind, Fin.sum_univ_two, Nat.add_assoc]
  rfl

/-- Extending a table adds the step body and five nodes, independently of the prefix length. -/
theorem Term.nodeCount_prefixTable_succ {Γ : List Ty} {a : Ty}
    (step : (n : Nat) → Term (.seq n a :: Γ) a) (n : Nat) :
    (prefixTable step (n + 1)).nodeCount =
      (prefixTable step n).nodeCount + (step n).nodeCount + 5 := by
  simp only [prefixTable, nodeCount_letE, nodeCount_snoc, nodeCount_var]
  omega

/-- A uniform step-size bound gives a linear bound on the stored description. -/
theorem Term.nodeCount_prefixTable_le {Γ : List Ty} {a : Ty}
    (step : (n : Nat) → Term (.seq n a :: Γ) a) (n bound : Nat)
    (hstep : ∀ i < n, (step i).nodeCount ≤ bound) :
    (prefixTable step n).nodeCount ≤ 1 + n * (bound + 5) := by
  induction n with
  | zero => simp [prefixTable, nodeCount, Term.sequence, IPFunctor.ScopedSignature.Term.nodeCount]
  | succ n ih =>
      have hp := ih (fun i hi => hstep i (hi.trans (Nat.lt_succ_self n)))
      have hn := hstep n (Nat.lt_succ_self n)
      rw [nodeCount_prefixTable_succ, Nat.succ_mul]
      omega

/-- Iterate a family of state updates, binding each intermediate result once. -/
@[expose] def Term.iterate {Γ : List Ty} {a : Ty}
    (step : Nat → Term (a :: Γ) a) (seed : Term Γ a) : Nat → Term Γ a
  | 0 => seed
  | n + 1 => .letE (iterate step seed n) (step n)

/-- Each iteration is the next native state update. -/
@[simp] theorem Term.denote_iterate_succ {Γ : List Ty} {a : Ty}
    (step : Nat → Term (a :: Γ) a) (seed : Term Γ a) (n : Nat) (ρ : Env Γ) :
    (iterate step seed (n + 1)).denote ρ =
      (step n).denote (ρ.extend ((iterate step seed n).denote ρ)) := rfl

end Interop.Cryptol.Finite
