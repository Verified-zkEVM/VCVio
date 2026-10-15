/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Resolved
public import PolyFun.Control.Domain.PrefixRecursion

/-!
# Certifying finite recursive source arrays

Resolved recursion has the existing least-fixed-point semantics. A proof that
each generated entry uses only earlier entries identifies it with finite
recursion, without assuming that the surrounding inputs are total.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Resolved

/-- A generated source array is a continuous family of suspended entries. -/
@[expose] noncomputable def recurrenceBody {Γ : List ClosedTy} {a : ClosedTy} {n : Nat}
    (body : Term (.integer :: .seq (.finite n) a :: Γ) a) (ρ : Environment Γ) :
    Computation (.seq (.finite n) a) →𝒄 (Fin n → Computation a) :=
  .ofFun (fun xs i => denote body (Environment.extendContinuous
    (Environment.extendContinuous (ρ, xs), DomainResult.value ⟨(i.val : Int)⟩)))

/-- A checked prefix equation certifies the entire recursive source array. -/
theorem denote_fix_generate {Γ : List ClosedTy} {a : ClosedTy} {n : Nat}
    (body : Term (.integer :: .seq (.finite n) a :: Γ) a) (ρ : Environment Γ)
    (step : (i : Fin n) → (Fin i.val → Computation a) →𝒄 Computation a)
    (hbody : ∀ (xs : Fin n → Computation a) (i : Fin n),
      denote body ((ρ.extend (DomainResult.value xs : Computation (.seq (.finite n) a))).extend
        (.value ⟨(i.val : Int)⟩)) =
        step i (fun j => xs ⟨j.val, j.isLt.trans i.isLt⟩)) :
    denote (Term.fix (Term.generate (.finite n) body)) ρ =
      DomainResult.value (Function.prefixRecursion (fun i => step i)) := by
  change (DomainResult.generateStep (recurrenceBody body ρ)).fix = _
  apply DomainResult.generateStep_fix_eq_prefixRecursion (recurrenceBody body ρ) step
  intro xs
  funext i
  exact hbody xs i

end Interop.Cryptol.Resolved
