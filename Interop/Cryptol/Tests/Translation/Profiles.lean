/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.SemanticCertificate
public import Interop.Cryptol.Model.Resolved

/-! # Admissibility, defined truth, and rejection of erroneous property certificates -/

public section

open Interop.Cryptol Interop.Cryptol.Finite
namespace ProfileTest
noncomputable def meaning : Computation (.arrow .bit .bit) :=
  (Expr.lam (.ite (.var .zero) (.bit true) (.error (.user "outside profile"))) :
    ClosedExpr [] (.arrow .bit .bit)).denote Environment.empty

theorem correct : CorrespondsOn .bit .bit (fun x => x = true) meaning (fun _ => true) := by
  intro x hx
  subst x
  rfl

example (post : Bool → Bool → Prop) :
    DataMeaningContract (b := .bit) .bit meaning (fun x => x = true) post ↔ post true true := by
  rw [correct.contract_iff (fun x => x = true) post (fun _ h => h)]
  simp

example (x : Bool) (hx : x = true) :
    DomainResult.applyContinuous meaning (encodeData .bit x) = encodeData .bit true :=
  (correct.property_iff x hx).mpr rfl

example : DomainResult.applyContinuous meaning (encodeData .bit false) =
    .error (.user "outside profile") := rfl

example : ¬ CorrespondsOn .bit .bit (fun _ => True) meaning (fun _ => true) := by
  intro h
  have he := h false trivial
  change (DomainResult.error (.user "outside profile") : Computation .bit) = .value ⟨true⟩ at he
  cases he

example : ¬ CorrespondsOn .bit .bit (fun _ => True)
    (⊥ : Computation (.arrow .bit .bit)) (fun _ => true) := by
  intro h
  have he := h true trivial
  change (⊥ : Computation .bit) = .value ⟨true⟩ at he
  cases he
end ProfileTest
