/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyLaws

/-!
# Checked observations of a fully instantiated scheme

A specialization records the ordered numeric, type and proof arguments leading
to one monomorphic result. It describes an observation of a staged computation;
it does not replace the finite source by a host-language family of syntax.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Polymorphic

/-- A complete, ordered instantiation with explicit evidence for every guard. -/
inductive Specialization : {n v : Nat} → Scheme n v → ParameterAssignment n v → ClosedTy → Type
  | mono {n v} (a : PolyTy n v) (ρ : ParameterAssignment n v) :
      Specialization (.mono a) ρ (ρ.apply a)
  | num {n v} {s : Scheme (n + 1) v} {ρ : ParameterAssignment n v} {a : ClosedTy}
      (l : Length) (next : Specialization s (ρ.extendNum l) a) :
      Specialization (.allNum s) ρ a
  | type {n v} {s : Scheme n (v + 1)} {ρ : ParameterAssignment n v} {a : ClosedTy}
      (b : ClosedTy) (next : Specialization s (ρ.extendType b) a) :
      Specialization (.allType s) ρ a
  | proof {n v} {s : Scheme n v} {ρ : ParameterAssignment n v} {a : ClosedTy}
      (c : Constraint n) (valid : c.Holds ρ.numbers) (next : Specialization s ρ a) :
      Specialization (.guard c s) ρ a

namespace Specialization

/-- Demand the quantifiers in order, erasing proof arguments and preserving errors. -/
@[expose] noncomputable def run : {n v : Nat} → {s : Scheme n v} →
    {ρ : ParameterAssignment n v} → {a : ClosedTy} →
    Specialization s ρ a → (s.Meaning ρ →𝒄 Computation a)
  | _, _, _, _, _, .mono _ _ => .id
  | _, _, _, _, _, .num l next =>
      DomainResult.elim DomainResult.error (.ofFun (fun f => next.run (f l)))
  | _, _, _, _, _, .type b next =>
      DomainResult.elim DomainResult.error (.ofFun (fun f => next.run (f b)))
  | _, _, _, _, _, .proof _ h next => next.run.comp (.ofFun (fun f => f ⟨h⟩))

/-- Full instantiation cannot turn divergence into a result. -/
@[simp] theorem run_bot {n v : Nat} {s : Scheme n v} {ρ : ParameterAssignment n v}
    {a : ClosedTy} (i : Specialization s ρ a) : i.run ⊥ = ⊥ := by
  induction i with
  | mono => rfl
  | num => rfl
  | type => rfl
  | proof _ _ _ ih => exact ih

/-- Full instantiation preserves errors from any remaining stage. -/
@[simp] theorem run_error {n v : Nat} {s : Scheme n v} {ρ : ParameterAssignment n v}
    {a : ClosedTy} (i : Specialization s ρ a) (e : EvalError) :
    i.run (s.error ρ e) = DomainResult.error e := by
  induction i with
  | mono => rfl
  | num => rfl
  | type => rfl
  | proof _ _ _ ih => exact ih

end Specialization

/-- Observe a finite description at a checked full instantiation. -/
@[expose] noncomputable def Term.observe {w : Scope} {Γ : List w.ValueSort}
    {s : w.ValueSort} {a : ClosedTy} (t : Term w Γ s) (ρ : w.Assignment)
    (i : Specialization s ρ.val a) : Env ρ Γ →𝒄 Computation a :=
  i.run.comp (t.denote ρ)

end Interop.Cryptol.Polymorphic
