/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolySyntax
public import Interop.Cryptol.Model.PolyDomain

/-!
# Denotation of finite polymorphic descriptions

The indexed fold gives every description a continuous function of its local
environment at each valid parameter assignment. Recursive groups tie schemes
together before instantiation, so recursive calls may change their parameters.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Polymorphic

/-- Transport monomorphic computations through equality of their closed types. -/
@[expose] noncomputable def castComputation {a b : ClosedTy}
    (h : a = b) : Computation a →𝒄 Computation b :=
  PointedDomain.cast (congrArg (fun a => PointedDomain.ofType (Computation a)) h)

/-- A finite-width logical primitive at a symbolic width with explicit evidence. -/
@[expose] noncomputable def wordLogic {w : Scope} (length : NumExpr w.numbers)
    (op : BitOp) (valid : w.Entails (.fin length)) (ρ : w.Assignment) :
    (Scheme.mono (.arrow (.seq length .bit)
      (.arrow (.seq length .bit) (.seq length .bit)))).Meaning ρ.val := by
  let n := Classical.choose (valid ρ)
  have hn := Classical.choose_spec (valid ρ)
  apply castComputation (a := .arrow (wordTy n) (.arrow (wordTy n) (wordTy n))) _
    (Primitive.wordLogic n op).denote
  simp only [ParameterAssignment.apply, Ty.instantiate]
  rw [hn]

/-- Interpret one constructor with independently interpreted children. -/
@[expose] noncomputable def denoteOp {w : Scope} (Γ : List w.ValueSort) :
    {s : w.ValueSort} → (op : Op w s) →
    ((p : Fin op.arity) → (ρ : (op.world p).Assignment) →
      Env ρ (op.binders p ++ Γ.map (op.reindex p)) →𝒄 (op.sort p).Meaning ρ.val) →
    (ρ : w.Assignment) → Env ρ Γ →𝒄 s.Meaning ρ.val
  | _, .numAbs _, next, ρ => .ofFun (fun η => DomainResult.valueContinuous
      (fun l => next 0 (ρ.extendNum l) (Env.enterNum ρ l η)))
  | _, .typeAbs _, next, ρ => .ofFun (fun η => DomainResult.valueContinuous
      (fun a => next 0 (ρ.extendType a) (Env.enterType ρ a η)))
  | _, .numApp s a, next, ρ =>
      (s.applyNum a ρ.val).comp ((next 0 ρ).comp (Env.same ρ))
  | _, .typeApp s a, next, ρ =>
      (s.applyType a ρ.val).comp ((next 0 ρ).comp (Env.same ρ))
  | _, .proofAbs _ _, next, ρ =>
      .ofFun (fun η h => next 0 (ρ.assume h.down) (Env.assume ρ h.down η))
  | _, .proofApp c s valid, next, ρ =>
      (ContinuousHom.ofFun (fun f : PLift (c.Holds ρ.val.numbers) → s.Meaning ρ.val =>
        f ⟨valid ρ⟩)).comp ((next 0 ρ).comp (Env.same ρ))
  | _, .bit b, _, _ => .const (.value ⟨b⟩)
  | _, .integer i, _, _ => .const (.value ⟨i⟩)
  | _, .unit, _, _ => .const (.value ⟨()⟩)
  | _, .error s e, _, ρ => .const (s.error ρ.val e)
  | _, .lam _ _, next, ρ => DomainResult.valueContinuous.comp
      (ContinuousHom.curry (.ofFun (fun p => next 0 ρ
        (Env.cons ρ (Env.same ρ p.1, p.2)))))
  | _, .app _ _, next, ρ => .ofFun (fun η => DomainResult.applyContinuous
      (next 0 ρ (Env.same ρ η)) (next 1 ρ (Env.same ρ η)))
  | _, .letE _ _, next, ρ => .ofFun (fun η => next 1 ρ
      (Env.cons ρ (Env.same ρ η, next 0 ρ (Env.same ρ η))))
  | _, .pair _ _, next, ρ => .ofFun (fun η => DomainResult.valueContinuous
      (next 0 ρ (Env.same ρ η), next 1 ρ (Env.same ρ η)))
  | _, .fst _ _, next, ρ =>
      (DomainResult.bind (.ofFun Prod.fst)).comp ((next 0 ρ).comp (Env.same ρ))
  | _, .snd _ _, next, ρ =>
      (DomainResult.bind (.ofFun Prod.snd)).comp ((next 0 ρ).comp (Env.same ρ))
  | _, .generate l _, next, ρ => .ofFun (fun η => DomainResult.valueContinuous
      (fun i : (l.eval ρ.val.numbers).Index => next 0 ρ
        (Env.cons ρ (Env.same ρ η, DomainResult.value ⟨(Length.indexNat i : Int)⟩))))
  | _, .index _ _, next, ρ => .ofFun (fun η => Semantics.index
      (next 0 ρ (Env.same ρ η)) (next 1 ρ (Env.same ρ η)))
  | _, .ite s, next, ρ => .ofFun (fun η => s.conditional ρ.val
      (next 1 ρ (Env.same ρ η), next 2 ρ (Env.same ρ η)) (next 0 ρ (Env.same ρ η)))
  | _, .fix _, next, ρ => ContinuousHom.fixContinuous.comp
      (ContinuousHom.curry (.ofFun (fun p => next 0 ρ
        (Env.cons ρ (Env.same ρ p.1, p.2)))))
  | _, .letRec bindings _, next, ρ =>
      let group : Env ρ (Γ.map id) →𝒄 Env ρ bindings :=
        IPFunctor.ScopedDomain.Env.fixGroup _ (fun i => next i.succ ρ)
      (next 0 ρ).comp ((Env.append ρ).comp ((ContinuousHom.ofFun
        (fun η : Env ρ (Γ.map id) => (group η, η))).comp (Env.same ρ)))
  | _, .bitNot, next, ρ => Semantics.bitNot.comp ((next 0 ρ).comp (Env.same ρ))
  | _, .bitOp op, next, ρ => .ofFun (fun η =>
      Semantics.binary (fun a b => .ok (op.eval a b))
        (next 0 ρ (Env.same ρ η)) (next 1 ρ (Env.same ρ η)))
  | _, .intOp op, next, ρ => .ofFun (fun η => Semantics.binary op.eval
      (next 0 ρ (Env.same ρ η)) (next 1 ρ (Env.same ρ η)))
  | _, .intEq, next, ρ => .ofFun (fun η =>
      Semantics.binary (fun a b : Int => .ok (a == b))
        (next 0 ρ (Env.same ρ η)) (next 1 ρ (Env.same ρ η)))
  | _, .intLt, next, ρ => .ofFun (fun η =>
      Semantics.binary (fun a b : Int => .ok (decide (a < b)))
        (next 0 ρ (Env.same ρ η)) (next 1 ρ (Env.same ρ η)))
  | _, .wordLogic l op h, _, ρ => .const (wordLogic l op h ρ)
  | _, .closed t, _, ρ => .const
      (castComputation (apply_quoteType ρ.val _).symm (Resolved.denote t Environment.empty))

/-- The annotation transports only the result domain, leaving the constructor
algebra and its recursive positions unchanged. -/
@[expose] noncomputable def denoteHead {w : Scope} (Γ : List w.ValueSort)
    {s : w.ValueSort} (h : Head w s)
    (next : (p : Fin h.code.2.arity) → (ρ : (h.code.2.world p).Assignment) →
      Env ρ (h.code.2.binders p ++ Γ.map (h.code.2.reindex p)) →𝒄
        (h.code.2.sort p).Meaning ρ.val) (ρ : w.Assignment) :
    Env ρ Γ →𝒄 s.Meaning ρ.val :=
  (PointedDomain.cast (congrArg (fun s => s.domain ρ.val) h.result)).comp
    (denoteOp Γ h.code.2 next ρ)

/-- Compositional denotation, defined by the generic indexed polynomial fold. -/
@[expose] noncomputable def Term.denote {w : Scope} {Γ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) (ρ : w.Assignment) : Env ρ Γ →𝒄 s.Meaning ρ.val :=
  t.fold (D := fun j => (ρ : j.1.Assignment) → Env ρ j.2.1 →𝒄 j.2.2.Meaning ρ.val)
    (fun _ x _ => .ofFun (fun η => η _ x)) (fun j op next => denoteHead j.2.1 op next) ρ

end Interop.Cryptol.Polymorphic
