/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.LogicalRelation
public import Interop.Cryptol.Model.Soundness
public import Interop.Cryptol.Model.Substitution

/-!
# Computational adequacy

The fundamental logical-relation theorem connects the compositional least
fixed point semantics to finite executions of the call-by-name machine.
Semantic environments and syntactic closing substitutions are related
pointwise, including suspended arguments that diverge or raise errors.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol

/-- The semantic environment agrees with a closing syntactic substitution. -/
@[expose] def EnvironmentRelated {Γ : List ClosedTy} (η : Environment Γ)
    (σ : Expr.Substitution Γ []) : Prop := ∀ a v, Related (η a v) (σ v)

/-- Add a related suspended argument to both environments. -/
theorem EnvironmentRelated.cons {Γ : List ClosedTy} {η : Environment Γ}
    {σ : Expr.Substitution Γ []} (h : EnvironmentRelated η σ) {a : ClosedTy}
    {d : Computation a} {arg : Expr [] a} (ha : Related d arg) :
    EnvironmentRelated (η.extend d) (σ.cons arg) := by
  intro b v
  cases v with
  | zero => exact ha
  | succ v => exact h b v

/-- A bit literal agrees with its discrete semantic value. -/
theorem Related.bit (b : Bool) : Related (a := .bit) (DomainResult.value ⟨b⟩)
    (Expr.bit b : ClosedExpr [] .bit) :=
  (StateRelated.value (w := .bit b) rfl).prev rfl

/-- An integer literal agrees with its discrete semantic value. -/
theorem Related.integer (i : Int) :
    Related (a := .integer) (DomainResult.value ⟨i⟩) (Expr.integer i) :=
  (StateRelated.value (w := .integer i) rfl).prev rfl

/-- A related bit can be demanded by a caller that handles either Boolean. -/
theorem StateRelated.bindBit {b : ClosedTy} {d : Computation .bit} {e : ClosedExpr [] .bit}
    (f : Bool → Computation b) (stack : Stack .bit b) (hd : Related d e)
    (hk : ∀ i, StateRelated (f i) (.value (.bit i) stack)) :
    StateRelated (DomainResult.bind (DiscreteOrder.continuousMap f) d) (.eval e stack) := by
  apply StateRelated.bind _ stack hd
  rintro ⟨i⟩ w h
  cases w with
  | bit j =>
      change i = j at h
      subst j
      exact hk i

/-- A related integer can be demanded by a caller that handles each integer. -/
theorem StateRelated.bindInteger {b : ClosedTy} {d : Computation .integer}
    {e : ClosedExpr [] .integer} (f : Int → Computation b) (stack : Stack .integer b)
    (hd : Related d e) (hk : ∀ i, StateRelated (f i) (.value (.integer i) stack)) :
    StateRelated (DomainResult.bind (DiscreteOrder.continuousMap f) d) (.eval e stack) := by
  apply StateRelated.bind _ stack hd
  rintro ⟨i⟩ w h
  cases w with
  | integer j =>
      change i = j at h
      subst j
      exact hk i

/-- Every well-typed core expression preserves the logical relation under
related closing environments. -/
theorem Expr.related_denote {Γ : List ClosedTy} {a : ClosedTy} (e : Expr Γ a)
    (σ : Expr.Substitution Γ []) (η : Environment Γ) (hη : EnvironmentRelated η σ) :
    Related (e.denote η) (e.subst σ) := by
  induction e with
  | var v => exact hη _ v
  | bit b => exact Related.bit b
  | integer i => exact Related.integer i
  | unit => exact (StateRelated.value (w := .unit) trivial).prev rfl
  | error err => exact (StateRelated.error err).prev rfl
  | lam body ih =>
      refine (StateRelated.value (w := .function (body.subst σ.lift)) ?_).prev rfl
      intro x arg hx
      rw [Expr.substOne_subst_lift]
      exact ih (σ.cons arg) (η.extend x) (hη.cons hx)
  | @app Γ a b f x ihf ihx =>
      apply StateRelated.prev (next := .eval (f.subst σ) (.push (.app (x.subst σ)) .done))
        (hs := rfl)
      refine StateRelated.bind (a := .arrow a b) (b := b)
        (.ofFun (fun g : Computation a →𝒄 Computation b =>
        g (x.denote η))) _ (ihf σ η hη) ?_
      intro g w hw
      cases w with
      | function body => exact StateRelated.prev (hw _ _ (ihx σ η hη)) rfl
  | letE x body ihx ihbody =>
      have hbody := ihbody (σ.cons (x.subst σ)) (η.extend (x.denote η))
        (hη.cons (ihx σ η hη))
      rw [← Expr.substOne_subst_lift] at hbody
      exact StateRelated.prev hbody rfl
  | force x next ihx ihn =>
      apply StateRelated.prev (next := .eval (x.subst σ)
        (.push (.force (next.subst σ)) .done)) (hs := rfl)
      refine StateRelated.bind (.const (next.denote η)) _ (ihx σ η hη) ?_
      intro v w _
      exact StateRelated.prev (ihn σ η hη) rfl
  | pair x y ihx ihy =>
      exact (StateRelated.value (w := .pair (x.subst σ) (y.subst σ))
        ⟨ihx σ η hη, ihy σ η hη⟩).prev rfl
  | fst x ih =>
      apply StateRelated.prev (next := .eval (x.subst σ) (.push .fst .done)) (hs := rfl)
      refine StateRelated.bind (.ofFun Prod.fst) _ (ih σ η hη) ?_
      intro v w hw
      cases w with
      | pair left right => exact StateRelated.prev hw.1 rfl
  | snd x ih =>
      apply StateRelated.prev (next := .eval (x.subst σ) (.push .snd .done)) (hs := rfl)
      refine StateRelated.bind (.ofFun Prod.snd) _ (ih σ η hη) ?_
      intro v w hw
      cases w with
      | pair left right => exact StateRelated.prev hw.2 rfl
  | generate l body ih =>
      refine (StateRelated.value (w := .sequence l (body.subst σ.lift)) ?_).prev rfl
      intro i
      rw [Expr.substOne_subst_lift]
      exact ih (σ.cons (.integer (Length.indexNat i)))
        (η.extend (.value ⟨(Length.indexNat i : Int)⟩))
        (hη.cons (Related.integer (Length.indexNat i)))
  | @index Γ a l xs i ihxs ihi =>
      apply StateRelated.prev (next := .eval (xs.subst σ) (.push (.index (i.subst σ)) .done))
        (hs := rfl)
      refine StateRelated.bind (.ofFun (fun vs =>
        Semantics.index (DomainResult.valueContinuous vs) (i.denote η))) _ (ihxs σ η hη) ?_
      intro vs w hw
      cases w with
      | sequence _ body =>
          apply StateRelated.prev (next := .eval (i.subst σ) (.push (.indexInto l body) .done))
            (hs := rfl)
          change StateRelated (Semantics.index (.value vs) (i.denote η)) _
          rw [Semantics.index_value_eq_bind]
          refine StateRelated.bindInteger (b := a) (fun n => match l.checkIndex n with
            | none => .error (.invalidIndex n)
            | some j => vs j) _ (ihi σ η hη) ?_
          intro n
          cases hj : l.checkIndex n with
          | none => exact (StateRelated.error (.invalidIndex n)).prev (by simp [MachineState.step,
              MachineState.resume, hj])
          | some j =>
              have hr := hw j
              rw [l.indexNat_checkIndex n j hj] at hr
              exact StateRelated.prev hr (by simp [MachineState.step, MachineState.resume,
                Expr.start, hj])
  | ite p x y ihp ihx ihy =>
      apply StateRelated.prev (next := .eval (p.subst σ)
        (.push (.branch (x.subst σ) (y.subst σ)) .done)) (hs := rfl)
      change StateRelated (Semantics.conditional (x.denote η, y.denote η) (p.denote η)) _
      rw [Semantics.conditional_eq_bind]
      refine StateRelated.bindBit (fun b => if b then x.denote η else y.denote η) _
        (ihp σ η hη) ?_
      intro b
      cases b
      · exact StateRelated.prev (ihy σ η hη) rfl
      · exact StateRelated.prev (ihx σ η hη) rfl
  | fix body ih =>
      change Related (body.bodyDenote η).fix (.fix (body.subst σ.lift))
      refine (body.bodyDenote η).fix_induction
        (fun d => Related d (.fix (body.subst σ.lift))) trivial ?_ (admissible_related _)
      intro d hd
      have hbody := ih (σ.cons (.fix (body.subst σ.lift))) (η.extend d) (hη.cons hd)
      rw [← Expr.substOne_subst_lift] at hbody
      exact StateRelated.prev hbody rfl
  | bitNot x ih =>
      apply StateRelated.prev (next := .eval (x.subst σ) (.push .bitNot .done)) (hs := rfl)
      refine StateRelated.bindBit (b := .bit) (fun b => .value ⟨!b⟩) _ (ih σ η hη) ?_
      intro b
      exact (StateRelated.value (w := .bit (!b)) rfl).prev rfl
  | bitOp op x y ihx ihy =>
      apply StateRelated.prev (next := .eval (x.subst σ) (.push (.bitLeft op (y.subst σ)) .done))
        (hs := rfl)
      refine StateRelated.bindBit (b := .bit) (fun a =>
        Semantics.binary (fun a b => .ok (op.eval a b))
          (.value ⟨a⟩) (y.denote η)) _ (ihx σ η hη) ?_
      intro a
      apply StateRelated.prev (next := .eval (y.subst σ) (.push (.bitRight op a) .done))
        (hs := rfl)
      refine StateRelated.bindBit (b := .bit) (fun b => .value ⟨op.eval a b⟩) _ (ihy σ η hη) ?_
      intro b
      exact (StateRelated.value (w := .bit (op.eval a b)) rfl).prev rfl
  | intOp op x y ihx ihy =>
      apply StateRelated.prev (next := .eval (x.subst σ) (.push (.intLeft op (y.subst σ)) .done))
        (hs := rfl)
      refine StateRelated.bindInteger (b := .integer) (fun a => Semantics.binary op.eval
        (.value ⟨a⟩) (y.denote η)) _ (ihx σ η hη) ?_
      intro a
      apply StateRelated.prev (next := .eval (y.subst σ) (.push (.intRight op a) .done))
        (hs := rfl)
      refine StateRelated.bindInteger (b := .integer) (fun b => ofExcept (op.eval a b)) _
        (ihy σ η hη) ?_
      intro b
      cases hop : op.eval a b with
      | error err =>
          exact (StateRelated.error err).prev (by
            simp [MachineState.step, MachineState.resume, hop])
      | ok c =>
          exact (StateRelated.value (w := .integer c) rfl).prev (by
            simp [MachineState.step, MachineState.resume, hop])
  | intEq x y ihx ihy =>
      apply StateRelated.prev (next := .eval (x.subst σ) (.push (.eqLeft (y.subst σ)) .done))
        (hs := rfl)
      refine StateRelated.bindInteger (b := .bit) (fun a => Semantics.binary
        (fun a b : Int => .ok (a == b))
        (.value ⟨a⟩) (y.denote η)) _ (ihx σ η hη) ?_
      intro a
      apply StateRelated.prev (next := .eval (y.subst σ) (.push (.eqRight a) .done)) (hs := rfl)
      refine StateRelated.bindInteger (b := .bit) (fun b => .value ⟨a == b⟩) _ (ihy σ η hη) ?_
      intro b
      exact (StateRelated.value (w := .bit (a == b)) rfl).prev rfl
  | intLt x y ihx ihy =>
      apply StateRelated.prev (next := .eval (x.subst σ) (.push (.ltLeft (y.subst σ)) .done))
        (hs := rfl)
      refine StateRelated.bindInteger (b := .bit) (fun a => Semantics.binary
        (fun a b : Int => .ok (decide (a < b))) (.value ⟨a⟩) (y.denote η)) _ (ihx σ η hη) ?_
      intro a
      apply StateRelated.prev (next := .eval (y.subst σ) (.push (.ltRight a) .done))
        (hs := rfl)
      refine StateRelated.bindInteger (b := .bit) (fun b => .value ⟨decide (a < b)⟩) _
        (ihy σ η hη) ?_
      intro b
      exact (StateRelated.value (w := .bit (decide (a < b))) rfl).prev rfl

/-- A closed term is related to its independently defined denotation. -/
theorem Expr.closed_related {a : ClosedTy} (e : Expr [] a) :
    Related (e.denote Environment.empty) e := by
  simpa only [Expr.subst_var] using e.related_denote (fun {_} x => .var x)
    Environment.empty (fun _ x => nomatch x)

/-- Semantic errors are exactly the errors produced in finite execution. -/
theorem Expr.adequacy_error {a : ClosedTy} (e : Expr [] a) (err : EvalError) :
    e.denote Environment.empty = .error err ↔ Evaluates e (.error err) := by
  constructor
  · intro h
    have hr := e.closed_related
    rw [h] at hr
    exact hr
  · exact Evaluates.sound

/-- A defined outer semantic value has a terminating operational witness
with exactly that denotation, including its suspended components. -/
theorem Expr.adequacy_value {a : ClosedTy} (e : Expr [] a) (v : Value a) :
    e.denote Environment.empty = .value v ↔
      ∃ w, Evaluates e (.ok w) ∧ w.denote = v := by
  constructor
  · intro h
    have hr := e.closed_related
    rw [h] at hr
    obtain ⟨w, hw, _⟩ := hr
    refine ⟨w, hw, ?_⟩
    have he := hw.sound
    rw [h] at he
    exact (Sum.inr.inj (WithBot.coe_inj.mp he)).symm
  · rintro ⟨w, hw, rfl⟩
    exact hw.sound

/-- Bottom is precisely the absence of any finite terminating outcome.
An outer sequence or function value can terminate while demands on it diverge. -/
theorem Expr.adequacy_bottom {a : ClosedTy} (e : Expr [] a) :
    e.denote Environment.empty = ⊥ ↔ ∀ r, ¬ Evaluates e r := by
  constructor
  · intro h r
    exact not_evaluates_of_denote_bot h r
  · intro h
    have hr := e.closed_related
    generalize hd : e.denote Environment.empty = d at hr ⊢
    induction d using WithBot.recBotCoe with
    | bot => rfl
    | coe x =>
        cases x with
        | inl err => exact False.elim (h (.error err.value) hr)
        | inr v =>
            obtain ⟨w, hw, _⟩ := hr
            exact False.elim (h (.ok w) hw)

/-- Adequacy holds after every constraint-respecting polymorphic instantiation. -/
theorem Definition.adequacy {schema : Schema} (definition : Definition schema)
    (arguments : schema.Instantiation) :
    Related ((definition.instantiate arguments).denote Environment.empty)
      (definition.instantiate arguments) :=
  (definition.instantiate arguments).closed_related

end Interop.Cryptol
