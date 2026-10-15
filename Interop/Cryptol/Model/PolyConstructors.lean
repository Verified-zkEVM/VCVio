/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolySyntax

/-! # Constructors for finite polymorphic descriptions -/

public section

namespace Interop.Cryptol.Polymorphic.Term

open IPFunctor

variable {w : Scope} {Γ : List w.ValueSort}

/-- A local variable at its binding position. -/
@[expose] def var {s : w.ValueSort} (x : ScopedVar Γ s) : Term w Γ s := .pure x

/-- Normalize the identity parameter action on a local context. -/
@[expose] def same {s : w.ValueSort} (t : Term w Γ s) : Term w (Γ.map id) s :=
  (List.map_id Γ).symm ▸ t

/-- Normalize an identity parameter action below a block of value binders. -/
@[expose] def underSame (Ξ : List w.ValueSort) {s : w.ValueSort}
    (t : Term w (Ξ ++ Γ) s) : Term w (Ξ ++ Γ.map id) s :=
  (congrArg (Ξ ++ ·) (List.map_id Γ)).symm ▸ t

/-- Abstract one numeric parameter, retaining a single finite body. -/
@[expose] def numAbs {s : Scheme (w.numbers + 1) w.types}
    (body : Term w.bindNum
      (Γ.map (Scheme.subst (ParameterSubstitution.weakenNum w.numbers w.types))) s) :
    Term w Γ (.allNum s) := .liftBind (Head.ofOp (.numAbs s)) (fun _ => body)

/-- Instantiate the outer numeric quantifier. -/
@[expose] def numApp {s : Scheme (w.numbers + 1) w.types}
    (f : Term w Γ (.allNum s)) (a : NumExpr w.numbers) :
    Term w Γ (s.subst (ParameterSubstitution.singleNum a)) :=
  .liftBind (Head.ofOp (.numApp s a)) (fun _ => f.same)

/-- Abstract one value-type parameter. -/
@[expose] def typeAbs {s : Scheme w.numbers (w.types + 1)}
    (body : Term w.bindType
      (Γ.map (Scheme.subst (ParameterSubstitution.weakenType w.numbers w.types))) s) :
    Term w Γ (.allType s) := .liftBind (Head.ofOp (.typeAbs s)) (fun _ => body)

/-- Instantiate the outer value-type quantifier. -/
@[expose] def typeApp {s : Scheme w.numbers (w.types + 1)}
    (f : Term w Γ (.allType s)) (a : PolyTy w.numbers w.types) :
    Term w Γ (s.subst (ParameterSubstitution.singleType a)) :=
  .liftBind (Head.ofOp (.typeApp s a)) (fun _ => f.same)

/-- Introduce an erased numeric assumption. -/
@[expose] def proofAbs (c : Constraint w.numbers) {s : w.ValueSort}
    (body : Term (w.assume c) Γ s) : Term w Γ (.guard c s) :=
  .liftBind (Head.ofOp (.proofAbs c s)) (fun _ => body.same)

/-- Discharge an erased numeric assumption using ambient evidence. -/
@[expose] def proofApp {c : Constraint w.numbers} {s : w.ValueSort}
    (f : Term w Γ (.guard c s)) (h : w.Entails c) : Term w Γ s :=
  .liftBind (Head.ofOp (.proofApp c s h)) (fun _ => f.same)

/-- A Boolean literal. -/
@[expose] def bit (b : Bool) : Term w Γ (.mono .bit) :=
  .liftBind (Head.ofOp (.bit b)) (fun p => nomatch p)

/-- An integer literal. -/
@[expose] def integer (i : Int) : Term w Γ (.mono .integer) :=
  .liftBind (Head.ofOp (.integer i)) (fun p => nomatch p)

/-- An explicit error at any stage of a scheme. -/
@[expose] def error (s : w.ValueSort) (e : EvalError) : Term w Γ s :=
  .liftBind (Head.ofOp (.error s e)) (fun p => nomatch p)

/-- A lazy function abstraction over a monomorphic argument. -/
@[expose] def lam {a b : PolyTy w.numbers w.types}
    (body : Term w (.mono a :: Γ) (.mono b)) : Term w Γ (.mono (.arrow a b)) :=
  .liftBind (Head.ofOp (.lam a b)) (fun _ => underSame [.mono a] body)

/-- Lazy function application. -/
@[expose] def app {a b : PolyTy w.numbers w.types}
    (f : Term w Γ (.mono (.arrow a b))) (x : Term w Γ (.mono a)) : Term w Γ (.mono b) :=
  .liftBind (Head.ofOp (.app a b)) (Fin.cases f.same (fun _ => x.same))

/-- A lazy pair. -/
@[expose] def pair {a b : PolyTy w.numbers w.types}
    (x : Term w Γ (.mono a)) (y : Term w Γ (.mono b)) : Term w Γ (.mono (.prod a b)) :=
  .liftBind (Head.ofOp (.pair a b)) (Fin.cases x.same (fun _ => y.same))

/-- Demand a pair and select its first component. -/
@[expose] def fst {a b : PolyTy w.numbers w.types} (x : Term w Γ (.mono (.prod a b))) :
    Term w Γ (.mono a) := .liftBind (Head.ofOp (.fst a b)) (fun _ => x.same)

/-- Demand a pair and select its second component. -/
@[expose] def snd {a b : PolyTy w.numbers w.types} (x : Term w Γ (.mono (.prod a b))) :
    Term w Γ (.mono b) := .liftBind (Head.ofOp (.snd a b)) (fun _ => x.same)

/-- Generate a lazy finite or infinite sequence from its integer index. -/
@[expose] def generate (length : NumExpr w.numbers) {a : PolyTy w.numbers w.types}
    (body : Term w (.mono .integer :: Γ) (.mono a)) : Term w Γ (.mono (.seq length a)) :=
  .liftBind (Head.ofOp (.generate length a)) (fun _ => underSame [.mono .integer] body)

/-- Demand the selected sequence element after checking its integer index. -/
@[expose] def index {length : NumExpr w.numbers} {a : PolyTy w.numbers w.types}
    (xs : Term w Γ (.mono (.seq length a))) (i : Term w Γ (.mono .integer)) :
    Term w Γ (.mono a) := .liftBind (Head.ofOp (.index length a))
      (Fin.cases xs.same (fun _ => i.same))

/-- Bind a possibly polymorphic local value. -/
@[expose] def letE {s t : w.ValueSort} (value : Term w Γ s)
    (body : Term w (s :: Γ) t) : Term w Γ t :=
  .liftBind (Head.ofOp (.letE s t)) (Fin.cases value.same
    (fun _ => underSame [s] body))

/-- Select a branch without demanding the unchosen branch. -/
@[expose] def ite {s : w.ValueSort} (condition : Term w Γ (.mono .bit))
    (yes no : Term w Γ s) : Term w Γ s :=
  .liftBind (Head.ofOp (.ite s)) (Fin.cases condition.same (Fin.cases yes.same (fun _ => no.same)))

/-- Tie one recursive scheme, before choosing its instantiation. -/
@[expose] def fix {s : w.ValueSort} (body : Term w (s :: Γ) s) : Term w Γ s :=
  .liftBind (Head.ofOp (.fix s)) (fun _ => underSame [s] body)

/-- A finite recursive declaration group with a body in the same scope. -/
@[expose] def letRec (bindings : List w.ValueSort) {s : w.ValueSort}
    (rhs : (i : Fin bindings.length) → Term w (bindings ++ Γ) bindings[i])
    (body : Term w (bindings ++ Γ) s) : Term w Γ s :=
  .liftBind (Head.ofOp (.letRec bindings s)) (Fin.cases
    (underSame bindings body) (fun i => underSame bindings (rhs i)))

/-- A finite-width logical function with a symbolic width. -/
@[expose] def wordLogic (length : NumExpr w.numbers) (op : BitOp)
    (h : w.Entails (.fin length)) :
    Term w Γ (.mono (.arrow (.seq length .bit)
      (.arrow (.seq length .bit) (.seq length .bit)))) :=
  .liftBind (Head.ofOp (.wordLogic length op h)) (fun p => nomatch p)

/-- Embed an existing closed resolved source term. -/
@[expose] def closed {a : ClosedTy} (t : Resolved.Term [] a) :
    Term w Γ (.mono (quoteType w.numbers w.types a)) :=
  .liftBind (Head.ofOp (.closed t)) (fun p => nomatch p)

end Interop.Cryptol.Polymorphic.Term
