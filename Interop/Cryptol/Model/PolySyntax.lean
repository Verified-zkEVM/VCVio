/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyScope
public import Interop.Cryptol.Model.Resolved
public import PolyFun.IPFunctor.Scoped.FamilySubstitution

/-!
# Finite resolved syntax with ordered polymorphic binders

Constructor heads and binder transitions form a PolyFun `ScopedFamily`. A type
or numeric abstraction stores one finite body, not a host-language family of
bodies. Local recursive groups retain every declared scheme and allow calls at
other instantiations. Constraint evidence is explicit and is erased by semantics.
-/

public section

namespace Interop.Cryptol.Polymorphic

/-- Embed a closed type into any pair of symbolic parameter scopes. -/
@[expose] def quoteType (n v : Nat) (a : ClosedTy) : PolyTy n v :=
  a.instantiate (fun l => match l with
    | .finite k => .finite k
    | .infinite => .infinite) Empty.elim

/-- A closed type's quotation has the same meaning at every assignment. -/
@[simp] theorem apply_quoteType {n v : Nat} (ρ : ParameterAssignment n v) (a : ClosedTy) :
    ρ.apply (quoteType n v a) = a := by
  induction a with
  | var x => exact x.elim
  | bit | integer | unit => rfl
  | seq l a ih => cases l <;> simp_all [quoteType, ParameterAssignment.apply, Ty.instantiate,
      NumExpr.eval]
  | prod a b iha ihb | arrow a b iha ihb =>
      simp_all [quoteType, ParameterAssignment.apply, Ty.instantiate]

/-- Resolved constructor heads, with explicit schemes and numeric arguments. -/
inductive Op (w : Scope) : w.ValueSort → Type 1 where
  | numAbs (body : Scheme (w.numbers + 1) w.types) : Op w (.allNum body)
  | numApp (body : Scheme (w.numbers + 1) w.types) (argument : NumExpr w.numbers) :
      Op w (body.subst (ParameterSubstitution.singleNum argument))
  | typeAbs (body : Scheme w.numbers (w.types + 1)) : Op w (.allType body)
  | typeApp (body : Scheme w.numbers (w.types + 1)) (argument : PolyTy w.numbers w.types) :
      Op w (body.subst (ParameterSubstitution.singleType argument))
  | proofAbs (c : Constraint w.numbers) (body : w.ValueSort) : Op w (.guard c body)
  | proofApp (c : Constraint w.numbers) (body : w.ValueSort) (valid : w.Entails c) : Op w body
  | bit (value : Bool) : Op w (.mono .bit)
  | integer (value : Int) : Op w (.mono .integer)
  | unit : Op w (.mono .unit)
  | error (s : w.ValueSort) (error : EvalError) : Op w s
  | lam (a b : PolyTy w.numbers w.types) : Op w (.mono (.arrow a b))
  | app (a b : PolyTy w.numbers w.types) : Op w (.mono b)
  | letE (value result : w.ValueSort) : Op w result
  | pair (a b : PolyTy w.numbers w.types) : Op w (.mono (.prod a b))
  | fst (a b : PolyTy w.numbers w.types) : Op w (.mono a)
  | snd (a b : PolyTy w.numbers w.types) : Op w (.mono b)
  | generate (length : NumExpr w.numbers) (a : PolyTy w.numbers w.types) :
      Op w (.mono (.seq length a))
  | index (length : NumExpr w.numbers) (a : PolyTy w.numbers w.types) : Op w (.mono a)
  | ite (s : w.ValueSort) : Op w s
  | fix (s : w.ValueSort) : Op w s
  | letRec (bindings : List w.ValueSort) (result : w.ValueSort) : Op w result
  | bitNot : Op w (.mono .bit)
  | bitOp (op : BitOp) : Op w (.mono .bit)
  | intOp (op : IntOp) : Op w (.mono .integer)
  | intEq : Op w (.mono .bit)
  | intLt : Op w (.mono .bit)
  | wordLogic (length : NumExpr w.numbers) (op : BitOp) (valid : w.Entails (.fin length)) :
      Op w (.mono (.arrow (.seq length .bit) (.arrow (.seq length .bit) (.seq length .bit))))
  | closed {a : ClosedTy} (source : Resolved.Term [] a) :
      Op w (.mono (quoteType w.numbers w.types a))

namespace Op

/-- Finite recursive positions; a group has one body and one child per declaration. -/
@[expose, reducible] def arity {w : Scope} : {s : w.ValueSort} → Op w s → Nat
  | _, .bit _ | _, .integer _ | _, .unit | _, .error _ _ | _, .wordLogic _ _ _ |
      _, .closed _ => 0
  | _, .numAbs _ | _, .numApp _ _ | _, .typeAbs _ | _, .typeApp _ _ |
      _, .proofAbs _ _ | _, .proofApp _ _ _ | _, .lam _ _ | _, .fst _ _ |
      _, .snd _ _ | _, .generate _ _ | _, .fix _ | _, .bitNot => 1
  | _, .app _ _ | _, .letE _ _ | _, .pair _ _ | _, .index _ _ | _, .bitOp _ |
      _, .intOp _ | _, .intEq | _, .intLt => 2
  | _, .ite _ => 3
  | _, .letRec bindings _ => bindings.length + 1

/-- Parameter context of a child. Only explicit abstractions extend it. -/
@[expose, reducible] def world {w : Scope} : {s : w.ValueSort} →
    (op : Op w s) → Fin op.arity → Scope
  | _, .numAbs _, _ => w.bindNum
  | _, .typeAbs _, _ => w.bindType
  | _, .proofAbs c _, _ => w.assume c
  | _, _, _ => w

/-- Reindex old local schemes when entering a parameter binder. -/
@[expose, reducible] def reindex {w : Scope} : {s : w.ValueSort} →
    (op : Op w s) → (p : Fin op.arity) → w.ValueSort → (op.world p).ValueSort
  | _, .numAbs _, _ => Scheme.subst (ParameterSubstitution.weakenNum w.numbers w.types)
  | _, .typeAbs _, _ => Scheme.subst (ParameterSubstitution.weakenType w.numbers w.types)
  | _, .proofAbs _ _, _ => id
  | _, .numApp _ _, _ | _, .typeApp _ _, _ | _, .proofApp _ _ _, _ |
      _, .bit _, _ | _, .integer _, _ | _, .unit, _ | _, .error _ _, _ |
      _, .lam _ _, _ | _, .app _ _, _ | _, .letE _ _, _ | _, .pair _ _, _ |
      _, .fst _ _, _ | _, .snd _ _, _ | _, .generate _ _, _ | _, .index _ _, _ |
      _, .ite _, _ | _, .fix _, _ | _, .letRec _ _, _ | _, .bitNot, _ |
      _, .bitOp _, _ | _, .intOp _, _ | _, .intEq, _ | _, .intLt, _ |
      _, .wordLogic _ _ _, _ | _, .closed _, _ => id

/-- Variables introduced at each child, nearest first. -/
@[expose, reducible] def binders {w : Scope} : {s : w.ValueSort} →
    (op : Op w s) → (p : Fin op.arity) → List (op.world p).ValueSort
  | _, .lam a _, _ => [.mono a]
  | _, .letE a _, p => Fin.cases [] (fun _ => [a]) p
  | _, .generate _ _, _ => [.mono .integer]
  | _, .fix s, _ => [s]
  | _, .letRec bindings _, _ => bindings
  | _, _, _ => []

/-- The scheme of each child, including partially applied polymorphic expressions. -/
@[expose, reducible] def sort {w : Scope} : {s : w.ValueSort} →
    (op : Op w s) → (p : Fin op.arity) → (op.world p).ValueSort
  | _, .numAbs s, _ | _, .typeAbs s, _ | _, .proofAbs _ s, _ => s
  | _, .numApp s _, _ => .allNum s
  | _, .typeApp s _, _ => .allType s
  | _, .proofApp c s _, _ => .guard c s
  | _, .lam _ b, _ => .mono b
  | _, .app a b, p => Fin.cases (.mono (.arrow a b)) (fun _ => .mono a) p
  | _, .letE a b, p => Fin.cases a (fun _ => b) p
  | _, .pair a b, p => Fin.cases (.mono a) (fun _ => .mono b) p
  | _, .fst a b, _ | _, .snd a b, _ => .mono (.prod a b)
  | _, .generate _ a, _ => .mono a
  | _, .index n a, p => Fin.cases (.mono (.seq n a)) (fun _ => .mono .integer) p
  | _, .ite s, p => Fin.cases (.mono .bit) (fun _ => s) p
  | _, .fix s, _ => s
  | _, .letRec bindings s, p => Fin.cases s (fun i => bindings[i]) p
  | _, .bitNot, _ | _, .bitOp _, _ => .mono .bit
  | _, .intOp _, _ | _, .intEq, _ | _, .intLt, _ => .mono .integer
  | _, .bit _, p | _, .integer _, p | _, .unit, p | _, .error _ _, p |
      _, .wordLogic _ _ _, p | _, .closed _, p => nomatch p

end Op

/-- A constructor head with a checked result annotation. Keeping the annotation
separate makes parameter substitution compute its children without equality casts. -/
structure Head (w : Scope) (s : w.ValueSort) where
  /-- Finite constructor data and its computed result scheme. -/
  code : (t : w.ValueSort) × Op w t
  /-- The computed scheme agrees with the surrounding judgment. -/
  result : code.1 = s

namespace Head

/-- Annotate a constructor with its computed scheme. -/
@[expose, reducible] def ofOp {w : Scope} {s : w.ValueSort} (op : Op w s) : Head w s :=
  ⟨⟨s, op⟩, rfl⟩

end Head

/-- The shared polynomial binding interface of resolved polymorphic syntax. -/
@[expose, reducible] def signature : IPFunctor.ScopedFamily Scope Scope.ValueSort where
  Op := Head
  Arg h := Fin h.code.2.arity
  world h := h.code.2.world
  reindex h := h.code.2.reindex
  binders h := h.code.2.binders
  sort h := h.code.2.sort

/-- Finite well-scoped polymorphic descriptions. -/
abbrev Term := signature.Term

end Interop.Cryptol.Polymorphic
