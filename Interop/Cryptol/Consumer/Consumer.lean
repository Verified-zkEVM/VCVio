/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunCryptol.Translation.DataCertificate
import PolyFunCryptol.Translation.Finite.Loop
import PolyFunCryptol.Model.ResolvedSequences
import PolyFunCryptol.Model.Recurrence
import PolyFunCryptol.Translation.PolymorphicExamples
import PolyFunCryptol.Model.PolySubstitutionSemantics
import PolyFunCryptol.Model.Numeric
import PolyFunCryptol.Model.Records
import PolyFunCryptol.Model.Comprehensions
import PolyFunCryptol.Model.StructuralLogic
import PolyFunCryptol.Model.StructuralRing

/-!
# Independent public API consumer

A separate package supplies its own specification without opening implementation
bodies or importing any cryptographic interpretation.
-/

open Cryptol Cryptol.Finite

example {n m : Nat} (e : NumericExpr n) (σ : Fin n → NumericExpr m)
    (ρ : Fin m → Option Length) :
    (e.subst σ).eval ρ = e.eval (fun i => (σ i).eval ρ) :=
  e.eval_subst σ ρ

example {Γ fields : List ClosedTy} {a : ClosedTy} (index : Var fields a)
    (old : Expr Γ (Record.type fields)) (value : Expr Γ a) (ρ : Environment Γ) :
    (Record.select index (Record.update index old value)).denote ρ = value.denote ρ :=
  Record.denote_select_update index old value ρ

example {Γ : List ClosedTy} {a : ClosedTy} (shape : LogicType a)
    (op : BitOp) (x y : Expr Γ a) (ρ : Environment Γ) :
    (shape.binary op x y).denote ρ = shape.binarySem op (x.denote ρ) (y.denote ρ) :=
  shape.denote_binary op x y ρ

example {Γ : List ClosedTy} {a : ClosedTy} (shape : RingType a)
    (op : RingOp) (x y : Expr Γ a) (ρ : Environment Γ) :
    (shape.binary op x y).denote ρ = shape.binarySem op (x.denote ρ) (y.denote ρ) :=
  shape.denote_binary op x y ρ

example {a b : Finite.Ty} (ha : DataShape a) (hb : DataShape b)
    (t : Resolved.Term [] (.arrow a.core b.core)) (g : a.Native → b.Native)
    (h : ∀ x, (t.denote Resolved.native IPFunctor.ScopedSignature.Env.empty).bind
      (fun f => f (ha.native x)) = hb.native (g x))
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop) :
    DataContract ha hb (Resolved.denote t Environment.empty) pre post ↔
      ∀ x, pre x → post x (g x) :=
  (Resolved.dataCertificate ha hb t g h).contract_iff pre post

example {Γ : List ClosedTy} (start : Int) (n : Nat) (ρ : Environment Γ) :
    Resolved.denote (Resolved.Term.range start n) ρ =
      DomainResult.value (fun i : Fin n => DomainResult.value ⟨start + (i.val : Int)⟩) :=
  Resolved.denote_range start n ρ

example {Γ Δ : List Finite.Ty} {a : Finite.Ty} (e : Finite.Term Γ a)
    (θ : Finite.signature.Substitution Γ Δ) (ρ : Env Δ) :
    Finite.Term.denote (e.subst θ) ρ = e.denote (fun _ v => Finite.Term.denote (θ v) ρ) :=
  Finite.Term.denote_subst e θ ρ

example {Γ : List Finite.Ty} {a : Finite.Ty}
    (step : (n : Nat) → Finite.Term (.seq n a :: Γ) a) (n bound : Nat)
    (h : ∀ i < n, (step i).nodeCount ≤ bound) :
    (Finite.Term.prefixTable step n).nodeCount ≤ 1 + n * (bound + 5) :=
  Finite.Term.nodeCount_prefixTable_le step n bound h

example (n : Nat) (pre : (BitVec n × BitVec n) → Prop)
    (post : (BitVec n × BitVec n) → BitVec n → Prop) :
    DataContract (.prod (.word n) (.word n)) (.word n)
      (PolymorphicExamples.xorInterface.observe Polymorphic.Examples.xor n) pre post ↔
        ∀ x, pre x → post x (x.1 ^^^ x.2) :=
  PolymorphicExamples.xor_contract n pre post

example {w : Polymorphic.Scope} {Γ : List w.ValueSort}
    {a b : PolyTy w.numbers w.types} (ρ : w.Assignment)
    (body : Polymorphic.Term w (.mono a :: Γ) (.mono b))
    (value : Polymorphic.Term w Γ (.mono a)) (η : Polymorphic.Env ρ Γ) :
    (Polymorphic.Term.app (.lam body) value).denote ρ η =
      body.denote ρ (Polymorphic.Env.cons ρ (η, value.denote ρ η)) :=
  Polymorphic.Term.denote_beta ρ body value η

example {w : Polymorphic.Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (t : Polymorphic.Term w Γ s) (r : IPFunctor.ScopedSignature.Renaming Γ Δ)
    (ρ : w.Assignment) (η : Polymorphic.Env ρ Δ) :
    Polymorphic.Term.denote (t.rename r) ρ η =
      t.denote ρ (Polymorphic.Env.rename ρ r η) :=
  Polymorphic.Term.denote_rename t r ρ η

example {a b : Finite.Ty} {ha : DataShape a} {hb : DataShape b}
    {valid : a.Native → Prop} {meaning : Computation (.arrow a.core b.core)}
    {implementation : a.Native → b.Native}
    (h : CorrespondsOn ha hb valid meaning implementation)
    (pre : a.Native → Prop) (post : a.Native → b.Native → Prop)
    (admissible : ∀ x, pre x → valid x) :
    DataContract ha hb meaning pre post ↔ ∀ x, pre x → post x (implementation x) :=
  h.contract_iff pre post admissible

open Polymorphic in
example {w z : Scope} {Γ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) (μ : Scope.Map w z) (ρ : z.Assignment) (η : Env (μ.pull ρ) Γ) :
    PointedDomain.cast (Scheme.domain_subst s μ.parameters ρ.val)
      ((Term.parameters μ t).denote ρ (Env.parameters μ ρ η)) =
        t.denote (μ.pull ρ) η :=
  Term.denote_parameters t μ ρ η

open Polymorphic in
example {w : Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) (θ : signature.Substitution Γ Δ) (ρ : w.Assignment) (η : Env ρ Δ) :
    (t.subst θ).denote ρ η = t.denote ρ (Env.substitute ρ θ η) :=
  Term.denote_subst t θ ρ η

open Polymorphic in
example {w : Scope} {Γ : List w.ValueSort} {s : w.ValueSort} (t : Term w Γ s) :
    HEq (Term.parameters (Scope.Map.id w) t) t := by simp
