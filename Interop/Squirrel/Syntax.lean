/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Interpretation

/-!
# Squirrel's local terms as scoped polynomial syntax

The local terms of the higher-order CCSA logic of Squirrel [LICS23] (§II-A and §II-B) are simply
typed λ-terms with conditionals and Boolean constants, over a declaration environment. Here they
are the terms of one monomorphic `ScopedSignature`, so variables, renaming and capture-avoiding
substitution are PolyFun's.

* `Ty B` is the simple types over base types `B`, with `bool` built in.
* `Label` holds the type labels of LICS23 that the semantics reads (`finite`, `fixed`, `large`),
  and `Ty.HasLabel` lifts a base type's labels `finite` and `fixed` along arrows as LICS23 §II-B.1
  does. `large` is a property of a type's name sampler, so only base types declared `large` have
  it.
* `Ty.arrows τs β` is the curried type `τ₁ → … → τₙ → β`. The logic has no product types, so a
  function of a tuple is a curried function.
* `Decl B` declares the labels of each base type, the names (`n : τ₀ → τ₁` with `τ₀` finite,
  §II-B.2), the honest function symbols and the attacker function symbols. Names and honest
  symbols are indexed by their types, so renaming names never changes the sort of a constructor
  and an honest symbol of an arrow type can be applied without a cast.
* `Kind B` is the sorts: a local type `loc τ`, or `glob`, the sort of global formulas. The local
  signature has no constructor at `glob`; the sort is here so that the global layer
  (`Interop.Squirrel.Global`) is a sum of signatures over the same sorts.
* `localSig D` has application, λ (the only binder), `if-then-else`, `true`, `false`, and the
  constants `=_τ`, `∀_τ`, `∃_τ`, the names and the declared symbols.

LICS23 treats `=_τ`, `∀_τ`, `∃_τ`, names and function symbols as declared variables whose models
are restricted. Here they are constructors, so that every model interprets them, and the
restrictions are part of the interpretation (`Interop.Squirrel.Model`). Arbitrary declared
variables are the free variables of a term.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-A, §II-B and App. A.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

/-- Simple types over base types `B`, with the Boolean type built in. -/
inductive Ty (B : Type) where
  /-- Booleans, interpreted as `{0, 1}` in every model. -/
  | bool
  /-- A declared base type. -/
  | base (b : B)
  /-- Functions, interpreted as full function spaces. -/
  | arrow (dom cod : Ty B)

/-- Labels restricting the interpretation of a base type (LICS23 §II-B.1, App. A). -/
inductive Label where
  /-- The carrier is finite at every security parameter. -/
  | finite
  /-- The carrier does not depend on the security parameter. -/
  | fixed
  /-- Names of the type draw any one value with probability at most `2^{-cη}`, for some `c > 0`
  (LICS23 App. A). -/
  | large

variable {B : Type}

/-- A type has a label when its base types do: LICS23 lifts `finite` and `fixed` along arrows.
Booleans are finite and fixed. `large` restricts the sampler of names of the type itself, which
the samplers of other types do not determine, so Booleans and arrow types are not large. -/
@[expose] def Ty.HasLabel (lab : B → Label → Prop) (l : Label) : Ty B → Prop
  | .bool => l ≠ .large
  | .base b => lab b l
  | .arrow a b => l ≠ .large ∧ a.HasLabel lab l ∧ b.HasLabel lab l

/-- The curried type `τ₁ → … → τₙ → β` of a function of the tuple `τs`. -/
@[expose] def Ty.arrows : List (Ty B) → Ty B → Ty B
  | [], β => β
  | τ :: τs, β => .arrow τ (Ty.arrows τs β)

/-- Booleans and base types, whose values are bitstrings: the types at which a polynomial-time
machine can test equality. -/
@[expose] def Ty.IsGround : Ty B → Prop
  | .arrow _ _ => False
  | _ => True

/-- A declaration environment: labelled base types, names, and honest and attacker function
symbols. -/
structure Decl (B : Type) where
  /-- The labels declared for each base type. -/
  labels : B → Label → Prop
  /-- Names `n : a → b`: random samplings of type `b` indexed by `a`. -/
  Name : Ty B → Ty B → Type
  /-- Names are indexed by finite types (LICS23 §II-B.2). -/
  nameDom_finite : ∀ {a b : Ty B}, Name a b → a.HasLabel labels .finite
  /-- There are finitely many names (LICS23 §II-B.2). -/
  finite_names : Finite ((a : Ty B) × (b : Ty B) × Name a b)
  /-- Honest function symbols of each type, interpreted without randomness. -/
  Fn : Ty B → Type
  /-- Attacker function symbols, interpreted from the attacker's random tape. -/
  Att : Type
  /-- The type of an attacker function symbol. -/
  attTy : Att → Ty B

/-- The sorts of the syntax: local types and the sort of global formulas. -/
inductive Kind (B : Type) where
  /-- Local terms of a type. -/
  | loc (τ : Ty B)
  /-- Global formulas. -/
  | glob

variable {D : Decl B}

/-- The constructors of local terms, at their result sorts. -/
inductive LocalOp (D : Decl B) : Kind B → Type where
  /-- Application `t t'`. -/
  | app (a b : Ty B) : LocalOp D (.loc b)
  /-- Abstraction `λ (x : a). t`. -/
  | lam (a b : Ty B) : LocalOp D (.loc (.arrow a b))
  /-- `if t then t' else t''`. -/
  | ite (a : Ty B) : LocalOp D (.loc a)
  /-- The Boolean `true`. -/
  | tt : LocalOp D (.loc .bool)
  /-- The Boolean `false`. -/
  | ff : LocalOp D (.loc .bool)
  /-- Equality `=_a : a → a → bool`. -/
  | eq (a : Ty B) : LocalOp D (.loc (.arrow a (.arrow a .bool)))
  /-- The quantifier constant `∀_a : (a → bool) → bool`. -/
  | all (a : Ty B) : LocalOp D (.loc (.arrow (.arrow a .bool) .bool))
  /-- The quantifier constant `∃_a : (a → bool) → bool`. -/
  | ex (a : Ty B) : LocalOp D (.loc (.arrow (.arrow a .bool) .bool))
  /-- A declared name `n : τ₀ → τ₁`. -/
  | name {a b : Ty B} (n : D.Name a b) : LocalOp D (.loc (.arrow a b))
  /-- A declared honest function symbol. -/
  | fn {τ : Ty B} (f : D.Fn τ) : LocalOp D (.loc τ)
  /-- A declared attacker function symbol. -/
  | att (f : D.Att) : LocalOp D (.loc (D.attTy f))

/-- Argument counts: application has two, abstraction one, conditionals three. -/
@[expose, reducible] def LocalOp.arity : {s : Kind B} → LocalOp D s → ℕ
  | _, .app _ _ => 2
  | _, .lam _ _ => 1
  | _, .ite _ => 3
  | _, _ => 0

/-- The local signature. Abstraction binds one variable in its body; nothing else binds. -/
@[expose, reducible] def localSig (D : Decl B) : ScopedSignature (Kind B) where
  Op := LocalOp D
  Arg o := Fin o.arity
  binders o := match o with
    | .lam a _ => fun _ => [.loc a]
    | _ => fun _ => []
  sort o := match o with
    | .app a b => Fin.cases (.loc (.arrow a b)) (fun _ => .loc a)
    | .lam _ b => fun _ => .loc b
    | .ite a => Fin.cases (.loc .bool) (fun _ => .loc a)
    | .tt | .ff | .eq _ | .all _ | .ex _ | .name _ | .fn _ | .att _ => Fin.elim0

/-- Local terms of type `τ` in a context of sorts. -/
abbrev LTerm (D : Decl B) (Γ : List (Kind B)) (τ : Ty B) := (localSig D).Term Γ (.loc τ)

namespace LTerm

variable {Γ : List (Kind B)} {a b : Ty B}

/-- Application. -/
@[expose] def app (f : LTerm D Γ (.arrow a b)) (x : LTerm D Γ a) : LTerm D Γ b :=
  .node (.app a b) (Fin.cases f (fun _ => x))

/-- Abstraction over the nearest variable. -/
@[expose] def lam (body : LTerm D (.loc a :: Γ) b) : LTerm D Γ (.arrow a b) :=
  .node (.lam a b) (fun _ => body)

/-- The conditional. -/
@[expose] def ite (c : LTerm D Γ .bool) (t e : LTerm D Γ a) : LTerm D Γ a :=
  .node (.ite a) (Fin.cases c (Fin.cases t (fun _ => e)))

/-- The constant `true`. -/
@[expose] def tt : LTerm D Γ .bool := .node .tt fun p => nomatch p

/-- The constant `false`. -/
@[expose] def ff : LTerm D Γ .bool := .node .ff fun p => nomatch p

/-- Local equality `t = u`. -/
@[expose] def eq (t u : LTerm D Γ a) : LTerm D Γ .bool :=
  app (app (.node (.eq a) fun p => nomatch p) t) u

/-- Local universal quantification `∀ (x : a). φ`, as `∀_a (λ x. φ)`. -/
@[expose] def all (φ : LTerm D (.loc a :: Γ) .bool) : LTerm D Γ .bool :=
  app (.node (.all a) fun p => nomatch p) (lam φ)

/-- Local existential quantification `∃ (x : a). φ`, as `∃_a (λ x. φ)`. -/
@[expose] def ex (φ : LTerm D (.loc a :: Γ) .bool) : LTerm D Γ .bool :=
  app (.node (.ex a) fun p => nomatch p) (lam φ)

/-- A name applied to an index. -/
@[expose] def name (n : D.Name a b) (i : LTerm D Γ a) : LTerm D Γ b :=
  app (.node (.name n) fun p => nomatch p) i

/-- Local implication, as a conditional. -/
@[expose] def imp (φ ψ : LTerm D Γ .bool) : LTerm D Γ .bool := ite φ ψ tt

end LTerm

end Interop.Squirrel
