/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Numeric

/-!
# The typechecked Cryptol reference syntax

This finite presentation retains the constructor distinctions of Cryptol
3.6.0's `TypeCheck.AST`. Names use frontend identities, not display spellings.
Types and expressions here are input syntax; acceptance requires a separate
scope, kind, and typing check. Proof application has no proof payload upstream.
-/

public section

namespace Interop.Cryptol.Reference

/-- Kinds accepted by the reference fragment. -/
inductive Kind where
  | number | value | proposition
  deriving DecidableEq, Repr

/-- A declaration identity and its diagnostic source spelling. -/
structure Name where
  /-- Unique identity within one exported bundle. -/
  id : Nat
  /-- Unqualified source spelling, never used for resolving variables. -/
  text : String
  /-- Qualified source spelling for diagnostics and provenance. -/
  origin : String
  deriving DecidableEq, Repr

/-- A parameter binder retains its identity and kind. -/
structure Parameter where
  /-- Unique numeric/type parameter identity. -/
  id : Nat
  /-- The kind checked when applying this binder. -/
  kind : Kind
  deriving DecidableEq, Repr

/-- Upstream selectors retain their optional shape annotations. -/
inductive Selector where
  | tuple (index : Nat) (size : Option Nat)
  | record (field : String) (fields : Option (List String))
  | list (index : Nat) (size : Option Nat)
  deriving DecidableEq, Repr

/-- Source type expressions retain synonyms and named record fields.
Constructor spellings are the pinned frontend's `TC`, `TF`, and `PC` names. -/
inductive TypeExpr where
  | var (parameter : Parameter)
  | number (value : Nat)
  | constructor (name : String) (arguments : List TypeExpr)
  | tuple (size : Nat) (fields : List TypeExpr)
  | record (fields : List (String × TypeExpr))
  | synonym (name : Name) (arguments : List TypeExpr) (body : TypeExpr)
  | has (selector : Selector) (arguments : List TypeExpr)
  deriving Repr, Inhabited

/-- An ordered prenex scheme, including every class and numeric obligation. -/
structure Schema where
  /-- Numeric and type parameters in source order. -/
  parameters : List Parameter
  /-- The proof assumptions following the parameter binders. -/
  constraints : List TypeExpr
  /-- The monomorphic result type under these binders. -/
  body : TypeExpr
  deriving Repr

mutual

  /-- Finite reference expressions with explicit binders and declaration groups. -/
  inductive Expr where
    | list (element : TypeExpr) (elements : List Expr)
    | tuple (elements : List Expr)
    | record (fields : List (String × Expr))
    | select (value : Expr) (selector : Selector)
    | update (type : TypeExpr) (value : Expr) (selector : Selector) (replacement : Expr)
    | ite (condition yes no : Expr)
    | comprehension (length element : TypeExpr) (body : Expr) (branches : List (List Match))
    | var (name : Name)
    | typeAbs (parameter : Parameter) (body : Expr)
    | typeApp (function : Expr) (argument : TypeExpr)
    | app (function argument : Expr)
    | abs (name : Name) (argument : TypeExpr) (body : Expr)
    | proofAbs (constraint : TypeExpr) (body : Expr)
    | proofApp (function : Expr)
    | whereE (body : Expr) (groups : List DeclGroup)
    | guards (type : TypeExpr) (branches : List (List TypeExpr × Expr))
    deriving Repr

  /-- One sequential comprehension binding. Parallel branches have separate scopes. -/
  inductive Match where
    | from (name : Name) (length element : TypeExpr) (source : Expr)
    | letE (declaration : Decl)
    deriving Repr

  /-- Declaration definitions distinguish primitives and pure foreign fallbacks. -/
  inductive Definition where
    | primitive
    | expression (body : Expr)
    | foreign (interface : String) (body : Option Expr)
    deriving Repr

  /-- A named declaration with its full source scheme. -/
  inductive Decl where
    | mk (name : Name) (schema : Schema) (definition : Definition)
    deriving Repr

  /-- Recursive declarations form a single simultaneous group. -/
  inductive DeclGroup where
    | nonrecursive (declaration : Decl)
    | recursive (declarations : List Decl)
    deriving Repr

end

/-- The identity declared by a source declaration. -/
@[expose] def Decl.name : Decl → Name
  | .mk name _ _ => name

/-- The complete scheme of a source declaration. -/
@[expose] def Decl.schema : Decl → Schema
  | .mk _ schema _ => schema

/-- The implementation of a source declaration. -/
@[expose] def Decl.definition : Decl → Definition
  | .mk _ _ definition => definition

/-- The declarations introduced by a group, in their exported order. -/
@[expose] def DeclGroup.declarations : DeclGroup → List Decl
  | .nonrecursive declaration => [declaration]
  | .recursive declarations => declarations

end Interop.Cryptol.Reference
