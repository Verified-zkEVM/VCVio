/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.SourceScope
public import Interop.Cryptol.Model.Reference.Types
public import Interop.Cryptol.Model.Resolved

/-!
# Checked specialization of a reference expression fragment

The elaborator checks instantiated schemes, proof applications, lexical binding,
application types and lambda annotations before constructing intrinsically typed
resolved syntax. It supports nonrecursive global definitions with closed numeric
and type arguments. Unsupported constructs and unsatisfied constraints are errors.
The acceptance certificate retains the exact input and output of this typed gate;
it does not assert correctness of the external frontend or a full Cryptol semantics.
-/

public section

namespace Interop.Cryptol.Translation.SourceElaboration

open Reference

/-- A resolved expression together with its checked result type. -/
abbrev TypedTerm (Γ : List ClosedTy) := (a : ClosedTy) × Resolved.Term Γ a

/-- Lift a first-order validation result into the universe of scoped syntax. -/
@[expose] def liftCheck {ε α : Type} : Except ε α → Except ε (ULift.{1} α)
  | .ok value => .ok ⟨value⟩
  | .error error => .error error

/-- Lexical source identities paired with typed de Bruijn positions. -/
abbrev Names (Γ : List ClosedTy) := List ((a : ClosedTy) × (Name × Var Γ a))

/-- Enter a value binder without merging distinct source identities. -/
@[expose] def Names.extend {Γ : List ClosedTy} (names : Names Γ) (name : Name) (a : ClosedTy) :
    Names (a :: Γ) :=
  ⟨a, name, .zero⟩ :: names.map (fun ⟨b, n, v⟩ => ⟨b, n, .succ v⟩)

/-- Translate supported closed source types, retaining sequence lengths. -/
@[expose] def coreType : ValueType → Except String ClosedTy
  | .bit => .ok .bit
  | .integer => .ok .integer
  | .seq n a => return .seq n (← coreType a)
  | .function a b => return .arrow (← coreType a) (← coreType b)
  | _ => .error "unsupported aggregate type in the scalar elaboration fragment"

/-- Resolve a source annotation under the current checked type arguments. -/
@[expose] def annotation (fuel : Nat) (params : TypeEnvironment) (t : TypeExpr) :
    Except String ClosedTy := do
  coreType (← t.evaluate fuel params >>= TypeValue.value?)

/-- Typed transport requires an actual equality proof, never Boolean equality alone. -/
@[expose] def expect {Γ : List ClosedTy} (a : ClosedTy) (t : TypedTerm Γ) :
    Except String (Resolved.Term Γ a) :=
  if h : t.1 = a then .ok (h ▸ t.2) else .error "expression type mismatch"

/-- Collect ordered type arguments followed by proof applications of a named declaration. -/
@[expose] def instantiation : Reference.Expr → Option (Name × List TypeExpr × Nat)
  | .var name => some (name, [], 0)
  | .typeApp f t => do
      let (name, args, proofs) ← instantiation f
      if proofs != 0 then none else some (name, args ++ [t], 0)
  | .proofApp f => do
      let (name, args, proofs) ← instantiation f
      some (name, args, proofs + 1)
  | _ => none

/-- Remove exactly the instantiated parameter and proof binders of a global body. -/
@[expose] def instantiateBody (fuel : Nat) (params : TypeEnvironment) :
    List Parameter → List TypeExpr → Reference.Expr → Except String Reference.Expr
  | p :: ps, constraints, .typeAbs q body =>
      if p = q then instantiateBody fuel params ps constraints body
      else .error "definition parameter differs from its scheme"
  | [], _ :: cs, .proofAbs constraint body => do
      unless (← constraint.evaluate fuel params >>= TypeValue.proposition?) do
        throw "unsatisfied definition constraint"
      instantiateBody fuel params [] cs body
  | [], [], body => .ok body
  | _, _, _ => .error "definition binders differ from its scheme"

/-- Recognize only explicitly supported, fully instantiated official primitive identities. -/
@[expose] def primitive {Γ : List ClosedTy} (name : Name) (args : List TypeValue) :
    Except String (TypedTerm Γ) := do
  unless name.origin == s!"Cryptol::{name.text}" ||
      name.origin == s!"(Cryptol::{name.text})" do throw "unrecognized primitive identity"
  match name.text, args with
  | "number", [.number (.finite n), .value .integer] =>
      return ⟨.integer, .integer n⟩
  | "^", [.value (.seq (.finite n) .bit)] =>
      return ⟨_, .primitive (.wordLogic n .xor)⟩
  | ">>", [.number (.finite n), .value .integer, .value .bit] =>
      return ⟨_, .primitive (.shift n .right)⟩
  | ">>>", [.number (.finite n), .value .integer, .value .bit] =>
      return ⟨_, .primitive (.shift n .rotateRight)⟩
  | _, _ => throw "unsupported primitive or primitive instantiation"

/-- Specialize and elaborate the supported expression fragment at a finite checking budget. -/
@[expose] def elaborate : Nat → List Decl → TypeEnvironment →
    {Γ : List ClosedTy} → Names Γ → Reference.Expr → Except String (TypedTerm Γ)
  | 0, _, _, _, _, _ => .error "expression elaboration budget exhausted"
  | fuel + 1, globals, params, Γ, names, expression => do
      match expression with
      | .abs name type body =>
          let ⟨a⟩ ← liftCheck (annotation fuel params type)
          let ⟨b, term⟩ ← elaborate fuel globals params (names.extend name a) body
          return ⟨.arrow a b, .lam term⟩
      | .app function argument =>
          let f ← elaborate fuel globals params names function
          let x ← elaborate fuel globals params names argument
          match f with
          | ⟨.arrow a b, f⟩ => return ⟨b, .app f (← expect a x)⟩
          | _ => throw "application requires a function"
      | .ite condition yes no =>
          let c ← elaborate fuel globals params names condition >>= expect .bit
          let ⟨a, y⟩ ← elaborate fuel globals params names yes
          let n ← elaborate fuel globals params names no >>= expect a
          return ⟨a, .ite c y n⟩
      | _ =>
          let some (name, arguments, proofs) := instantiation expression
            | throw "unsupported expression constructor"
          match names.find? (fun entry => entry.2.1.id == name.id) with
          | some ⟨a, known, v⟩ =>
              unless known = name && arguments.isEmpty && proofs == 0 do
                throw "invalid lexical variable instantiation"
              return ⟨a, .var v⟩
          | none =>
              let some declaration := globals.find? (fun d => d.name.id == name.id)
                | throw "unresolved or recursive global declaration"
              unless declaration.name = name do throw "inconsistent global identity"
              let ⟨args⟩ ← liftCheck (arguments.mapM (fun t => t.evaluate fuel params))
              let schema := declaration.schema
              unless proofs == schema.constraints.length do throw "wrong proof-argument count"
              let ⟨(instantiated, type)⟩ ← liftCheck (schema.instantiate fuel [] args)
              let ⟨resultType⟩ ← liftCheck (coreType type)
              let result ← match declaration.definition with
                | .primitive => primitive name args
                | .expression body => do
                    let ⟨body⟩ ← liftCheck (instantiateBody fuel instantiated schema.parameters
                      schema.constraints body)
                    elaborate fuel globals instantiated ([] : Names Γ) body
                | .foreign _ _ => throw "foreign definitions need a separate correspondence"
              return ⟨resultType, ← expect resultType result⟩

/-- Complete source validation precedes expression elaboration.
Recursive groups stay unsupported. -/
@[expose] def check (bundle : SourceBundle) (expression : Reference.Expr) (fuel : Nat := 1000) :
    Except ImportError (TypedTerm []) := do
  let _ ← liftCheck (bundle.checkScopes fuel)
  let globals := bundle.groups.filterMap fun
    | .nonrecursive declaration => some declaration
    | .recursive _ => none
  (elaborate fuel globals [] [] expression).mapError (⟨["expression"], ·⟩)

/-- Acceptance of the expression-typing gate for a particular intrinsically typed output. -/
structure Certificate (bundle : SourceBundle) (expression : Reference.Expr) where
  /-- Explicit checking budget; exhaustion rejects rather than supplying a default. -/
  budget : Nat
  /-- Checked result type and resolved term. -/
  result : TypedTerm []
  /-- Kernel-checkable connection to the exact input bundle and expression. -/
  accepted : check bundle expression budget = .ok result

/-- A successful elaboration retains its acceptance equation. -/
def certify (bundle : SourceBundle) (expression : Reference.Expr) (fuel : Nat := 1000) :
    Except ImportError (Certificate bundle expression) :=
  match h : check bundle expression fuel with
  | .ok result => .ok ⟨fuel, result, h⟩
  | .error error => .error error

end Interop.Cryptol.Translation.SourceElaboration
