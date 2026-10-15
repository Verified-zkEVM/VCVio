/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.SourceBundle
public import Interop.Cryptol.Model.Reference.Kinds

/-!
# Scope and kind validation of imported declaration graphs

Top-level groups are checked in dependency order. A nonrecursive declaration
cannot refer to itself or to a later group; recursive declarations see their
entire group. Parallel comprehension branches are checked independently before
their bound names are combined for the body. This gate establishes scope and
kind validity, separately from expression typing and semantic correspondence.
-/

public section

namespace Interop.Cryptol.Translation

open Reference

private def addNames (bound names : List Reference.Name) : Except String (List Reference.Name) := do
  let result := names ++ bound
  unless (result.map Reference.Name.id).Nodup do throw "duplicate value-binding identity"
  return result

private def checkSelector : Selector → Except String Unit
  | .tuple i (some n) | .list i (some n) =>
      if i < n then .ok () else .error "selector is outside its annotated shape"
  | .record field (some names) => do
      unless names.Nodup && names.contains field do throw "invalid record selector annotation"
  | _ => .ok ()

mutual

  private def checkExpression : Nat → List Reference.Name → List Parameter →
      Reference.Expr → Except String Unit
    | 0, _, _, _ => .error "scope-checking budget exhausted"
    | fuel + 1, bound, params, e => do
        let child := checkExpression fuel bound params
        let type := TypeExpr.checkKind fuel params
        match e with
        | .list t es => type .value t; es.forM child
        | .tuple es => es.forM child
        | .record fs =>
            unless (fs.map Prod.fst).Nodup do throw "duplicate record field"
            fs.forM (child ∘ Prod.snd)
        | .select e s => checkSelector s; child e
        | .update t e s v => type .value t; checkSelector s; child e; child v
        | .ite c a b => child c; child a; child b
        | .comprehension n t body branches =>
            type .number n
            type .value t
            if branches.isEmpty then throw "comprehension must have a branch"
            let introduced ← branches.mapM (checkMatches fuel bound params)
            let scope ← addNames bound introduced.flatten
            checkExpression fuel scope params body
        | .var name =>
            match bound.find? (fun n => n.id == name.id) with
            | none => throw s!"unbound value {name.origin} ({name.id})"
            | some known =>
                unless known = name do throw s!"inconsistent spelling for value identity {name.id}"
        | .typeAbs p body =>
            unless p.kind != .proposition do throw "invalid abstraction kind"
            if params.any (fun q => q.id == p.id) then throw "duplicate parameter binder"
            checkExpression fuel bound (p :: params) body
        | .typeApp e t => child e; let _ ← t.kind? fuel params
        | .app f x => child f; child x
        | .abs name t body =>
            type .value t
            checkExpression fuel (← addNames bound [name]) params body
        | .proofAbs c body => type .proposition c; child body
        | .proofApp e => child e
        | .whereE body groups =>
            let scope ← checkGroups fuel bound params groups
            checkExpression fuel scope params body
        | .guards t branches =>
            type .value t
            for (constraints, body) in branches do
              constraints.forM (type .proposition)
              child body

  private def checkDeclaration : Nat → List Reference.Name → List Parameter →
      Reference.Decl → Except String Unit
    | 0, _, _, _ => .error "declaration-checking budget exhausted"
    | fuel + 1, bound, params, .mk name schema definition =>
        (do
          schema.checkKinds fuel params
          match definition with
          | .primitive => pure ()
          | .expression body => checkExpression fuel bound params body
          | .foreign _ (some body) => checkExpression fuel bound params body
          | .foreign _ none => throw "foreign declaration has no pure reference body"
        ).mapError (fun message => s!"{name.origin}: {message}")

  private def checkGroups : Nat → List Reference.Name → List Parameter →
      List Reference.DeclGroup → Except String (List Reference.Name)
    | 0, _, _, _ => .error "group-checking budget exhausted"
    | _ + 1, bound, _, [] => .ok bound
    | fuel + 1, bound, params, .nonrecursive d :: rest => do
        checkDeclaration fuel bound params d
        checkGroups fuel (← addNames bound [d.name]) params rest
    | fuel + 1, bound, params, .recursive ds :: rest => do
        if ds.isEmpty then throw "empty recursive group"
        let scope ← addNames bound (ds.map Reference.Decl.name)
        ds.forM (checkDeclaration fuel scope params)
        checkGroups fuel scope params rest

  private def checkMatches : Nat → List Reference.Name → List Parameter →
      List Reference.Match → Except String (List Reference.Name)
    | 0, _, _, _ => .error "comprehension-checking budget exhausted"
    | _ + 1, _, _, [] => .ok []
    | fuel + 1, bound, params, .from name n t source :: rest => do
        n.checkKind fuel params .number
        t.checkKind fuel params .value
        checkExpression fuel bound params source
        return name :: (← checkMatches fuel (← addNames bound [name]) params rest)
    | fuel + 1, bound, params, .letE d :: rest => do
        checkDeclaration fuel bound params d
        return d.name :: (← checkMatches fuel (← addNames bound [d.name]) params rest)

end

/-- Validate binding structure, complete dependencies, and all type-expression kinds. -/
def SourceBundle.checkScopes (bundle : SourceBundle) (fuel : Nat := 10000) :
    Except ImportError Unit :=
  let checked : Except String Unit := do
    let globals ← checkGroups fuel [] [] bundle.groups
    unless (bundle.primitiveFallbacks.map (fun p => p.1.id)).Nodup do
      throw "duplicate primitive fallback"
    let declarations := bundle.groups.flatMap DeclGroup.declarations
    for (source, target) in bundle.primitiveFallbacks do
      unless globals.contains source && globals.contains target do
        throw "primitive fallback has an unresolved endpoint"
      unless source.origin == s!"Cryptol::{source.text}" &&
          target.origin == s!"Cryptol::Reference::{source.text}" do
        throw "primitive fallback is not an official reference definition"
      unless ["pmult", "pdiv", "pmod", "foldl", "foldl'", "foldWhile", "scanl", "iterate"].contains
          source.text do throw "unknown reference primitive fallback"
      match declarations.find? (fun d => d.name == source),
          declarations.find? (fun d => d.name == target) with
      | some (.mk _ _ .primitive), some (.mk _ _ (.expression _)) => pure ()
      | _, _ => throw "primitive fallback endpoints have the wrong declaration forms"
    for root in bundle.roots do
      (do
        root.schema.checkKinds fuel []
        checkExpression fuel globals [] root.expression
      ).mapError (fun message => s!"root {root.text}: {message}")
  checked.mapError (⟨["scope"], ·⟩)

/-- Evidence that a bundle passed the scope/kind gate at an explicit finite budget.
This certificate makes no claim about expression typing or source fidelity. -/
structure SourceBundle.ScopeCertificate (bundle : SourceBundle) where
  /-- Nesting budget used by the terminating checker. -/
  budget : Nat
  /-- Acceptance is retained as an equation checked by Lean's kernel. -/
  valid : bundle.checkScopes budget = .ok ()

/-- Successful validation returns its acceptance witness, without an unchecked cast. -/
def SourceBundle.certifyScopes (bundle : SourceBundle) (fuel : Nat := 10000) :
    Except ImportError bundle.ScopeCertificate :=
  match h : bundle.checkScopes fuel with
  | .ok () => .ok ⟨fuel, h⟩
  | .error error => .error error

end Interop.Cryptol.Translation
