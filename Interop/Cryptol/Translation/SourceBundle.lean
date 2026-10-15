/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Reference.Syntax
public import Lean.Data.Json

/-!
# Versioned typed-AST bundles

The decoder accepts the explicit JSON constructor format emitted by the pinned
Haskell exporter. Decoding preserves annotations and binding structure; it does
not assert that an input is well typed or corresponds to a source file.
-/

public section

namespace Interop.Cryptol.Translation

/-- An import failure identifies the input component and the violated requirement. -/
structure ImportError where
  /-- Outermost-to-innermost diagnostic path. -/
  location : List String
  /-- A concrete parsing, scope, kind, typing, or unsupported-feature error. -/
  message : String
  deriving Repr

/-- A checked frontend expression selected as a reference entry point. -/
structure SourceRoot where
  /-- The requested source expression. -/
  text : String
  /-- The typechecked frontend expression before Lean validation. -/
  expression : Reference.Expr
  /-- Its ordered source scheme. -/
  schema : Reference.Schema
  deriving Repr

/-- Content provenance for a module loaded by the frontend. -/
structure SourceModule where
  /-- Cryptol module identity. -/
  name : String
  /-- Portable path within Foundation or the pinned Cryptol distribution. -/
  path : String
  /-- SHA-256 digest of the exact input bytes. -/
  sha256 : String
  /-- Aliases retained after module instantiation. -/
  aliases : List (Reference.Name × String)
  deriving Repr

/-- A complete exported dependency graph with separately declared roots. -/
structure SourceBundle where
  /-- The exact frontend revision required by this format. -/
  cryptolRevision : String
  /-- Public entry expressions and their schemes. -/
  roots : List SourceRoot
  /-- Shared top-level definitions, retaining simultaneous recursive groups. -/
  groups : List Reference.DeclGroup
  /-- Content provenance of the loaded modules. -/
  modules : List SourceModule
  /-- Official `Cryptol::Reference` bodies used for primitives absent from the Haskell table. -/
  primitiveFallbacks : List (Reference.Name × Reference.Name)
  deriving Repr

namespace SourceBundle

/-- The pinned reference frontend understood by this decoder. -/
def expectedCryptolRevision : String := "61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b"

private abbrev Decode (α : Type) := Except String α

private def field (j : Lean.Json) (key : String) : Decode Lean.Json := j.getObjVal? key

private def array (j : Lean.Json) : Decode (List Lean.Json) :=
  j.getArr?.map Array.toList

private def tagged (j : Lean.Json) : Decode (String × List Lean.Json) := do
  return (← j.getObjValAs? String "tag", ← array (← field j "args"))

private def optional {α : Type} (f : Lean.Json → Decode α) : Lean.Json → Decode (Option α)
  | .null => .ok none
  | j => some <$> f j

private def named (j : Lean.Json) : Decode Reference.Name := do
  return ⟨← j.getObjValAs? Nat "id", ← j.getObjValAs? String "text",
    ← j.getObjValAs? String "origin"⟩

private def kind (j : Lean.Json) : Decode Reference.Kind := do
  match ← tagged j with
  | ("num", []) => return .number
  | ("type", []) => return .value
  | ("prop", []) => return .proposition
  | _ => throw "unsupported parameter kind"

private def parameter (j : Lean.Json) : Decode Reference.Parameter := do
  return ⟨← j.getObjValAs? Nat "id", ← kind (← field j "kind")⟩

private def selector (j : Lean.Json) : Decode Reference.Selector := do
  match ← tagged j with
  | ("tuple", [i, shape]) => return .tuple (← Lean.fromJson? i) (← Lean.fromJson? shape)
  | ("list", [i, shape]) => return .list (← Lean.fromJson? i) (← Lean.fromJson? shape)
  | ("record", [i, shape]) => return .record (← i.getStr?) (← Lean.fromJson? shape)
  | _ => throw "malformed selector"

private def pairs {α β : Type} (left : Lean.Json → Decode α) (right : Lean.Json → Decode β)
    (j : Lean.Json) : Decode (List (α × β)) := do
  (← array j).mapM fun entry => do
    match ← array entry with
    | [a, b] => return (← left a, ← right b)
    | _ => throw "expected a pair"

private def typeExpr : Nat → Lean.Json → Decode Reference.TypeExpr
  | 0, _ => .error "type nesting budget exhausted"
  | fuel + 1, j => do
      let child := typeExpr fuel
      let children := fun j => array j >>= List.mapM child
      match ← tagged j with
      | ("var", [p]) => return .var (← parameter p)
      | ("num", [n]) =>
          let text ← n.getStr?
          match text.toNat? with
          | some n => return .number n
          | none => throw "numeric type literal must be a natural number"
      | ("con", [name, args]) => return .constructor (← name.getStr?) (← children args)
      | ("tuple", [size, args]) => return .tuple (← Lean.fromJson? size) (← children args)
      | ("record", [fs]) => return .record (← pairs Lean.Json.getStr? child fs)
      | ("synonym", [name, args, body]) =>
          return .synonym (← named name) (← children args) (← child body)
      | ("has", [sel, args]) => return .has (← selector sel) (← children args)
      | ("free", _) => throw "unresolved frontend type variable"
      | ("nominal", _) => throw "nominal types are outside the accepted reference fragment"
      | _ => throw "malformed or unsupported type constructor"

private def schema (fuel : Nat) (j : Lean.Json) : Decode Reference.Schema := do
  return ⟨← (← array (← field j "parameters")).mapM parameter,
    ← (← array (← field j "constraints")).mapM (typeExpr fuel),
    ← typeExpr fuel (← field j "body")⟩

/-- Decode one standalone type or constraint with the same versioned constructor grammar. -/
def decodeType (j : Lean.Json) (fuel : Nat := 10000) : Except ImportError Reference.TypeExpr :=
  (typeExpr fuel j).mapError (⟨["type"], ·⟩)

mutual

  private def expression : Nat → Lean.Json → Decode Reference.Expr
    | 0, _ => .error "expression nesting budget exhausted"
    | fuel + 1, j => do
        let child := expression fuel
        let children := fun j => array j >>= List.mapM child
        let ty := typeExpr fuel
        match ← tagged j with
        | ("list", [t, es]) => return .list (← ty t) (← children es)
        | ("tuple", [es]) => return .tuple (← children es)
        | ("record", [fs]) => return .record (← pairs Lean.Json.getStr? child fs)
        | ("select", [e, s]) => return .select (← child e) (← selector s)
        | ("update", [t, e, s, v]) =>
            return .update (← ty t) (← child e) (← selector s) (← child v)
        | ("if", [c, a, b]) => return .ite (← child c) (← child a) (← child b)
        | ("comprehension", [n, t, e, bs]) =>
            let branches ← (← array bs).mapM fun b => array b >>= List.mapM (matchExpr fuel)
            return .comprehension (← ty n) (← ty t) (← child e) branches
        | ("var", [n]) => return .var (← named n)
        | ("typeAbs", [p, e]) => return .typeAbs (← parameter p) (← child e)
        | ("typeApp", [e, t]) => return .typeApp (← child e) (← ty t)
        | ("app", [f, x]) => return .app (← child f) (← child x)
        | ("abs", [n, t, e]) => return .abs (← named n) (← ty t) (← child e)
        | ("proofAbs", [c, e]) => return .proofAbs (← ty c) (← child e)
        | ("proofApp", [e]) => return .proofApp (← child e)
        | ("where", [e, gs]) => return .whereE (← child e) (← (← array gs).mapM (group fuel))
        | ("guards", [t, gs]) =>
            return .guards (← ty t) (← pairs (fun cs => array cs >>= List.mapM ty) child gs)
        | ("case", _) =>
            throw "nominal case expressions are outside the accepted reference fragment"
        | _ => throw "malformed or unsupported expression constructor"

  private def matchExpr : Nat → Lean.Json → Decode Reference.Match
    | 0, _ => .error "comprehension nesting budget exhausted"
    | fuel + 1, j => do
        match ← tagged j with
        | ("from", [name, len, ty, e]) =>
            return .from (← named name) (← typeExpr fuel len) (← typeExpr fuel ty)
              (← expression fuel e)
        | ("let", [d]) => return .letE (← declaration fuel d)
        | _ => throw "malformed comprehension match"

  private def declaration : Nat → Lean.Json → Decode Reference.Decl
    | 0, _ => .error "declaration nesting budget exhausted"
    | fuel + 1, j => do
        let defn : Reference.Definition ← match ← tagged (← field j "definition") with
          | ("primitive", []) => pure .primitive
          | ("expression", [e]) => Reference.Definition.expression <$> expression fuel e
          | ("foreign", [ffi, body]) => do
              pure (Reference.Definition.foreign
                (← ffi.getStr?) (← optional (expression fuel) body))
          | _ => throw "malformed declaration definition"
        return .mk (← named (← field j "name")) (← schema fuel (← field j "schema")) defn

  private def group : Nat → Lean.Json → Decode Reference.DeclGroup
    | 0, _ => .error "declaration-group nesting budget exhausted"
    | fuel + 1, j => do
        match ← tagged j with
        | ("nonrecursive", [d]) => return .nonrecursive (← declaration fuel d)
        | ("recursive", [ds]) => return .recursive (← (← array ds).mapM (declaration fuel))
        | _ => throw "malformed declaration group"

end

private def root (fuel : Nat) (j : Lean.Json) : Decode SourceRoot := do
  return ⟨← j.getObjValAs? String "text", ← expression fuel (← field j "expression"),
    ← schema fuel (← field j "schema")⟩

private def sourceModule (j : Lean.Json) : Decode SourceModule := do
  let digest ← j.getObjValAs? String "sha256"
  unless digest.length = 64 && digest.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw "invalid source SHA-256 digest"
  let path ← j.getObjValAs? String "path"
  unless !path.startsWith "/" && !(path.splitOn "/").contains ".." do
    throw "source path must be portable and must not contain parent traversals"
  return ⟨← j.getObjValAs? String "name", path, digest,
    ← pairs named Lean.Json.getStr? (← field j "aliases")⟩

/-- Decode a bundle with an explicit nesting budget and an exact version/pin check. -/
def decode (j : Lean.Json) (fuel : Nat := 10000) : Except ImportError SourceBundle :=
  let decoded : Decode SourceBundle := do
    unless (← j.getObjValAs? String "format") = "cryptol-typed-ast" do
      throw "unknown typed-AST format"
    unless (← j.getObjValAs? Nat "version") = 1 do throw "unsupported typed-AST version"
    unless (← j.getObjValAs? String "cryptol_revision") = expectedCryptolRevision do
      throw "Cryptol frontend revision differs from the supported pin"
    let roots ← (← array (← field j "roots")).mapM (root fuel)
    if roots.isEmpty then throw "bundle must contain an entry point"
    return ⟨expectedCryptolRevision, roots, ← (← array (← field j "groups")).mapM (group fuel),
      ← (← array (← field j "modules")).mapM sourceModule,
      ← pairs named named (← field j "primitive_fallbacks")⟩
  decoded.mapError (⟨["bundle"], ·⟩)

end SourceBundle
end Interop.Cryptol.Translation
