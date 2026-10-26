/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public meta import Lean

/-!
# Kernel contracts and semantic dependency capture

A deterministic expression encoding records fully quantified declaration types and local
semantic dependencies. Theorem proofs are audited for axioms without treating proof terms as
program definitions. Definition bodies are retained even when their values are propositions.
-/

public meta section

open Lean Elab Command Meta

namespace SLHDSA.Refactor.R0

/-- A tagged structural serialization node. -/
def node (tag : String) (fields : List Json := []) : Json :=
  Json.arr (Json.str tag :: fields).toArray

/-- Kernel names retain their component structure. -/
def encodeName : Name → Json
  | .anonymous => node "anonymous"
  | .str parent value => node "str" [encodeName parent, toJson value]
  | .num parent value => node "num" [encodeName parent, toJson value]

/-- Universe levels are serialized without pretty-printer notation. -/
partial def encodeLevel : Level → Except String Json
  | .zero => pure (node "zero")
  | .succ level => return node "succ" [← encodeLevel level]
  | .max left right => return node "max" [← encodeLevel left, ← encodeLevel right]
  | .imax left right => return node "imax" [← encodeLevel left, ← encodeLevel right]
  | .param name => pure (node "param" [encodeName name])
  | .mvar _ => throw "unresolved universe metavariable in a closed declaration"

/-- Binder visibility is part of a declaration's calling convention. -/
def encodeBinder : BinderInfo → Json
  | .default => toJson "explicit"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strictImplicit"
  | .instImplicit => toJson "instance"

/-- Closed kernel expressions retain all semantic syntax and omit only source metadata. -/
partial def encodeExpr : Expr → Except String Json
  | .bvar index => pure (node "bvar" [toJson index])
  | .fvar _ => throw "free variable in a closed declaration"
  | .mvar _ => throw "unresolved expression metavariable in a closed declaration"
  | .sort level => return node "sort" [← encodeLevel level]
  | .const name levels =>
      return node "const" [encodeName name, toJson (← levels.mapM encodeLevel)]
  | .app fn arg => return node "app" [← encodeExpr fn, ← encodeExpr arg]
  | .lam name type body binder =>
      return node "lam" [encodeName name, encodeBinder binder, ← encodeExpr type, ← encodeExpr body]
  | .forallE name type body binder =>
      return node "forall" [encodeName name, encodeBinder binder, ← encodeExpr type, ← encodeExpr body]
  | .letE name type value body nondep =>
      return node "let" [encodeName name, ← encodeExpr type, ← encodeExpr value,
        ← encodeExpr body, toJson nondep]
  | .lit (.natVal value) => pure (node "nat" [toJson value])
  | .lit (.strVal value) => pure (node "string" [toJson value])
  | .mdata _ body => encodeExpr body
  | .proj name index body => return node "proj" [encodeName name, toJson index, ← encodeExpr body]

/-- The imported module owning a declaration, independent of its namespace. -/
def owner (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  env.header.moduleNames[index.toNat]?

/-- Local ownership is selected by module roots, rather than declaration-name prefixes. -/
def isLocal (roots : Array String) (moduleName : Name) : Bool :=
  roots.any fun root => moduleName.toString == root || moduleName.toString.startsWith (root ++ ".")

/-- Kernel reducibility hints distinguish opaque, abbreviated, and regular definitions. -/
def encodeHints : ReducibilityHints → Json
  | .opaque => node "opaque"
  | .abbrev => node "abbrev"
  | .regular height => node "regular" [toJson height.toNat]

/-- Declaration shape metadata preserves safety, reduction, and constructor behavior. -/
def shape (info : ConstantInfo) : Json :=
  match info with
  | .axiomInfo value => node "axiom" [toJson value.isUnsafe]
  | .defnInfo value => node "definition" [toJson (reprStr value.safety), encodeHints value.hints]
  | .thmInfo _ => node "theorem"
  | .opaqueInfo value => node "opaque" [toJson value.isUnsafe]
  | .quotInfo _ => node "quotient"
  | .inductInfo value => node "inductive" [toJson value.numParams, toJson value.numIndices,
      toJson (value.all.map encodeName), toJson (value.ctors.map encodeName),
      toJson value.numNested, toJson value.isRec, toJson value.isUnsafe, toJson value.isReflexive]
  | .ctorInfo value => node "constructor" [encodeName value.induct, toJson value.cidx,
      toJson value.numParams, toJson value.numFields, toJson value.isUnsafe]
  | .recInfo value => node "recursor" [toJson value.numParams, toJson value.numIndices,
      toJson value.numMotives, toJson value.numMinors, toJson (value.all.map encodeName),
      toJson value.k, toJson value.isUnsafe,
      toJson (value.rules.map fun rule => node "rule" [encodeName rule.ctor, toJson rule.nfields])]

/-- Semantic bodies include opaque and proposition-valued definitions, but exclude theorem proofs. -/
def semanticBodies (info : ConstantInfo) : Array Expr :=
  match info with
  | .defnInfo value => #[value.value]
  | .opaqueInfo value => #[value.value]
  | .recInfo value => value.rules.toArray.map (·.rhs)
  | _ => #[]

/-- Constants used by types and computational bodies, including inductive constructors. -/
def semanticDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut result := info.type.getUsedConstants
  for body in semanticBodies info do result := result ++ body.getUsedConstants
  match info with
  | .inductInfo value => result := result ++ value.all.toArray ++ value.ctors.toArray
  | .recInfo value => result := result ++ value.all.toArray ++ (value.rules.toArray.map (·.ctor))
  | _ => pure ()
  return result.qsort Name.lt

/-- Encode one declaration without replacing its type by a named alias. -/
def captureConstant (env : Environment) (name : Name) : CommandElabM Json := do
  let some info := env.find? name | throwError "Unknown captured declaration {name}"
  let type ← ofExcept (encodeExpr info.type)
  let values ← ofExcept ((semanticBodies info).mapM encodeExpr)
  let axioms ← collectAxioms name
  let pretty ← liftTermElabM do
    withOptions (fun options => options.setBool `pp.fullNames true |>.setBool `pp.universes true
      |>.setBool `pp.explicit false |>.setBool `pp.proofs true) do
      return (← ppExpr info.type).pretty
  return Json.mkObj [
    ("name", toJson name.toString),
    ("module", toJson ((owner env name).map Name.toString)),
    ("levels", toJson (info.levelParams.map Name.toString)),
    ("levelNames", toJson (info.levelParams.map encodeName)),
    ("shape", shape info),
    ("type", type),
    ("typePretty", toJson pretty),
    ("values", toJson values),
    ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
    ("dependencies", toJson (semanticDependencies info |>.map Name.toString))]

/-- Capture selected declarations and their complete locally owned semantic dependency closure. -/
def capture (names : Array Name) (roots : Array String) : CommandElabM Json := do
  let env := (← getEnv).setExporting false
  let mut pending := names
  let mut seen : Std.HashSet Name := {}
  let mut records : Array Json := #[]
  let mut externalNames : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing semantic dependency {name}"
    if let .axiomInfo _ := info then
      if (owner env name).any (isLocal roots) then
        throwError "Local semantic body {name} is unavailable or axiomatic; import its implementation explicitly"
    records := records.push (← captureConstant env name)
    for dependency in semanticDependencies info do
      if let some moduleName := owner env dependency then
        if isLocal roots moduleName then pending := pending.push dependency
        else externalNames := externalNames.insert dependency
      else if !seen.contains dependency then
        throwError "Semantic dependency {dependency} has no recorded imported-module owner"
  return Json.mkObj [
    ("format", toJson 1), ("leanVersion", toJson Lean.versionString), ("selected", toJson (names.map Name.toString)),
    ("localModuleRoots", toJson roots), ("records", toJson records),
    ("externalBoundary", toJson (externalNames.toArray.qsort Name.lt |>.map fun name =>
      Json.mkObj [("name", toJson name.toString),
        ("module", toJson ((owner env name).map Name.toString))]))]

/-- Export a contract capture requested by an explicit driver command. -/
elab "slhdsa_r0_capture " input:str " to " output:str : command => do
  let raw ← IO.FS.readFile input.getString
  let specification ← ofExcept (Json.parse raw)
  let names ← ofExcept (specification.getObjValAs? (Array String) "names")
  let roots ← ofExcept (specification.getObjValAs? (Array String) "localModuleRoots")
  let result ← capture (names.map String.toName) roots
  IO.FS.writeFile output.getString result.compress
  logInfo m!"Captured {names.size} contracts and their local semantic dependencies"



/-- Expand a topologically ordered JSON DAG without permitting cycles or forward references. -/
def expandDag (nodes : Array Json) : Except String (Array Json) := do
  let mut expanded : Array Json := #[]
  for encoded in nodes do
    let fields ← encoded.getArr?
    if fields.isEmpty then throw "empty DAG node"
    let tag ← fields[0]!.getNat?
    let value ← match tag with
      | 0 => do
        let mut children : Array Json := #[]
        for reference in fields.extract 1 fields.size do
          let index ← reference.getNat?
          if h : index < expanded.size then children := children.push expanded[index]
          else throw "DAG reference is not an earlier node"
        pure (Json.arr children)
      | 1 => do
        if fields.size != 2 then throw "invalid string DAG node"
        pure (Json.str (← fields[1]!.getStr?))
      | 2 => do
        if fields.size != 2 then throw "invalid natural DAG node"
        pure (toJson (← fields[1]!.getNat?))
      | 3 => do
        if fields.size != 2 then throw "invalid boolean DAG node"
        pure (toJson (← fields[1]!.getBool?))
      | 4 => do
        if fields.size != 1 then throw "invalid null DAG node"
        pure Json.null
      | _ => throw "unknown DAG node tag"
    expanded := expanded.push value
  return expanded

/-- Read a tagged serialization node of a fixed arity. -/
def fieldsOf (value : Json) (arity : Nat) : Except String (Array Json) := do
  let fields ← value.getArr?
  if fields.size != arity then throw "invalid kernel node arity"
  return fields

/-- Decode a structurally represented kernel name. -/
partial def decodeName (value : Json) : Except String Name := do
  let fields ← value.getArr?
  if fields.isEmpty then throw "empty name node"
  match ← fields[0]!.getStr? with
  | "anonymous" =>
    let _ ← fieldsOf value 1
    pure .anonymous
  | "str" =>
    let fields ← fieldsOf value 3
    return .str (← decodeName fields[1]!) (← fields[2]!.getStr?)
  | "num" =>
    let fields ← fieldsOf value 3
    return .num (← decodeName fields[1]!) (← fields[2]!.getNat?)
  | _ => throw "unknown name node"

/-- Decode a universe expression without accepting metavariables. -/
partial def decodeLevel (value : Json) : Except String Level := do
  let fields ← value.getArr?
  if fields.isEmpty then throw "empty universe node"
  match ← fields[0]!.getStr? with
  | "zero" => let _ ← fieldsOf value 1; pure .zero
  | "succ" => let fields ← fieldsOf value 2; return .succ (← decodeLevel fields[1]!)
  | "max" =>
    let fields ← fieldsOf value 3
    return .max (← decodeLevel fields[1]!) (← decodeLevel fields[2]!)
  | "imax" =>
    let fields ← fieldsOf value 3
    return .imax (← decodeLevel fields[1]!) (← decodeLevel fields[2]!)
  | "param" => let fields ← fieldsOf value 2; return .param (← decodeName fields[1]!)
  | _ => throw "unknown universe node"

/-- Decode binder visibility exactly. -/
def decodeBinder (value : Json) : Except String BinderInfo := do
  match ← value.getStr? with
  | "explicit" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instance" => pure .instImplicit
  | _ => throw "unknown binder visibility"

/-- Decode kernel syntax without free variables, metavariables, or source elaboration. -/
partial def decodeExpr (value : Json) : Except String Expr := do
  let fields ← value.getArr?
  if fields.isEmpty then throw "empty expression node"
  match ← fields[0]!.getStr? with
  | "bvar" => let fields ← fieldsOf value 2; return .bvar (← fields[1]!.getNat?)
  | "sort" => let fields ← fieldsOf value 2; return .sort (← decodeLevel fields[1]!)
  | "const" =>
    let fields ← fieldsOf value 3
    return .const (← decodeName fields[1]!) (← (← fields[2]!.getArr?).toList.mapM decodeLevel)
  | "app" =>
    let fields ← fieldsOf value 3
    return .app (← decodeExpr fields[1]!) (← decodeExpr fields[2]!)
  | "lam" =>
    let fields ← fieldsOf value 5
    return .lam (← decodeName fields[1]!) (← decodeExpr fields[3]!)
      (← decodeExpr fields[4]!) (← decodeBinder fields[2]!)
  | "forall" =>
    let fields ← fieldsOf value 5
    return .forallE (← decodeName fields[1]!) (← decodeExpr fields[3]!)
      (← decodeExpr fields[4]!) (← decodeBinder fields[2]!)
  | "let" =>
    let fields ← fieldsOf value 6
    return .letE (← decodeName fields[1]!) (← decodeExpr fields[2]!)
      (← decodeExpr fields[3]!) (← decodeExpr fields[4]!) (← fields[5]!.getBool?)
  | "nat" => let fields ← fieldsOf value 2; return .lit (.natVal (← fields[1]!.getNat?))
  | "string" => let fields ← fieldsOf value 2; return .lit (.strVal (← fields[1]!.getStr?))
  | "proj" =>
    let fields ← fieldsOf value 4
    return .proj (← decodeName fields[1]!) (← fields[2]!.getNat?) (← decodeExpr fields[3]!)
  | _ => throw "unknown or non-closed expression node"

/-- Read one immutable contract from the literal type bundle. -/
def readContract (path source : String) : CommandElabM (Json × Expr) := do
  let raw ← IO.FS.readFile path
  let bundle ← ofExcept (Json.parse raw)
  let nodes ← ofExcept (bundle.getObjValAs? (Array Json) "nodes")
  let expanded ← ofExcept (expandDag nodes)
  let contracts ← ofExcept (bundle.getObjValAs? (Array Json) "contracts")
  let foundEntries := contracts.filter fun entry => (entry.getObjValAs? String "source").toOption == some source
  if foundEntries.size != 1 then throwError "Contract {source} does not occur exactly once"
  let entry := foundEntries[0]!
  let index ← ofExcept (entry.getObjValAs? Nat "typeRoot")
  let some encoded := expanded[index]? | throwError "Contract root is outside the DAG"
  let type ← ofExcept (decodeExpr encoded)
  if type.hasLooseBVars || type.hasFVar || type.hasMVar || type.hasLevelMVar then
    throwError "The expected contract is not closed"
  return (entry, type)

/-- Submit a literal, fully quantified contract witness to the ordinary checked declaration API. -/
elab "slhdsa_r0_witness " path:str " for " source:str " as " witness:ident : command => do
  let (entry, type) ← readContract path.getString source.getString
  let levels ← ofExcept (entry.getObjValAs? (Array Json) "levelNames")
  let kind ← ofExcept (entry.getObjValAs? String "kind")
  let name := (← getCurrNamespace) ++ witness.getId
  let levelParams ← ofExcept (levels.toList.mapM decodeName)
  let value := Expr.const source.getString.toName (levelParams.map Level.param)
  let declaration ← match kind with
    | "theorem" => pure (Declaration.thmDecl { name, levelParams, type, value })
    | "definition" => pure (Declaration.defnDecl
        { name, levelParams, type, value, hints := .opaque, safety := .safe })
    | _ => throwError "Unsupported contract witness kind {kind}"
  liftCoreM <| addAndCompile declaration
  addDocStringCore name "A fully quantified signature contract checked against a literal kernel type."



/-- Check that every literal contract has its public kernel-checked witness. -/
elab "slhdsa_r0_validate_witnesses " path:str : command => do
  let raw ← IO.FS.readFile path.getString
  let bundle ← ofExcept (Json.parse raw)
  let contracts ← ofExcept (bundle.getObjValAs? (Array Json) "contracts")
  let mut seen : Std.HashSet String := {}
  for entry in contracts do
    let source ← ofExcept (entry.getObjValAs? String "source")
    let witness ← ofExcept (entry.getObjValAs? String "witness")
    if seen.contains source then throwError "Duplicate literal source contract {source}"
    seen := seen.insert source
    let (_, expected) ← readContract path.getString source
    let levels ← ofExcept (entry.getObjValAs? (Array Json) "levelNames")
    let levelParams ← ofExcept (levels.toList.mapM decodeName)
    let some info := (← getEnv).find? witness.toName |
      throwError "Missing public contract witness {witness}"
    if info.type != expected || info.levelParams != levelParams then
      throwError "Witness {witness} does not have its literal quantified type"
    let actualAxioms ← collectAxioms witness.toName
    let sourceAxioms ← collectAxioms source.toName
    if actualAxioms.qsort Name.lt != sourceAxioms.qsort Name.lt then
      throwError "Witness {witness} changes its source contract's axioms"
  logInfo m!"Validated {contracts.size} literal kernel contract witnesses"

end SLHDSA.Refactor.R0
