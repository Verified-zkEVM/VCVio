/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Lean
import Std.Data.HashSet

/-!
# Documentation name resolution

Resolves the declaration-like tokens that `scripts/check-doc-names.py` extracts from the agent
documentation against the compiled environment of the proof libraries, so that a guide cannot
cite a declaration that does not exist. A token resolves when it is a declaration, a namespace,
a module, an option (with or without the `weak.` prefix), a simp set, an attribute, a leading
keyword of the tactic, command or term parsers, or a suffix by components of a declaration,
namespace or module name (`Spec.uniformSample` for `OracleComp.Lower.Spec.uniformSample`,
`.run'` for a field, `Tracing.Core` for a module). A token whose first component starts in
lower case is read as a variable's field access (`spec.toPFunctor`) and resolves by the rest.

```
lake exe docnames NAMES.json [--root Module]…
```

`NAMES.json` is `{"names": ["…", …]}`. Each unresolved token is printed to standard output
as a line `UNRESOLVED<tab>token<tab>suggestions`, the suggestions being up to four constants
that share the token's last component; the Python half applies the allowlist and sets the exit
status. The default roots are the proof libraries. Exit code 2 is an infrastructure failure:
unreadable input, or roots that cannot be imported (run after `lake build`).
-/

open Lean

namespace DocNames

/-- The proof libraries whose environments the tokens are resolved against. -/
def defaultRoots : Array Name :=
  #[`VCVio, `ToMathlib, `LatticeCrypto, `HashSig, `Examples, `Extern]

structure Config where
  names? : Option String := none
  roots : Array Name := #[]

partial def parseArgs : List String → Config → Except String Config
  | [], cfg =>
    if cfg.names?.isSome then .ok cfg else .error "docnames: expected the names file"
  | "--root" :: m :: rest, cfg => parseArgs rest { cfg with roots := cfg.roots.push m.toName }
  | ["--root"], _ => .error "docnames: --root needs a module name"
  | arg :: rest, cfg =>
    if arg.startsWith "-" then .error s!"docnames: unknown option {arg}"
    else if cfg.names?.isSome then .error s!"docnames: unexpected argument {arg}"
    else parseArgs rest { cfg with names? := some arg }

/-- Every nonempty suffix of a name, by components. -/
def suffixes (n : Name) : List Name :=
  let cs := n.components
  (List.range cs.length).map fun i => (cs.drop i).foldl (· ++ ·) Name.anonymous

/-- Every nonempty contiguous run of a name's components: the suffixes of its prefixes. -/
def segments (n : Name) : List Name :=
  let cs := n.components
  (List.range cs.length).flatMap fun i =>
    (List.range (cs.length - i)).map fun j => (cs.drop i |>.take (j + 1)).foldl (· ++ ·) .anonymous

/-- The user-facing form of a constant name: a private name without its private prefix. -/
def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- A suffix index of names and, by last component, the full constant names behind it. -/
structure Index where
  suffixes : Std.HashSet Name := {}
  byLast : Std.HashMap Name (Array Name) := {}

/-- The suffixes of every constant name (private names by their user-facing form; no internal
or numbered components), of the namespace each one is declared in, and every segment of every
module name; and the constant names behind each last component, for suggestions. -/
def buildIndex (env : Environment) : Index :=
  let insertAll (acc : Std.HashSet Name) (n : Name) : Std.HashSet Name :=
    (suffixes n).foldl (fun acc s => acc.insert s) acc
  let index := env.constants.fold (init := ({} : Index)) fun acc n _ =>
    let n := userName n
    if n.isInternal || n.components.any (·.isNum) then acc
    else
      { suffixes := insertAll (insertAll acc.suffixes n) n.getPrefix
        byLast := acc.byLast.alter (n.components.getLast?.getD n) fun
          | some names => some (if names.size < 4 then names.push n else names)
          | none => some #[n] }
  let suffixes := env.header.moduleNames.foldl (init := index.suffixes) fun acc m =>
    (segments m).foldl (fun acc s => acc.insert s) acc
  { index with suffixes }

/-- Whether `raw` is the leading keyword of a tactic, command or term parser. Identifier-like
keywords are not entries of the token table, which holds the symbolic tokens. -/
def leadingKeyword (env : Environment) (raw : String) : Bool :=
  let categories := (Parser.parserExtension.getState env).categories
  [`tactic, `command, `term].any fun category =>
    match categories.find? category with
    | some cat => cat.tables.leadingTable.contains (Name.mkSimple raw)
    | none => false

/-- The name without its first component: the field path of a variable's field access. -/
def fieldPath (n : Name) : Name :=
  (n.components.drop 1).foldl (· ++ ·) Name.anonymous

/-- Whether `token` names something in the environment. -/
def resolves (index : Index) (options : OptionDecls) (token : String) :
    CoreM Bool := do
  let env ← getEnv
  let raw : String :=
    if token.startsWith "." then (token.toRawSubstring.drop 1).toString else token
  let n := raw.toName
  if env.contains n || env.isNamespace n || env.header.moduleNames.contains n then
    return true
  let optionName := if raw.startsWith "weak." then n.replacePrefix `weak Name.anonymous else n
  if options.contains optionName || isAttribute env n then
    return true
  let simpSet? ← Meta.getSimpExtension? n
  if simpSet?.isSome then
    return true
  if index.suffixes.contains n then
    return true
  if n.components.length ≥ 2 then
    if let some head := n.components.head? then
      if head.toString.front.isLower && index.suffixes.contains (fieldPath n) then
        return true
  return leadingKeyword env raw

/-- Constants sharing the token's last component, as a hint for an unresolved token. -/
def suggestions (index : Index) (token : String) : Array Name :=
  let n := token.toName
  (index.byLast.get? (n.components.getLast?.getD n)).getD #[]

/-- The tokens that do not resolve, in input order, each with its suggestions. -/
def unresolvedTokens (index : Index) (options : OptionDecls) (names : Array String) :
    CoreM (Array (String × Array Name)) := do
  let mut unresolved := #[]
  for token in names do
    unless ← resolves index options token do
      unresolved := unresolved.push (token, suggestions index token)
  return unresolved

/-- The tokens of the names file: `{"names": ["…", …]}`. -/
def readNames (path : String) : IO (Except String (Array String)) := do
  let text ← IO.FS.readFile path
  return (Json.parse text >>= (·.getObjVal? "names") >>= (·.getArr?) >>= (·.mapM (·.getStr?)))

end DocNames

open DocNames in
unsafe def run (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args {} with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln e; return 2
  let some namesPath := cfg.names? | IO.eprintln "docnames: expected the names file"; return 2
  let names ← match ← readNames namesPath with
    | .ok names => pure names
    | .error e => IO.eprintln s!"docnames: cannot read {namesPath}: {e}"; return 2
  let roots := if cfg.roots.isEmpty then defaultRoots else cfg.roots
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← try
      importModules (roots.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
    catch e =>
      IO.eprintln s!"docnames: cannot import root modules {roots}: {e.toString}"
      return (2 : UInt32)
  let index := buildIndex env
  let options ← getOptionDecls
  let (unresolved, _) ← (unresolvedTokens index options names).toIO
    { fileName := "<docnames>", fileMap := default } { env }
  for (token, hints) in unresolved do
    IO.println s!"UNRESOLVED\t{token}\t{" ".intercalate (hints.toList.map toString)}"
  IO.eprintln s!"docnames: {names.size} tokens, {unresolved.size} unresolved, against {roots}"
  return 0

unsafe def main (args : List String) : IO UInt32 := do
  try
    run args
  catch e =>
    IO.eprintln s!"docnames: internal error: {e}"
    return 2
