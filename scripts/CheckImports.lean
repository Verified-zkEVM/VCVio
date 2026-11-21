/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
import Lean.Elab.ParseImportsFast

/-!
# Import isolation

Checks the optional-backend, native-linking and pure-algorithm boundaries directly from source.
Lean's own header parser handles import modifiers, comments and module names. No project or
dependency build is needed. Run `lean --run scripts/CheckImports.lean [--extern]` from the root.

Each directory `Interop/<A>/` is a sub-project with its own Lake package. A module of `Interop/<A>/`
imports a module `Interop.<B>.…` of another sub-project only when the pair `A B` is listed in
`scripts/interop_import_allowlist.txt`.
-/

public section

open Lean System

private def core : List String :=
  ["VCVio", "LatticeCrypto", "LatticeCryptoTest", "HashSig", "HashSigTest",
   "Examples", "ToMathlib", "Extern", "VCVioTest"]

private def tests : List String := ["VCVioTest", "LatticeCryptoTest", "HashSigTest"]

private partial def sources (dir : FilePath) : IO (Array FilePath) := do
  let mut files := #[]
  if !(← dir.isDir) then return files
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      files := files ++ (← sources entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path
  return files

private def allowed (externOnly : Bool) (owner : String) (path : FilePath) (name : Name) : Bool :=
  let head := name.getRoot.toString
  let source := (path.withExtension "").components.foldl Name.str .anonymous
  if externOnly then
    owner == "Extern" || tests.contains owner || head != "Extern"
  else if core.contains owner then
    !(["Interop", "Hax", "Aeneas"].contains head) &&
      (if (`VCVio.Algorithms).isPrefixOf source then
        ["Init", "Std", "Lean", "Mathlib", "Batteries", "Cslib", "ToCslib", "PolyFun",
         "Qq", "Aesop", "ToMathlib"].contains head || (`VCVio.Algorithms).isPrefixOf name
       else true)
  else
    !(core.filter fun root => root != "VCVio" && root != "ToMathlib").contains head

/-- The pairs `(A, B)` of `Interop/` sub-projects such that modules of `Interop/<A>/` may import
modules of `Interop/<B>/`: the lines `A B` of `scripts/interop_import_allowlist.txt`, after `#`
comments. A missing file lists no pair. -/
private def interopAllowlist : IO (List (String × String)) := do
  let file : FilePath := "scripts" / "interop_import_allowlist.txt"
  unless ← file.pathExists do return []
  let mut pairs := []
  for line in ← IO.FS.lines file do
    let body := (line.splitOn "#").headD ""
    match ((body.replace "\t" " ").splitOn " ").filter (!·.isEmpty) with
    | [] => pure ()
    | [importer, imported] => pairs := (importer, imported) :: pairs
    | _ => throw <| IO.userError s!"{file}: expected `<importer> <imported>`, got: {line}"
  return pairs

/-- Whether the `Interop/` source at `path` may import `name` as far as sub-projects go: a module
`Interop.<B>.…` only from `Interop/<B>/` itself or from a sub-project `A` listing `(A, B)`. -/
private def interopSubprojectAllowed (allow : List (String × String)) (path : FilePath)
    (name : Name) : Bool :=
  if name.getRoot != `Interop then true else
  match (path.withExtension "").components[1]?, name.components[1]?.map (·.toString) with
  | some importer, some imported => importer == imported || allow.contains (importer, imported)
  | _, _ => false

/-- Check source imports without resolving or compiling their targets. -/
def main (args : List String) : IO UInt32 := do
  unless args.isEmpty || args == ["--extern"] do
    IO.eprintln "Usage: lean --run scripts/CheckImports.lean [--extern]"
    return 2
  let allow ← if args.isEmpty then interopAllowlist else pure []
  let mut failed := false
  for owner in core ++ ["Interop"] do
    let mut paths ← sources owner
    let umbrella : FilePath := owner ++ ".lean"
    if ← umbrella.pathExists then paths := paths.push umbrella
    for path in paths do
      let header ← parseImports' (← IO.FS.readFile path) path.toString
      for imp in header.imports do
        unless allowed (args == ["--extern"]) owner path imp.module do
          IO.eprintln s!"{path}: forbidden import {imp.module}"
          failed := true
        if owner == "Interop" && args.isEmpty &&
            !interopSubprojectAllowed allow path imp.module then
          IO.eprintln s!"{path}: forbidden import {imp.module} from another Interop sub-project \
            (scripts/interop_import_allowlist.txt)"
          failed := true
  if failed then return 1
  IO.println "Import isolation: OK"
  return 0
