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
-/

public section

open Lean System

private def core : List String :=
  ["VCVio", "VCVioCslib", "LatticeCrypto", "LatticeCryptoTest", "HashSig", "HashSigTest",
   "Examples", "ToMathlib", "Extern", "VCVioWidgets", "VCVioTest"]

private def tests : List String := ["VCVioTest", "LatticeCryptoTest", "HashSigTest"]

private partial def sources (dir : FilePath) : IO (Array FilePath) := do
  let mut files := #[]
  if !(← dir.isDir) then return files
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      files := files ++ (← sources entry.path)
    else if entry.path.extension == some "lean" && entry.fileName != "lakefile.lean" then
      files := files.push entry.path
  return files

private def allowed (externOnly : Bool) (owner : String) (path : FilePath) (name : Name) : Bool :=
  let head := name.getRoot.toString
  if externOnly then
    owner == "Extern" || tests.contains owner || head != "Extern"
  else if core.contains owner then
    !(["Interop", "Hax", "Aeneas"].contains head) &&
      (if path.components.take 2 == ["VCVio", "Algorithms"] then
        ["Init", "Std", "Lean", "Mathlib", "Batteries", "Cslib", "ToCslib", "PolyFun",
         "Qq", "Aesop", "ToMathlib"].contains head || (`VCVio.Algorithms).isPrefixOf name
       else true)
  else
    !(core.filter fun root => root != "VCVio" && root != "ToMathlib").contains head

/-- Check source imports without resolving or compiling their targets. -/
def main (args : List String) : IO UInt32 := do
  unless args.isEmpty || args == ["--extern"] do
    IO.eprintln "Usage: lean --run scripts/CheckImports.lean [--extern]"
    return 2
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
  if failed then return 1
  IO.println "Import isolation: OK"
  return 0
