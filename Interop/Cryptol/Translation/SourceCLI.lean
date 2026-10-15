/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Translation.SourceScope
import Interop.Cryptol.Translation.SourceElaboration
import Interop.Cryptol.Translation.Export
import Interop.Cryptol.Model.Reference.Types

/-! # Source-bundle validation and inspection -/

namespace Interop.Cryptol.Translation.SourceCLI

def errorJson (error : ImportError) : Lean.Json :=
  .mkObj [("status", .str "rejected"), ("location", Lean.toJson error.location),
    ("message", .str error.message)]

/-- Decode and validate a versioned source bundle, reporting the exact checking stage. -/
public def run (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match args with
  | ["elaborate", file] =>
      let text ← IO.FS.readFile file
      let input : Except ImportError SourceBundle := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        SourceBundle.decode json
      match input with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok bundle =>
          let reports : List (Except ImportError (ULift.{1} Lean.Json)) :=
            bundle.roots.map fun root => do
            let certificate ← SourceElaboration.certify bundle root.expression
            let ⟨(_, type)⟩ ← SourceElaboration.liftCheck
              ((root.schema.instantiate 1000 [] []).mapError (⟨["root schema"], ·⟩))
            let ⟨expected⟩ ← SourceElaboration.liftCheck
              ((SourceElaboration.coreType type).mapError (⟨["root type"], ·⟩))
            let term ← (SourceElaboration.expect expected certificate.result).mapError
              (⟨["root type"], ·⟩)
            pure ⟨Lean.Json.mkObj [("root", .str root.text), ("status", .str "typed"),
              ("type", .str (reprStr expected)),
              ("source", .str (Export.expression term))]⟩
          let mut results := #[]
          for result in reports do
            match result with
            | .error error => out.putStrLn (errorJson error).compress; return 1
            | .ok ⟨result⟩ => results := results.push result
          out.putStrLn (Lean.Json.arr results).compress
          return 0
  | ["constraints", file] =>
      let text ← IO.FS.readFile file
      let result : Except ImportError Lean.Json := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        let cases ← json.getArr?.mapError (⟨["cases"], ·⟩)
        let checked ← cases.mapM fun entry => do
          let input ← (entry.getObjVal? "constraint").mapError (⟨["constraint"], ·⟩)
          let expression ← SourceBundle.decodeType input
          let result ← (do
            expression.checkKind 10000 [] .proposition
            expression.evaluate 10000 [] >>= Reference.TypeValue.proposition?).mapError
              (⟨["constraint"], ·⟩)
          pure (Lean.Json.mkObj [("constraint", input), ("result", Lean.toJson result)])
        return .arr checked
      match result with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok result => out.putStrLn result.compress; return 0
  | ["inspect", file] =>
      let text ← IO.FS.readFile file
      let result : Except ImportError SourceBundle := do
        let json ← (Lean.Json.parse text).mapError (⟨["json"], ·⟩)
        let bundle ← SourceBundle.decode json
        let _ ← bundle.certifyScopes
        pure bundle
      match result with
      | .error error => out.putStrLn (errorJson error).compress; return 1
      | .ok bundle =>
          out.putStrLn (Lean.Json.mkObj [("status", .str "scoped"),
            ("roots", Lean.toJson (bundle.roots.map SourceRoot.text)),
            ("groups", Lean.toJson bundle.groups.length),
            ("declarations", Lean.toJson
              (bundle.groups.flatMap Reference.DeclGroup.declarations).length),
            ("modules", Lean.toJson bundle.modules.length)]).compress
          return 0
  | _ =>
      err.putStrLn "Usage: cryptol-interop source {inspect | elaborate | constraints} FILE.json"
      return 1

end Interop.Cryptol.Translation.SourceCLI
