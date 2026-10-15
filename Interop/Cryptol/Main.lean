/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Translation.CLI
import Interop.Cryptol.Translation.SourceCLI
import Interop.Cryptol.Bridge.CLI

/-! # Executable Cryptol interoperation workflows -/

/-- Dispatch model observations and Foundation correspondence checks. -/
public def main (args : List String) : IO UInt32 :=
  match args with
  | "model" :: args => Interop.Cryptol.CLI.run args
  | "source" :: args => Interop.Cryptol.Translation.SourceCLI.run args
  | "foundation" :: args => Interop.Cryptol.Bridge.CLI.run args
  | _ => do
    (← IO.getStderr).putStrLn "Usage: cryptol-interop {model | source | foundation} COMMAND ..."
    return 1
