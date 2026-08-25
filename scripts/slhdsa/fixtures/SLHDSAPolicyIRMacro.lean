/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public meta import Lean.Elab.Command

public section

syntax "slhdsa_policy_hidden_entry " ident : command

macro_rules
  | `(slhdsa_policy_hidden_entry $name:ident) =>
      `(initialize $name : Nat ← do
          let some path ← IO.getEnv "SLHDSA_POLICY_SENTINEL"
            | throw <| IO.userError "SLHDSA_POLICY_SENTINEL is unset"
          IO.FS.writeFile path "initializer executed"
          pure 0)
