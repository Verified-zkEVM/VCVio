/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction
public import Lean.Util.CollectAxioms
public import Lean.Elab.Command

/-! Every declaration in the exported namespace stays inside Lean's standard axiom footprint. -/

public section

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for (name, _) in (← getEnv).constants.toList do
    if (`GroupModel.Interaction).isPrefixOf name then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unexpected axiom in {name}: {axiomName}"
