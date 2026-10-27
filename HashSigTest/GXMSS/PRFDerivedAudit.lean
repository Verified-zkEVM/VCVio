/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public import HashSig.GXMSS.Security.PRFDerived.Unforgeability
import all HashSig.GXMSS.Encoding.RetryIndexed
import all HashSig.GXMSS.PRFDerivedScheme
import all HashSig.GXMSS.Security.PRFDerived.KeyGeneration
import all HashSig.GXMSS.Security.PRFDerived.Signing
import all HashSig.GXMSS.Security.PRFDerived.PRFOracleInteraction
import all HashSig.GXMSS.Security.PRFDerived.Unforgeability

/-!
# PRF-derived GXMSS security import audit

The public security results must originate in their designated proof modules. Every imported
declaration from the scheme, indexed retry, and four security modules, including private and
generated auxiliaries, is checked for a definition or proof and its transitive axioms.
-/

public section

open GXMSS.PRFDerived.Unforgeability

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  let header := env.header
  let interactionModule := `HashSig.GXMSS.Security.PRFDerived.PRFOracleInteraction
  let finalModule := `HashSig.GXMSS.Security.PRFDerived.Unforgeability
  let modules := [
    `HashSig.GXMSS.Encoding.RetryIndexed,
    `HashSig.GXMSS.PRFDerivedScheme,
    `HashSig.GXMSS.Security.PRFDerived.KeyGeneration,
    `HashSig.GXMSS.Security.PRFDerived.Signing,
    interactionModule,
    finalModule]
  let names := [
    (``randgenPRFReduction_real_strong, interactionModule),
    (``randgenPRFReduction_functionQuery_bound, finalModule),
    (``ideal_adaptive_strong_correspondence, finalModule),
    (``adaptive_strong_additive_bound, finalModule),
    (``strong_reduction_bound, finalModule)]
  for (name, expectedModule) in names do
    let some info := env.find? name
      | throwError "{name} is missing from the imported environment"
    let .thmInfo theoremInfo := info
      | throwError "{name} is not an imported theorem"
    let some index := env.getModuleIdxFor? name
      | throwError "{name} has no imported-module origin"
    let origin := header.moduleNames[index.toNat]!
    unless origin == expectedModule do
      throwError "{name} has wrong imported origin: {origin}"
    Lean.Meta.forallTelescope theoremInfo.type fun _ proposition => do
      let propositionType ← Lean.Meta.inferType proposition
      unless (← Lean.Meta.isDefEq propositionType (Lean.mkSort Lean.Level.zero)) do
        throwError "{name} is not a universally closed proposition"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut counts := modules.map fun name => (name, 0)
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let origin := header.moduleNames[index.toNat]!
      if modules.contains origin then
        match info with
        | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure ()
        | .axiomInfo _ => throwError "{name} is an imported axiom"
        | _ =>
          unless (info.value? true).isSome do
            throwError "{name} has no imported definition or proof"
        let axioms ← Lean.collectAxioms name
        let unexpected := axioms.filter fun ax => !allowed.contains ax
        unless unexpected.isEmpty do
          throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
        counts := counts.map fun (moduleName, count) =>
          if moduleName == origin then (moduleName, count + 1) else (moduleName, count)
  for (moduleName, count) in counts do
    if count == 0 then
      throwError "PRF security import audit found no declarations in {moduleName}"
  Lean.logInfo m!"PRF security import audit passed ({counts} declarations by module)"
