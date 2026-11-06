/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public meta import Lean.Elab.Command
meta import all Lean.Util.CollectAxioms

/-! # GXMSS trust-audit support

One test-only checker validates direct and PRF-extended inventories against their explicit
compiler origins, proof bodies, allowed transitive axioms and import-only facades.
-/

public meta section

namespace GXMSS.Test.TrustAudit

/-- Audit all owned declarations and the exact origins of the listed theorem endpoints. -/
def check (modules : Array Lean.Name) (endpoints : Array (Lean.Name × Lean.Name))
    (facades : Array Lean.Name) (definitions : Array (Lean.Name × Lean.Name) := #[]) :
    Lean.Elab.Term.TermElabM Unit := do
  let auditEnv ← liftM <| Lean.importModules
    (modules.map fun m => { module := m, importAll := true }) {}
    (loadExts := false) (level := .private)
  Lean.withEnv auditEnv do
    let env ← Lean.getEnv
    let header := env.header
    for (name, expected) in endpoints do
      let some (.thmInfo info) := env.find? name
        | throwError "missing theorem endpoint {name}"
      let some index := env.getModuleIdxFor? name
        | throwError "no imported compiler origin for {name}"
      let origin := header.moduleNames[index.toNat]!
      unless origin == expected do
        throwError "{name} has origin {origin}; expected {expected}"
      Lean.Meta.forallTelescope info.type fun _ proposition => do
        unless (← Lean.Meta.isProp proposition) do
          throwError "endpoint {name} is not a universally closed proposition"
    for (name, expected) in definitions do
      let some (.defnInfo _) := env.find? name
        | throwError "missing definition endpoint {name}"
      let some index := env.getModuleIdxFor? name
        | throwError "no imported compiler origin for {name}"
      let origin := header.moduleNames[index.toNat]!
      unless origin == expected do
        throwError "{name} has origin {origin}; expected {expected}"
    let allowed := [``propext, ``Classical.choice, ``Quot.sound]
    let mut counts : Array Nat := Array.replicate modules.size 0
    let mut owned : Array Lean.Name := #[]
    for (name, info) in env.constants.toList do
      if let some index := env.getModuleIdxFor? name then
        let origin := header.moduleNames[index.toNat]!
        for i in [:modules.size] do
          if origin == modules[i]! then
            if let .axiomInfo _ := info then
              throwError "new axiom {name} in {origin}"
            match info with
            | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
              unless (info.value? true).isSome do
                throwError "missing definition or proof body {name} in {origin}"
            | _ => pure ()
            owned := owned.push name
            counts := counts.set! i (counts[i]! + 1)
    -- Lean's own export hook shares this exact collector state across roots. The returned
    -- cache entry isolates each root's dependencies; the accumulated state is not inspected.
    let entries := Lean.CollectAxioms.runM (env.setExporting false) do
      owned.mapM fun name =>
        return (name, ← Lean.CollectAxioms.collectAndGet (fun _ _ => none) name)
    for (name, axioms) in entries do
      let unexpected := axioms.filter fun ax => !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "unapproved transitive axioms for {name}: {unexpected.toList}"
    for i in [:modules.size] do
      if facades.contains modules[i]! then
        unless counts[i]! == 0 do
          throwError "import-only facade {modules[i]!} unexpectedly owns declarations"
        Lean.logInfo m!"GXMSS_TRUST_AUDIT_FACADE {modules[i]!}: zero owned declarations"
      else
        if counts[i]! == 0 then
          throwError "zero audit coverage for {modules[i]!}"
        Lean.logInfo m!"GXMSS_TRUST_AUDIT {modules[i]!}: {counts[i]!} declarations"

end GXMSS.Test.TrustAudit
