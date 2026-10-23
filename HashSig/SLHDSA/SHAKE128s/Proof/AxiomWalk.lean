/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Axioms
public import HashSig.SLHDSA.SHAKE128s.Statement.Theorems.StrongUnforgeability

/-!
# The soundness invariant, checked by walking the environment

`Axioms.lean` pins each public theorem's axioms individually with a `#guard_msgs`-guarded
`#print axioms`. That list is worth keeping: a theorem *silently acquiring* `Classical.choice`
shows up in its diff, which a blanket check cannot see.

But a list is a check that something **else** stayed in sync, so it decays the moment a theorem
is added without a line, and the sweep in `scripts/guard_sweep.py` buys detection rather than
prevention. This file is the invariant that cannot decay: one command that walks every
declaration under `SlhDsaSecurity` and fails the build if any depends on an axiom outside the
three Mathlib's classical reasoning rests on. Nothing to keep in sync, nothing to forget, and a
new theorem is covered the moment it compiles — including one nobody thought to list.

It is the library's root, so it imports the theorem and `Axioms.lean` and sees every declaration.
-/

@[expose] public section

open Lean Elab Command

namespace SlhDsaSecurity.AxiomWalk

/-- The only axioms this development is permitted to rest on. `sorryAx` is deliberately absent,
so a `sorry` anywhere under `SlhDsaSecurity` fails the build here even if it is never printed. -/
def permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut offenders : Array (Name × Name) := #[]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    unless name.isInternal do
      if (`SlhDsaSecurity).isPrefixOf name then
        checked := checked + 1
        for ax in (← liftCoreM (Lean.collectAxioms name)) do
          unless permitted.contains ax do
            offenders := offenders.push (name, ax)
  unless offenders.isEmpty do
    let lines := offenders.toList.map fun (n, ax) => s!"  {n} depends on {ax}"
    throwError "axiom walk: {offenders.size} declaration(s) rest on an axiom outside \
      \{propext, Classical.choice, Quot.sound}:\n{"\n".intercalate lines}"
  logInfo s!"axiom walk: {checked} declarations, none outside the permitted three"

end SlhDsaSecurity.AxiomWalk
