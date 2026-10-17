/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.UniformThreshold

/-!
# Deterministic tape checks for the persistent threshold machine

The tape handler fails when it runs out of supplied bits. These checks exercise exact
endpoints, non-dyadic thresholds, timeout, and retained state. They do not use a statistical
test or a production RNG assumption.
-/

open PFunctor UniformThreshold

public section

namespace UniformThresholdTest

private def tape : Handler (StateT (List Bool) Option) coinSpec.toPFunctor := fun _ bits =>
  match bits with
  | [] => none
  | b :: rest => some (b, rest)

/-- Observe a bounded run and the exact unconsumed tape suffix. -/
def inspect (q : ℚ) (fuel : ℕ) (bits : List Bool) (p := Prefix.empty) :
    Option (Option Bool × ℕ × ℕ × List Bool) := do
  let (chunk, rest) ← (machine q).runChunk tape fuel p bits
  match chunk with
  | .done (b, p) => pure (some b, p.depth, p.cell, rest)
  | .paused p => pure (none, p.depth, p.cell, rest)

/-- Execute two one-bit chunks against the same tape state. -/
def resumed : Option (Option Bool × ℕ × ℕ × List Bool) := do
  let (first, rest) ← (machine (1 / 3)).runChunk tape 1 Prefix.empty [false, false, true]
  let (second, rest) ← ((machine (1 / 3)).resumeChunk 1 first).liftM tape rest
  match second with
  | .done (b, p) => pure (some b, p.depth, p.cell, rest)
  | .paused p => pure (none, p.depth, p.cell, rest)

/-- Run deterministic regression cases through the compiled generic chunk driver. -/
def run : IO Unit := do
  let check (label : String) (actual expected : Option (Option Bool × ℕ × ℕ × List Bool)) := do
    unless actual == expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  check "zero endpoint" (inspect 0 0 []) (some (some false, 0, 0, []))
  check "one endpoint" (inspect 1 0 []) (some (some true, 0, 0, []))
  check "lower half" (inspect (1 / 2) 1 [false]) (some (some true, 1, 0, []))
  check "upper half" (inspect (1 / 2) 1 [true]) (some (some false, 1, 1, []))
  check "cutoff" (inspect (1 / 3) 1 [false, false]) (some (none, 1, 0, [false]))
  check "non-dyadic true" (inspect (1 / 3) 2 [false, false]) (some (some true, 2, 0, []))
  check "non-dyadic false" (inspect (1 / 3) 1 [true, false])
    (some (some false, 1, 1, [false]))
  check "exhausted input" (inspect (1 / 3) 2 [false]) none
  check "retained prefix" (inspect (1 / 3) 0 [true] (Prefix.empty.push false |>.push false))
    (some (some true, 2, 0, [true]))
  check "resume" resumed (some (some true, 2, 0, [true]))
  IO.println "Persistent uniform threshold: 10 deterministic tape cases passed"

end UniformThresholdTest
