/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Examples.MeasurableServices.CompiledRejection

/-!
# Deterministic tape checks for counted rejection sampling

Run the same composed machine as the joint-law theorem. Administration consumes
fuel but no random bits. Pauses inside an attempt retain its first bit and retry
counter, and successful execution leaves the supplied tape suffix untouched.
-/

public section

open PFunctor ResumptionRejection

namespace RejectionTimingTest

private def tape : Handler (StateT (List Bool) Option) (coinSpec.toPFunctor + PFunctor.y) :=
  fun q bits => match q with
  | .inl _ => match bits with
    | [] => none
    | b :: rest => some (b, rest)
  | .inr _ => some (PUnit.unit, bits)

/-- Run the compiled machine and expose its value, retry count, and unused tape. -/
def inspect (fuel : ℕ) (bits : List Bool) : Option (Option (ℕ × ℕ) × List Bool) := do
  let (chunk, rest) ← compiledMachine.runChunk tape fuel (compiledMachine.init (0, ())) bits
  return (chunk.result.map (fun out => (out.1.1.val, out.1.2)), rest)

/-- Pause after the first bit, then resume through rejection and a successful second attempt. -/
def resumed : Option (Option (ℕ × ℕ) × List Bool) := do
  let (first, rest) ← compiledMachine.runChunk tape 2 (compiledMachine.init (0, ()))
    [true, true, false, true, false]
  let (last, rest) ← (compiledMachine.resumeChunk 6 first).liftM tape rest
  return (last.result.map (fun out => (out.1.1.val, out.1.2)), rest)

/-- Exact runtime checks of the composed fair-bit sampler, including retained partial work. -/
def run : IO Unit := do
  let check (name : String) (actual expected : Option (Option (ℕ × ℕ) × List Bool)) := do
    unless actual == expected do
      throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")
  check "zero fuel" (inspect 0 [true]) (some (none, [true]))
  check "accepted zero" (inspect 4 [false, false, true]) (some (some (0, 0), [true]))
  check "accepted one" (inspect 4 [false, true, true]) (some (some (1, 0), [true]))
  check "accepted two" (inspect 4 [true, false, true]) (some (some (2, 0), [true]))
  check "retry then accept" (inspect 8 [true, true, false, true, false])
    (some (some (1, 1), [false]))
  check "pause before administrative return" (inspect 3 [false, false, true])
    (some (none, [true]))
  check "resume without replay" resumed (some (some (1, 1), [false]))
  check "exhausted tape" (inspect 4 [false]) none
  IO.println "Counted rejection sampling: 8 deterministic tape cases passed"

end RejectionTimingTest
