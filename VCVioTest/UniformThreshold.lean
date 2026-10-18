/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Coinductive.UniformThreshold.Budget
public import VCVio.OracleComp.Coinductive.UniformThreshold.Categorical

/-!
# Deterministic tape checks for the persistent threshold machine

The tape handler fails when it runs out of supplied bits. These checks exercise exact
endpoints, non-dyadic thresholds, timeout, and retained state. They do not use a statistical
test or a production RNG assumption.
Categorical checks exercise the actual IO sampler with normalized rational ticket arrays.
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

/-- A second threshold depends on the first answer and shares its random prefix. -/
def adaptive : FreeM spec.toPFunctor Bool := do
  let answer ← FreeM.lift (P := spec.toPFunctor) (1 / 3)
  FreeM.lift (P := spec.toPFunctor) (if answer then 1 / 4 else 2 / 3)

/-- Observe failure, retained prefix, remaining allowance, and unconsumed random bits jointly. -/
def inspectBudget (cap : ℚ → Budget.Session → ℕ) (allowance : ℚ≥0) (bits : List Bool) :
    Option (Except Budget.Failure Bool × ℕ × ℕ × ℚ≥0 × List Bool) := do
  let (out, rest) ← (Budget.run cap adaptive (Prefix.empty, allowance)).liftM tape bits
  return (out.1, out.2.1.depth, out.2.1.cell, out.2.2, rest)

private def categoricalZeros : FinRatPMF.Raw Nat :=
  ⟨#[(0, 0), (1, 1 / 3), (99, 0), (2, 2 / 3)], by norm_num⟩

private def categoricalDuplicates : FinRatPMF.Raw Nat :=
  ⟨#[(7, 1 / 3), (7, 2 / 3)], by norm_num⟩

private def categoricalQuarters : FinRatPMF.Raw Nat :=
  ⟨#[(0, 1 / 4), (1, 1 / 2), (2, 1 / 4)], by norm_num⟩

private def checkCategorical (label : String) (distribution : FinRatPMF.Raw Nat)
    (bits : List Bool) (expected : Nat) (remaining : List Bool) : IO Unit := do
  let source ← IO.mkRef bits
  let draw : IO Bool := do
    match ← source.get with
    | [] => throw (IO.userError s!"{label}: unexpected bit query")
    | bit :: rest => source.set rest; return bit
  let out ← Categorical.sampleIO distribution draw
  let rest ← source.get
  unless out == expected && rest == remaining do
    throw (IO.userError s!"{label}: got {out} and {rest}, expected {expected} and {remaining}")

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
  let checkBudget (label : String)
      (actual expected : Option (Except Budget.Failure Bool × ℕ × ℕ × ℚ≥0 × List Bool)) := do
    unless actual == expected do
      throw (IO.userError s!"{label}: joint budget, output, prefix, or tape observation differs")
  checkBudget "refusal before sampling" (inspectBudget (fun _ _ => 2) (1 / 8) [false, true])
    (some (.error .budgetExhausted, 0, 0, 1 / 8, [false, true]))
  checkBudget "timeout keeps debit and bits" (inspectBudget (fun _ _ => 1) 1 [false, false, true])
    (some (.error .timeout, 1, 0, 1 / 2, [false, true]))
  checkBudget "zero-cap timeout" (inspectBudget (fun _ _ => 0) 1 [true])
    (some (.error .timeout, 0, 0, 0, [true]))
  checkBudget "adaptive client reuses prefix" (inspectBudget (fun _ _ => 2) 1 [false, false, true])
    (some (.ok true, 2, 0, 1 / 2, [true]))
  checkBudget "adaptive cap preserves allowance"
    (inspectBudget (fun _ state => 2 + state.1.depth) 1 [false, false, true])
    (some (.ok true, 2, 0, 11 / 16, [true]))
  checkBudget "later refusal keeps earlier effects"
    (inspectBudget (fun _ state => if state.1.depth = 0 then 2 else 0) 1 [false, false, true])
    (some (.error .budgetExhausted, 2, 0, 3 / 4, [true]))
  checkBudget "half allowance needs no counter"
    (inspectBudget Budget.halfAllowanceCap (1 / 2) [true, false, false, true])
    (some (.ok true, 3, 4, 11 / 32, [true]))
  checkBudget "half allowance timeout retains positive reserve"
    (inspectBudget Budget.halfAllowanceCap (1 / 2) [false, true, false, true])
    (some (.error .timeout, 3, 2, 3 / 8, [true]))
  checkBudget "half allowance zero refuses before bits"
    (inspectBudget Budget.halfAllowanceCap 0 [true])
    (some (.error .budgetExhausted, 0, 0, 0, [true]))
  checkCategorical "singleton needs no bits" (pure 9) [] 9 []
  checkCategorical "zero weights below" categoricalZeros [false, false, true] 1 [true]
  checkCategorical "repeated thresholds above" categoricalZeros [true, false] 2 [false]
  checkCategorical "duplicate outcome below" categoricalDuplicates [false, false, true] 7 [true]
  checkCategorical "duplicate outcome above" categoricalDuplicates [true, false] 7 [false]
  checkCategorical "lower quarter" categoricalQuarters [false, false, true] 0 [true]
  checkCategorical "middle reuses prefix" categoricalQuarters [false, true, true] 1 [true]
  checkCategorical "upper quarter" categoricalQuarters [true, true, false] 2 [false]
  IO.println "Persistent threshold and categorical sampling: 27 deterministic tape cases passed"

end UniformThresholdTest
