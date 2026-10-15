/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Events of programs with failure and exceptions

An event of an `OptionT` or `ExceptT` program over an oracle computation counts the runs that
return a value: a failure or an exception contributes nothing. `prvcgen` reads such an event
through core's lift of the reading, with the exception assertion stating what a failure is worth:
nothing under the bound readings (`fun _ => toDual 0`), and forbidden under the necessary and
possible readings (`fun _ => False`), so that a guard's condition becomes a verification
condition.

| Statement | Reading | Failure |
|---|---|---|
| `Pr{…}[p] = 1` | necessary, lifted | forbidden: the guard's condition is a condition |
| `Pr{…}[p] ≤ ε`, `= 0` | upper bound, lifted | worth `0` |
| `0 < Pr{…}[p]` | possible, lifted | forbidden: a successful run is named |
| `r ≤ Pr{…}[p]` | lower bound, lifted | worth `0` |
-/

public section

open OracleSpec OracleComp Std.WP ENNReal

namespace Examples.ProgramLogic.TransformerEvents

/-- A draw that fails when the guard's condition is false. -/
def guardedCoin (ok : Prop) [Decidable ok] : OptionT ProbComp Bool := do
  guard ok
  OptionT.lift ($ᵗ Bool)

/-- Necessary: with the guard open, every run returns a coin, so the tautology has probability
one. The lifted reading forbids failure, which leaves the guard's condition `1 < 2` as a
verification condition beside the coin's. -/
example : Pr{let b ← guardedCoin (1 < 2)}[(b || !b) = true] = 1 := by
  prvcgen [guardedCoin]
  all_goals simp_all

/-- Upper bound: with the guard closed, every run fails, and a failure is worth nothing, so any
event has probability zero. The guard's rule keeps its condition as a hypothesis of the
continuation, which is contradictory here. -/
example : Pr{let b ← guardedCoin (2 < 1)}[b = true] = 0 := by
  prvcgen [guardedCoin]
  rename_i h _
  exact absurd h.down (by decide)

/-- Possible: with the guard open, some run returns `true`. The lifted possible reading asks for
the guard's condition and a witness for the coin. -/
example : 0 < Pr{let b ← guardedCoin (1 < 2)}[b = true] := by
  prvcgen [guardedCoin]
  all_goals simp_all

/-- A program given by `OptionT.mk` on an underlying computation returning an option: the lifted
readings see the option its body returns. -/
example : Pr{let b ← (OptionT.mk ((fun b => some b) <$> ($ᵗ Bool)) : OptionT ProbComp Bool)}[
    (b || !b) = true] = 1 := by
  prvcgen
  simp

/-- An exceptional program: the draw decides between a value and an exception. -/
def coinOrThrow : ExceptT String ProbComp Bool := do
  let b ← ExceptT.lift ($ᵗ Bool)
  if b then pure b else throw "tails"

/-- Upper bound: an exception is worth nothing, so the event that the returned coin is `false`
has probability zero, since the program throws instead. -/
example : Pr{let b ← coinOrThrow}[b = false] = 0 := by
  prvcgen [coinOrThrow]
  all_goals simp_all

/-- Possible: some run returns `true`. The lifted possible reading names the run through the
draw; the `if` is read once the witness is fixed. -/
example : 0 < Pr{let b ← coinOrThrow}[b = true] := by
  prvcgen [coinOrThrow]
  refine ⟨true, ?_⟩
  simp only [binderNameHint, ite_true]
  prvcgen

end Examples.ProgramLogic.TransformerEvents
