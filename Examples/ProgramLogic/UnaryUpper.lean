/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Upper bounds with `prvcgen`

The reading of oracle computations that cryptographic statements use most: an event has
probability at most `ε`. Each example states the bound as `Pr{…}[…] ≤ ε` and lets `prvcgen` run
core's `vcgen` in the upper-bound reading (`OracleComp.Upper`), whose registered rules bound a
draw by its largest outcome and whose averaging rules, passed in brackets, bound it by its exact
average.

* a guessing game: a guess of a fresh uniform key succeeds with probability at most `1 / |K|`,
  whatever the adversary's distribution, by reading the adversary on its support and the key by
  its average;
* an event that cannot happen is below every event, the comparison form `Pr{A}[p] ≤ Pr{B}[q]`;
* an event of an aborting (`OptionT`) program, where a failure costs nothing;
* the readback of a bare `vcgen`'s verification conditions with the simp set `upper_readback`.
-/

public section

open OracleSpec OracleComp Std.WP ENNReal OrderDual

namespace Examples.ProgramLogic.UnaryUpper

/-- An adversary commits to a guess, then a key is drawn uniformly; the game accepts when the
guess is the key. The adversary sees nothing, so committing first loses no generality, and
it is the order the program logic reads directly: the adversary's draw is opaque and the key's
draw is averaged. -/
def guessGame (K : Type) [SampleableType K] [DecidableEq K] (adv : ProbComp K) : ProbComp Bool :=
  do
    let k' ← adv
    let k ← $ᵗ K
    pure (decide (k = k'))

/-- The guess succeeds with probability at most `1 / |K|`: the adversary's output is read on
its support (`Spec.ofSupport`, passed since it applies to every program), and the key by the
averaging rule `Spec.uniformSample_avg`, which leaves the average of an indicator. -/
theorem guessGame_le {K : Type} [SampleableType K] [Fintype K] [DecidableEq K]
    (adv : ProbComp K) :
    Pr{let b ← guessGame K adv}[b = true] ≤ (Fintype.card K : ℝ≥0∞)⁻¹ := by
  prvcgen [guessGame, OracleComp.Upper.Spec.ofSupport adv,
    OracleComp.Upper.Spec.uniformSample_avg]
  simp [propInd_eq_ite]

/-- An event that cannot happen is below every event: the comparison is read as an upper bound
on the left-hand side with the right-hand side as the bound, and the registered rule bounds the
draw on the left by its largest outcome. -/
example {K : Type} [SampleableType K] (adv : ProbComp K) (T : Finset K) [DecidableEq K] :
    Pr{let k ← $ᵗ K}[k ∈ T ∧ k ∉ T] ≤ Pr{let k' ← adv}[k' ∈ T] := by
  prvcgen
  simp [propInd_eq_ite]

/-- An aborting program: the game rejects a guess outside the admissible set `T` before the
key is drawn. The event is read through the transformer's bridge, which charges an abort
nothing, and the lifted adversary and sample through core's lift rule. -/
def guessOrAbort (K : Type) [SampleableType K] [DecidableEq K] (T : Finset K)
    (adv : ProbComp K) : OptionT ProbComp Bool := do
  let k' ← OptionT.lift adv
  guard (k' ∈ T)
  let k ← OptionT.lift ($ᵗ K)
  pure (decide (k = k'))

theorem guessOrAbort_le {K : Type} [SampleableType K] [Fintype K] [DecidableEq K]
    (T : Finset K) (adv : ProbComp K) :
    Pr{let b ← guessOrAbort K T adv}[b = true] ≤ (Fintype.card K : ℝ≥0∞)⁻¹ := by
  prvcgen [guessOrAbort, OracleComp.Upper.Spec.ofSupport adv,
    OracleComp.Upper.Spec.uniformSample_avg]
  all_goals simp [propInd_eq_ite]

open scoped OracleComp.Upper in
/-- A bare `vcgen` on a triple of the reading leaves its verification condition in the dual
vocabulary; `simp only [upper_readback]` turns it into an inequality in `ℝ≥0∞`, before any other
`simp` can rewrite the dual numerals. -/
example : ⦃ toDual 0 ⦄ (do let b ← $ᵗ Bool; pure (b && !b) : ProbComp Bool)
    ⦃ fun r => toDual (propInd (r = true)) ⦄ := by
  vcgen
  simp only [upper_readback]
  simp [propInd_eq_ite]

end Examples.ProgramLogic.UnaryUpper
