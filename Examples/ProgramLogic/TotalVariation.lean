/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics.PrVCGen
public import VCVio.ProgramLogic.Tactics.Relational

/-!
# Distances between programs

The event-keyed total variation `etvDist mx my` is the largest discrepancy between the
probabilities of an event under two programs, which may live in different monads. It bounds
every event, contracts under a common continuation, and composes along a bind, a bad event and
a hybrid chain; an approximate relational triple `ApproxRelTriple ε oa ob R` is a coupling that
relates the outputs by `R` except with probability `ε`, and composes by the same rules.

| Statement | Lemma or tactic |
|---|---|
| an event's probability moves by at most the distance | `absDiff_prEvent_le_etvDist` |
| continuations that differ only after a bad draw | `etvDist_bind_bind_le_of_bad` |
| a chain of games | `etvDist_le_sum_etvDist_succ`, `by_dist hybrid` |
| approximate couplings: returned values, weakening, sequencing | `approxRelTriple_*`, `by_approx` |

`Examples/ProgramLogic/ProofMode.lean` shows `by_upto`, the identical-until-bad distance of two
simulations.
-/

public section

open ENNReal OracleSpec OracleComp OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic OracleComp.Rel.Quantitative

namespace Examples.ProgramLogic.TotalVariation

/-- A fair coin against a coin that always lands heads: the event "heads" differs by at most
their distance. -/
example : ENNReal.absDiff Pr{let b ← ($ᵗ Bool : ProbComp Bool)}[b = true]
    Pr{let b ← (pure true : ProbComp Bool)}[b = true] ≤
      etvDist ($ᵗ Bool : ProbComp Bool) (pure true : ProbComp Bool) :=
  absDiff_prEvent_le_etvDist _ _ _

/-- A die, then a continuation that is corrected on a bad face. -/
def corrected : ProbComp ℕ := do
  let d ← $[0..5]
  if d = 0 then pure 1 else pure d.val

/-- The same die with the continuation left alone. -/
def plain : ProbComp ℕ := do
  let d ← $[0..5]
  pure d.val

/-- The two programs differ only after the bad face `0`, so their distance is at most the
probability of that face: the bad-event rule charges the bad draw in full and the continuations
agree exactly elsewhere. -/
example : etvDist corrected plain ≤ Pr{let d ← ($[0..5] : ProbComp (Fin 6))}[d = 0] := by
  refine (etvDist_bind_bind_le_of_bad ($[0..5] : ProbComp (Fin 6)) _ _ (· = 0) 0
    fun d hd => ?_).trans ?_
  · simp [hd, etvDist_self]
  · simp

/-- A hybrid argument: an advantage bound on the last game of a chain gives one on the first,
adding the distances of the consecutive games. -/
example (games : ℕ → ProbComp Bool) (n : ℕ) (ε : ℝ≥0∞) (step : ℕ → ℝ≥0∞)
    (hbound : AdvBound (games n) ε)
    (hstep : ∀ i < n, etvDist (games i) (games (i + 1)) ≤ step i) :
    AdvBound (games 0) (ε + ∑ i ∈ Finset.range n, step i) := by
  by_dist hybrid games n
  · exact hbound
  · exact hstep

/-- Sequencing approximate couplings adds their errors: a prefix related by `R` except with
probability `ε₁`, then continuations related by `S` except with probability `ε₂`. -/
example {α β γ δ : Type} (oa : ProbComp α) (ob : ProbComp β) (fa : α → ProbComp γ)
    (fb : β → ProbComp δ) (R : RelPost α β) (S : RelPost γ δ) (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : ApproxRelTriple ε₁ oa ob R) (h₂ : ∀ a b, R a b → ApproxRelTriple ε₂ (fa a) (fb b) S) :
    ApproxRelTriple (ε₁ + ε₂) (oa >>= fa) (ob >>= fb) S :=
  approxRelTriple_bind h₁ h₂

/-- A uniform draw coupled with itself through the quantitative carrier: `by_approx` leaves the
quantitative triple, whose precondition `rvcgen` computes from the identity coupling, and the
comparison of that precondition with `1 - ε`. -/
example : ApproxRelTriple 0 ($ᵗ Bool : ProbComp Bool) ($ᵗ Bool : ProbComp Bool) (EqRel Bool) := by
  by_approx
  · rvcgen
  · simp [RelPost.indicator, EqRel]

end Examples.ProgramLogic.TotalVariation
