/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio

/-!
# Native probability tactic gate

The measure-side counterpart of `VCVioTest/ProbabilityTactics.lean`: goal families stated with
`𝒟[…]` and `Pr{…}[…]`, each closed by one terminal tactic, following the conventions of
`CONTRIBUTING.md` (*Tactic Gate Files*). `simp` closes constant, pure, uniform, lossless and
failure facts in measure normal form; bind-swap and shared-prefix congruence go through the
`vcstep` planner.
-/

public section

open MeasureTheory ProbabilityTheory OracleComp OracleSpec
open scoped ENNReal

namespace VCVioTest.NativeProbabilityTactics

/-! ## Pure and constant programs -/

example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] {x} = 1 := by simp
example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] = Measure.dirac x := by simp
example (mx : ProbComp (Fin 2)) (my : ProbComp (Fin 3)) : 𝒟[mx >>= fun _ => my] = 𝒟[my] := by
  simp
example (mx : ProbComp (Fin 2)) (b : Fin 3) : 𝒟[(fun _ => b) <$> mx] = Measure.dirac b := by
  simp

-- target(simp): over a discarded `Bool`, Mathlib's `simp` rewrites `(Set.univ : Set Bool)` to
-- `{false, true}` before the lossless-mass rule sees it; the oracle-specific law closes the goal.
example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) : 𝒟[mx >>= fun _ => my] = 𝒟[my] :=
  OracleComp.evalDist_bind_const mx my

/-! ## Uniform samples -/

example (x : Fin 6) : 𝒟[$ᵗ Fin 6] {x} = 6⁻¹ := by simp
-- target(simp): the uniform event law fires first and leaves the arithmetic `2 / 2 = 1`.
example : Pr{let _ ← ($ᵗ Bool : ProbComp Bool)}[True] = 1 :=
  OracleComp.prEvent_true_eq_one _

/-! ## Losslessness -/

example (mx : ProbComp (Fin 3)) : 𝒟[mx] Set.univ = 1 := by simp
example (mx : ProbComp (Fin 3)) : IsProbabilityMeasure 𝒟[mx] := inferInstance

/-! ## Failure is missing mass -/

example : 𝒟[(failure : OptionT ProbComp Bool)] = 0 := by simp
example (mx : OptionT ProbComp Bool) :
    𝒟[mx >>= fun _ => (failure : OptionT ProbComp Bool)] = 0 := by simp
example (mx : ProbComp Bool) : Pr{let _ ← mx}[False] = 0 := by simp

/-! ## Independent products -/

example (f : Bool → ProbComp (Fin 3)) (v : Bool → Fin 3) :
    𝒟[Fintype.mPi f] {v} = ∏ i, 𝒟[f i] {v i} := by
  simp [evalDist_mPi]

/-! ## Swaps and congruence through the planner -/

example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) (f : Bool → Fin 3 → ProbComp Bool) :
    Pr{let r ← mx >>= fun a => my >>= fun b => f a b}[r = true] =
      Pr{let r ← my >>= fun b => mx >>= fun a => f a b}[r = true] := by
  vcstep

example (mx : ProbComp Bool) (f g : Bool → ProbComp (Fin 3)) (y : Fin 3)
    (h : ∀ b ∈ support mx, 𝒟[f b] {y} = 𝒟[g b] {y}) :
    𝒟[mx >>= f] {y} = 𝒟[mx >>= g] {y} := by
  vcstep
  exact h _ ‹_›

example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) (f : Bool → Fin 3 → ProbComp Bool) :
    𝒟[mx >>= fun a => my >>= fun b => f a b] = 𝒟[my >>= fun b => mx >>= fun a => f a b] := by
  vcstep

end VCVioTest.NativeProbabilityTactics
