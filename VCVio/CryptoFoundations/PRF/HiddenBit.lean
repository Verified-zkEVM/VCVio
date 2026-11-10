/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.PRF

/-!
# Hidden-bit PRF distinguishers

A reduction to PRF security often draws a hidden bit `b`, runs a game `run b` that uses the
distinguisher's function oracle, and outputs whether the game's guess is `b`. In either world of
the PRF game its success probability is the average of the two branches in that world: the
probability that the game at bit `true` outputs `true` and the probability that the game at bit
`false` outputs `false`. If the two branches have the same output distribution in the ideal
world, comparing the two worlds bounds the gap between the branches in the real world by twice
the PRF advantage.

## Main statements

* `PRFScheme.prfRealExperiment_guessBit`: the success probability in the real world is
  `(p₁ + q₀) / 2`, where `p₁` is the probability that the game at bit `true` outputs `true` and
  `q₀` that the game at bit `false` outputs `false`, each in the real world.
* `PRFScheme.prfIdealExperiment_guessBit`: the same in the ideal world.
* `PRFScheme.absDiff_prfRealExperiment_eq_two_mul_prfAdvantage`: if the two branches output
  `true` with the same probability in the ideal world, the gap between them in the real world is
  twice the advantage of the hidden-bit distinguisher.
-/

public section

open OracleComp OracleSpec

namespace PRFScheme

variable {K D R : Type}

/-- A uniform hidden bit is guessed with the average probability of the two branches: the guess
`true` at bit `true` and the guess `false` at bit `false`. -/
private lemma prEvent_uniformBool_guess (f : Bool → ProbComp Bool) :
    Pr{let x ← (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let g ← f b
        return decide (g = b))}[x = true] =
      (Pr{let g ← f true}[g = true] + Pr{let g ← f false}[g = false]) / 2 := by
  rw [prEvent_bind_eq_sum_fintype, Fintype.sum_bool]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool, bind_pure_comp,
    prEvent_map, decide_eq_true_eq]
  rw [ENNReal.div_eq_inv_mul, mul_add]
  norm_num

/-- **The hidden-bit distinguisher in the real world.** The distinguisher that draws a uniform bit
`b`, runs `run b` and outputs whether its guess is `b` outputs `true` in the real experiment with
probability `(p₁ + q₀) / 2`, where `p₁` is the probability that `run true` outputs `true` and `q₀`
that `run false` outputs `false`, each in the real experiment. -/
theorem prfRealExperiment_guessBit (prf : PRFScheme K D R) (run : Bool → PRFAdversary D R) :
    Pr{let g ← prf.prfRealExperiment (do
        let b ← (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (PRFOracleSpec D R) Bool)
        let g ← run b
        return decide (g = b) : OracleComp (PRFOracleSpec D R) Bool)}[g = true] =
      (Pr{let g ← prf.prfRealExperiment (run true)}[g = true] +
        Pr{let g ← prf.prfRealExperiment (run false)}[g = false]) / 2 := by
  rw [← prEvent_uniformBool_guess fun b => prf.prfRealExperiment (run b)]
  have h : prf.prfRealExperiment (do
        let b ← (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (PRFOracleSpec D R) Bool)
        let g ← run b
        return decide (g = b) : OracleComp (PRFOracleSpec D R) Bool) =ᵈ (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let g ← prf.prfRealExperiment (run b)
        return decide (g = b)) := by
    simp only [prfRealExperiment, simulateQ_bind, ← liftComp_eq_liftM,
      simulateQ_prfRealQueryImpl_liftComp, simulateQ_pure, bind_assoc]
    exact EvalDistEq.bind_bind_swap _ _ _
  exact h.prEvent_eq _

/-- **The hidden-bit distinguisher in the ideal world.** The distinguisher that draws a uniform bit
`b`, runs `run b` and outputs whether its guess is `b` outputs `true` in the ideal experiment with
probability `(p₁ + q₀) / 2`, where `p₁` is the probability that `run true` outputs `true` and `q₀`
that `run false` outputs `false`, each in the ideal experiment. -/
theorem prfIdealExperiment_guessBit [DecidableEq D] [SampleableType R]
    (run : Bool → PRFAdversary D R) :
    Pr{let g ← prfIdealExperiment (do
        let b ← (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (PRFOracleSpec D R) Bool)
        let g ← run b
        return decide (g = b) : OracleComp (PRFOracleSpec D R) Bool)}[g = true] =
      (Pr{let g ← prfIdealExperiment (run true)}[g = true] +
        Pr{let g ← prfIdealExperiment (run false)}[g = false]) / 2 := by
  rw [← prEvent_uniformBool_guess fun b => prfIdealExperiment (run b)]
  have h : prfIdealExperiment (do
        let b ← (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (PRFOracleSpec D R) Bool)
        let g ← run b
        return decide (g = b) : OracleComp (PRFOracleSpec D R) Bool) = (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let g ← prfIdealExperiment (run b)
        return decide (g = b)) := by
    simp only [prfIdealExperiment, simulateQ_bind, ← liftComp_eq_liftM,
      simulateQ_prfIdealQueryImpl_liftComp, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
      StateT.run_monadLift]
    simp
  rw [h]

/-- **The hidden-bit reduction loses a factor of two.** If the two branches output `true` with the
same probability in the ideal world, the gap between their probabilities of outputting `true` in
the real world is twice the PRF advantage of the hidden-bit distinguisher. -/
theorem absDiff_prfRealExperiment_eq_two_mul_prfAdvantage [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (run : Bool → PRFAdversary D R)
    (hideal : Pr{let g ← prfIdealExperiment (run true)}[g = true] =
      Pr{let g ← prfIdealExperiment (run false)}[g = true]) :
    ENNReal.absDiff (Pr{let g ← prf.prfRealExperiment (run true)}[g = true])
        (Pr{let g ← prf.prfRealExperiment (run false)}[g = true]) =
      2 * prf.prfAdvantage (do
        let b ← (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (PRFOracleSpec D R) Bool)
        let g ← run b
        return decide (g = b) : OracleComp (PRFOracleSpec D R) Bool) := by
  rw [prfAdvantage, MeasureTheory.Measure.boolDist, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton, prfRealExperiment_guessBit, prfIdealExperiment_guessBit]
  simp only [← Bool.not_eq_true, prEvent_not_eq_one_sub, hideal]
  set p₁ := Pr{let g ← prf.prfRealExperiment (run true)}[g = true]
  set p₀ := Pr{let g ← prf.prfRealExperiment (run false)}[g = true]
  set q := Pr{let g ← prfIdealExperiment (run false)}[g = true]
  have h₁ : p₁ ≤ 1 := prEvent_le_one _
  have h₀ : p₀ ≤ 1 := prEvent_le_one _
  have hq : q ≤ 1 := prEvent_le_one _
  have hne : ∀ x : ENNReal, x ≤ 1 → x ≠ ⊤ := fun x hx => ne_top_of_le_ne_top ENNReal.one_ne_top hx
  have hhalf : ∀ x y : ENNReal, x ≤ 1 → (x + (1 - y)) / 2 ≠ ⊤ := fun x y hx =>
    ENNReal.div_ne_top (ENNReal.add_ne_top.mpr ⟨hne x hx, ENNReal.sub_ne_top ENNReal.one_ne_top⟩)
      two_ne_zero
  have htop : ∀ a b : ENNReal, a ≠ ⊤ → b ≠ ⊤ → ENNReal.absDiff a b ≠ ⊤ := fun a b ha hb =>
    ENNReal.add_ne_top.mpr ⟨ENNReal.sub_ne_top ha, ENNReal.sub_ne_top hb⟩
  rw [← ENNReal.toReal_eq_toReal_iff' (htop _ _ (hne _ h₁) (hne _ h₀))
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (htop _ _ (hhalf _ _ h₁) (hhalf _ _ hq))),
    ENNReal.toReal_mul, ENNReal.absDiff_toReal (hne _ h₁) (hne _ h₀),
    ENNReal.absDiff_toReal (hhalf _ _ h₁) (hhalf _ _ hq)]
  simp only [ENNReal.toReal_div,
    ENNReal.toReal_add (hne _ h₁) (ENNReal.sub_ne_top ENNReal.one_ne_top),
    ENNReal.toReal_add (hne _ hq) (ENNReal.sub_ne_top ENNReal.one_ne_top),
    ENNReal.toReal_sub_of_le h₀ ENNReal.one_ne_top, ENNReal.toReal_sub_of_le hq ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [show (p₁.toReal + (1 - p₀.toReal)) / 2 - (q.toReal + (1 - q.toReal)) / 2 =
    (p₁.toReal - p₀.toReal) / 2 by ring, abs_div, abs_two]
  ring

end PRFScheme
