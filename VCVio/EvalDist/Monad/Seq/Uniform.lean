/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Seq.Measure
public import ToMathlib.Probability.UniformOn

/-!
# Combining independent uniform draws

A bijective binary operation transports two independent uniform draws to a uniform draw.
The operation's codomain can carry its own measurable structure.
-/

public section

open MeasureTheory ProbabilityTheory

universe u v

/-- A measurable bijective combination of independent finite uniform draws is uniform. -/
theorem evalDist_seq_map_eq_uniformOn {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β γ : Type u}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    [Finite α] [Finite β] [Nonempty α] [Nonempty β]
    (mx : m α) (my : m β) (f : α → β → γ)
    (hx : 𝒟[mx] = uniformOn Set.univ) (hy : 𝒟[my] = uniformOn Set.univ)
    (hf : Measurable (Function.uncurry f)) (hbij : Function.Bijective (Function.uncurry f)) :
    𝒟[f <$> mx <*> my] = uniformOn Set.univ := by
  let : Finite γ := Finite.of_surjective _ hbij.surjective
  let : Nonempty γ := Nonempty.map (Function.uncurry f) inferInstance
  rw [evalDist_seq_map mx my f hf, hx, hy, ← uniformOn_univ_prod]
  exact map_uniformOn_univ_of_bijective hf hbij
