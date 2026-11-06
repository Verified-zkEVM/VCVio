/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio

/-!
# Uniform permutations extending a finite trace

A fresh edge programmed by an output swap sends the uniform permutation to the uniform permutation
extending that edge, and the swap installs the edge. Uniform preimage resampling keeps the uniform
law.
-/

public section

open OracleComp OracleComp.PermutationConditioning OracleComp.UniformPreimage

namespace VCVioTest.RandomPermutationConditioning

variable {α : Type}

/-- The empty trace is satisfied by every permutation. -/
theorem extensions_nil_nonempty : Nonempty (Extensions ([] : List (α × α))) :=
  ⟨⟨1, by simp⟩⟩

/-- Every fixed edge is fresh for the empty trace. -/
theorem freshProgram_singleton (x y : α) : FreshProgram [] [(x, y)] where
  sourcesNodup := by simp
  targetsNodup := by simp
  inputsFresh := by simp
  outputsFresh := by simp

example [DecidableEq α] (p : Equiv.Perm α) (x y : α) : install p [(x, y)] x = y := by
  simp [install]

example [DecidableEq α] [Fintype α] (x y : α) :
    (letI : MeasurableSpace (Equiv.Perm α) := ⊤;
    𝒟[(fun p => install p [(x, y)]) <$> uniformPermutations [] extensions_nil_nonempty] =
      𝒟[uniformPermutations ([] ++ [(x, y)])
        (extensions_append_nonempty _ _ (freshProgram_singleton x y) extensions_nil_nonempty)]) :=
  map_install_uniformPermutations _ _ (freshProgram_singleton x y) extensions_nil_nonempty

example {A B : Type} [DecidableEq A] [Fintype B] [SampleableType B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (ψ : B → A) (hψ : Function.Surjective ψ) :
    𝒟[do let b ← $ᵗ B; sampleUniformPreimage ψ hψ (ψ b)] = 𝒟[$ᵗ B] :=
  bind_sampleUniformPreimage_eq_uniform ψ hψ

end VCVioTest.RandomPermutationConditioning
