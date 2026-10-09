/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.EvalDist.Monad.Measure

/-!
# Shared ElGamal-family helpers

Small distribution lemmas shared by the plain and hashed ElGamal examples.
-/

@[expose] public section


open OracleComp OracleSpec ENNReal

namespace ElGamalExamples

variable {A M : Type} [AddGroup M]

/-- Uniform additive masking hides which payload was chosen from every continuation. -/
theorem evalDist_uniformMaskedCipher_bind_dist_indep
    {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {β : Type}
    [MeasurableSpace M] [DiscreteMeasurableSpace M] [MeasurableSingletonClass M]
    [Finite M] [Nonempty M] [MeasurableSpace β]
    (draw : m M) (huniform : 𝒟[draw] = ProbabilityTheory.uniformOn Set.univ)
    (head : A) (m₁ m₂ : M) (cont : A × M → m β) :
    𝒟[do let y ← draw; cont (head, m₁ + y)] =
      𝒟[do let y ← draw; cont (head, m₂ + y)] := by
  have h₁ := evalDist_bind_bijective_of_uniform draw huniform
    (m₁ + ·) (AddGroup.addLeft_bijective m₁) (fun y => cont (head, y))
  have h₂ := evalDist_bind_bijective_of_uniform draw huniform
    (m₂ + ·) (AddGroup.addLeft_bijective m₂) (fun y => cont (head, y))
  simpa [monad_norm] using h₁.trans h₂.symm

end ElGamalExamples
