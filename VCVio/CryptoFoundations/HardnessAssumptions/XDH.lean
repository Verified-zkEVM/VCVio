/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-! # External Diffie–Hellman

XDH is DDH in the first source group of a Type 3 bilinear group, with the second generator
and the pairing public. The name external Diffie–Hellman follows the literature of
Ballard, Green, de Medeiros and Monrose, and Boneh, Boyen and Shacham.

These experiments define the distinguishing problem. They impose no hardness or resource
assumption: an adversary may close over the public pairing and other system parameters.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace XDH

/-- An XDH adversary receives `g₁, a • g₁, b • g₁, T, g₂`. The scalar field is a phantom
parameter; the public pairing can be captured by the adversary. -/
@[expose] def Adversary (_F G₁ G₂ : Type) := G₁ → G₁ → G₁ → G₁ → G₂ → ProbComp Bool

/-- The real XDH experiment supplies a genuine Diffie–Hellman triple in the first source
group and the public second-source generator. -/
@[expose] def realExperiment {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F G₁ G₂) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  A g₁ (a • g₁) (b • g₁) ((a * b) • g₁) g₂

/-- The random XDH experiment supplies an independent random scalar multiple as the
fourth first-source element, with the same public second-source generator. -/
@[expose] def randomExperiment {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F G₁ G₂) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let c ← $ᵗ F
  A g₁ (a • g₁) (b • g₁) (c • g₁) g₂

/-- XDH advantage is the Boolean distance between the real and random experiments. -/
@[expose] noncomputable def advantage {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F G₁ G₂) : ℝ≥0∞ :=
  𝒟[realExperiment g₁ g₂ A].boolDist 𝒟[randomExperiment g₁ g₂ A]

end XDH
