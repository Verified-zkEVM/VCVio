/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-! # Symmetric external Diffie–Hellman

SXDH is XDH in both source groups of a Type 3 bilinear group, in the terminology of
Ballard, Green, de Medeiros and Monrose, and Boneh, Boyen and Shacham.
The namespace `XDH₂` defines the second-source problem: DDH in `G₂`, with the first
source generator and the pairing public. Together with `XDH` this gives the two
constituent distinguishing problems of SXDH.

These experiments impose no hardness or resource assumption: an adversary may close
over the public pairing and other system parameters.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace XDH₂

/-- An XDH₂ adversary receives `g₂, a • g₂, b • g₂, T, g₁`. The scalar field is a phantom
parameter; the public pairing can be captured by the adversary. -/
@[expose] def Adversary (_F G₁ G₂ : Type) := G₂ → G₂ → G₂ → G₂ → G₁ → ProbComp Bool

/-- The real XDH₂ experiment supplies a genuine Diffie–Hellman triple in the second source
group and the public first-source generator. -/
@[expose] def realExperiment {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₂] [Module F G₂]
    (g₂ : G₂) (g₁ : G₁) (A : Adversary F G₁ G₂) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  A g₂ (a • g₂) (b • g₂) ((a * b) • g₂) g₁

/-- The random XDH₂ experiment supplies an independent random scalar multiple as the
fourth second-source element, with the same public first-source generator. -/
@[expose] def randomExperiment {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₂] [Module F G₂]
    (g₂ : G₂) (g₁ : G₁) (A : Adversary F G₁ G₂) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let c ← $ᵗ F
  A g₂ (a • g₂) (b • g₂) (c • g₂) g₁

/-- XDH₂ advantage is the Boolean distance between the real and random experiments. -/
@[expose] noncomputable def advantage {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₂] [Module F G₂]
    (g₂ : G₂) (g₁ : G₁) (A : Adversary F G₁ G₂) : ℝ≥0∞ :=
  𝒟[realExperiment g₂ g₁ A].boolDist 𝒟[randomExperiment g₂ g₁ A]

end XDH₂
