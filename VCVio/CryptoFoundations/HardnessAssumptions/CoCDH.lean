/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Module.Basic

/-! # Co-computational Diffie–Hellman problems

The Type 3 challenge supplies a common scalar multiple in both source groups. The Type 2
challenge supplies only the second-source multiple, with a public map to the first source.
Both problems ask for the scalar multiple of an independent uniform first-source point.
-/

public section

open OracleComp OracleSpec

namespace CoCDH

/-- A co-CDH adversary receives the generators, their common scalar multiples, and a
challenge point in the first source group, and returns a point in that group. -/
@[expose] def Adversary (_F G₁ G₂ : Type) := G₁ → G₂ → G₁ → G₂ → G₁ → ProbComp G₁

/-- The Type 3 co-CDH problem of Boneh, Lynn and Shacham as used for BLS, in the form
that also gives `x • g₁`. The scalar `x` and challenge point `h` are independent and uniform;
success means returning `x • h`. The pairing is public. Section 6.5 of the group-model design
note distinguishes this form from co-CDH with a map between the source groups. -/
@[expose] def experiment {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂]
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F G₁ G₂) : ProbComp Bool := do
  let x ← $ᵗ F
  let h ← $ᵗ G₁
  let w ← A g₁ g₂ (x • g₁) (x • g₂) h
  return decide (w = x • h)

/-- A Type 2 co-CDH adversary receives a second-source generator, its scalar multiple,
and an independent challenge point in the first source group. -/
@[expose] def IsoAdversary (_F G₁ G₂ : Type) := G₂ → G₂ → G₁ → ProbComp G₁

/-- The Type 2 co-CDH problem of Boneh, Gentry, Lynn and Shacham (aggregate signatures,
EUROCRYPT 2003). The scalar `x` and challenge `h` are independent and uniform; success
means returning `x • h`. The map `ψ : G₂ → G₁` and the pairing are public system
parameters, which the adversary may capture. -/
@[expose] def isoExperiment {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂]
    (g₂ : G₂) (A : IsoAdversary F G₁ G₂) : ProbComp Bool := do
  let x ← $ᵗ F
  let h ← $ᵗ G₁
  let w ← A g₂ (x • g₂) h
  return decide (w = x • h)

end CoCDH
