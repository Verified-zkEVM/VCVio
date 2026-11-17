/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Module.Basic

/-! # The Type 3 co-computational Diffie–Hellman problem

The challenge supplies a common scalar multiple in both source groups and an independent
uniform point in the first source group. The adversary must multiply that point by the scalar.
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

end CoCDH
