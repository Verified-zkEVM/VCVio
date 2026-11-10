/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Module.Basic

/-! # The two-source powers discrete-logarithm problem

The `(q₁, q₂)`-DLog assumption of KZG asks for the common exponent from powers in
both source groups. The pairing is public, so the adversary needs no oracle for it.
-/

public section

open OracleComp OracleSpec

namespace PairingDLog

/-- An adversary receives the powers through `q₁` and `q₂` in the two source groups
and returns a scalar guess for their common exponent. -/
@[expose] def Adversary (F G₁ G₂ : Type) (q₁ q₂ : ℕ) :=
  (Fin (q₁ + 1) → G₁) → (Fin (q₂ + 1) → G₂) → ProbComp F

/-- The `(q₁, q₂)`-DLog experiment of KZG samples a uniform common exponent,
provides its powers in both source groups, and tests the adversary's guess.
The pairing is public, so the adversary needs no oracle for it. -/
@[expose] def experiment {F G₁ G₂ : Type} [Field F] [SampleableType F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    {q₁ q₂ : ℕ} (g₁ : G₁) (g₂ : G₂) (A : Adversary F G₁ G₂ q₁ q₂) : ProbComp Bool := do
  let x ← $ᵗ F
  let c ← A (fun i => x ^ (i : ℕ) • g₁) (fun j => x ^ (j : ℕ) • g₂)
  return decide (c = x)

end PairingDLog
