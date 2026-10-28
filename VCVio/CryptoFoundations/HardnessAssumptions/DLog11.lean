/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Module.Basic
public import VCVio.CryptoFoundations.HardnessAssumptions.PairingDLog

/-! # The (1,1)-discrete logarithm problem

The problem of Bauer, Fuchsbauer and Loss supplies one common scalar multiple in each
of two source groups. The solver returns the scalar, rather than another group element.
-/

public section

open OracleComp OracleSpec

namespace DLog11

/-- A solver receiving the first generator and challenge, then the second generator and
challenge, and returning a scalar guess. -/
abbrev Adversary (F G₁ G₂ : Type) := G₁ → G₁ → G₂ → G₂ → ProbComp F

/-- Sample a uniform scalar, reveal its multiples in both source groups, and accept exactly
when the solver recovers it. -/
@[expose] def experiment {F G₁ G₂ : Type} [SampleableType F] [DecidableEq F]
    [SMul F G₁] [SMul F G₂] (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F G₁ G₂) : ProbComp Bool := do
  let α ← $ᵗ F
  let guess ← A g₁ (α • g₁) g₂ (α • g₂)
  return decide (guess = α)

/-- Present the two source generators and challenges as the degree-zero and degree-one
powers of a powers discrete-logarithm solver. -/
@[expose] def Adversary.ofPairing {F G₁ G₂ : Type}
    (A : PairingDLog.Adversary F G₁ G₂ 1 1) : Adversary F G₁ G₂ :=
  fun g₁ x₁ g₂ x₂ => A ![g₁, x₁] ![g₂, x₂]

/-- The two presentations of the common-exponent experiment agree exactly at `(1,1)`. -/
theorem experiment_ofPairing {F G₁ G₂ : Type} [Field F] [SampleableType F]
    [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (g₁ : G₁) (g₂ : G₂) (A : PairingDLog.Adversary F G₁ G₂ 1 1) :
    experiment g₁ g₂ (Adversary.ofPairing A) = PairingDLog.experiment g₁ g₂ A := by
  unfold experiment PairingDLog.experiment Adversary.ofPairing
  congr 1
  funext a
  have h₁ : ![g₁, a • g₁] = (fun i : Fin 2 => a ^ (i : ℕ) • g₁) := by
    ext i
    fin_cases i <;> simp
  have h₂ : ![g₂, a • g₂] = (fun i : Fin 2 => a ^ (i : ℕ) • g₂) := by
    ext i
    fin_cases i <;> simp
  rw [h₁, h₂]

end DLog11
