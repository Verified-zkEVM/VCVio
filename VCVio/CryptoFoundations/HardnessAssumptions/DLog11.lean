/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.PairingDLog

/-! # The (1,1)-discrete logarithm problem

The problem of Bauer, Fuchsbauer and Loss supplies one common scalar multiple in each
of two source groups. The solver returns the scalar, rather than another group element.

It is the `(q₁, q₂)`-DLog problem `PairingDLog.experiment` at `q₁ = q₂ = 1`, so the generic
bound `PairingDLog.experiment_ofGeneric_le` applies to it. This module gives that instance a
solver interface that takes the generator and the challenge in each group as separate arguments
(`Adversary.toPairing`), and states the experiment in that form (`experiment_eq`).
-/

public section

open OracleComp OracleSpec

namespace DLog11

/-- A solver receiving the first generator and challenge, then the second generator and
challenge, and returning a scalar guess. -/
abbrev Adversary (F G₁ G₂ : Type) := G₁ → G₁ → G₂ → G₂ → ProbComp F

/-- The `(1, 1)` solver of `PairingDLog`: it reads the powers `x ^ 0 • g` and `x ^ 1 • g` in each
group as the generator and the challenge. -/
@[expose] def Adversary.toPairing {F G₁ G₂ : Type} (A : Adversary F G₁ G₂) :
    PairingDLog.Adversary F G₁ G₂ 1 1 :=
  fun v w => A (v 0) (v 1) (w 0) (w 1)

/-- The (1,1)-DLog experiment: `PairingDLog.experiment` at `q₁ = q₂ = 1`. -/
@[expose] def experiment {F G₁ G₂ : Type} [Semiring F] [SampleableType F] [DecidableEq F]
    [AddCommMonoid G₁] [Module F G₁] [AddCommMonoid G₂] [Module F G₂] (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F G₁ G₂) : ProbComp Bool :=
  PairingDLog.experiment g₁ g₂ A.toPairing

/-- The experiment samples a uniform scalar, reveals its multiples in both source groups, and
accepts exactly when the solver recovers it. -/
theorem experiment_eq {F G₁ G₂ : Type} [Semiring F] [SampleableType F] [DecidableEq F]
    [AddCommMonoid G₁] [Module F G₁] [AddCommMonoid G₂] [Module F G₂] (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F G₁ G₂) :
    experiment g₁ g₂ A = do
      let α ← $ᵗ F
      let guess ← A g₁ (α • g₁) g₂ (α • g₂)
      return decide (guess = α) := by
  simp [experiment, PairingDLog.experiment, Adversary.toPairing]

end DLog11
