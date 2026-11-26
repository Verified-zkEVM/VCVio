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

/-- Present the two source generators and challenges as the degree-zero and degree-one
powers of a powers discrete-logarithm solver. -/
@[expose] def Adversary.ofPairing {F G₁ G₂ : Type}
    (A : PairingDLog.Adversary F G₁ G₂ 1 1) : Adversary F G₁ G₂ :=
  fun g₁ x₁ g₂ x₂ => A ![g₁, x₁] ![g₂, x₂]

/-- Reading a `(1, 1)` powers solver as a four-argument solver and back gives it unchanged. -/
@[simp] theorem Adversary.toPairing_ofPairing {F G₁ G₂ : Type}
    (A : PairingDLog.Adversary F G₁ G₂ 1 1) : (Adversary.ofPairing A).toPairing = A := by
  funext v w
  simp only [Adversary.toPairing, Adversary.ofPairing]
  congr <;> funext i <;> fin_cases i <;> rfl

/-- The (1,1)-DLog experiment of a powers solver read as a four-argument solver is that
solver's `PairingDLog` experiment. -/
theorem experiment_ofPairing {F G₁ G₂ : Type} [Semiring F] [SampleableType F] [DecidableEq F]
    [AddCommMonoid G₁] [Module F G₁] [AddCommMonoid G₂] [Module F G₂]
    (g₁ : G₁) (g₂ : G₂) (A : PairingDLog.Adversary F G₁ G₂ 1 1) :
    experiment g₁ g₂ (Adversary.ofPairing A) = PairingDLog.experiment g₁ g₂ A := by
  rw [experiment, Adversary.toPairing_ofPairing]

end DLog11
