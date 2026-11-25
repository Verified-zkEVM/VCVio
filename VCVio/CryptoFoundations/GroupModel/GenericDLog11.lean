/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.GenericPairing
public import VCVio.CryptoFoundations.HardnessAssumptions.DLog11

/-! # Generic common-exponent recovery in the two-source challenge experiment

The `(1,1)` presentation of the powers experiment yields a closed generic bound for
`DLog11.experiment`, with the same generic program and the same group-operation budget.
-/

public section

open OracleComp OracleSpec GroupModel
open scoped ENNReal

namespace DLog11

/-- Interpret a generic pairing program on the generators and common-exponent challenges. -/
@[expose] def Adversary.ofGeneric {F G₁ G₂ Gₜ : Type} [CommSemiring F]
    [AddCommMonoid G₁] [Module F G₁] [AddCommMonoid G₂] [Module F G₂]
    [AddCommMonoid Gₜ] [Module F Gₜ] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (A : OracleComp (genSpec F pairingSig) F) :
    Adversary F G₁ G₂ :=
  Adversary.ofPairing (PairingDLog.Adversary.ofGeneric e A)

/-- The interpreted solver runs the generic program on the two-element source tables of the
generator and the challenge in each group, with an empty target table. -/
theorem Adversary.ofGeneric_apply {F G₁ G₂ Gₜ : Type} [CommSemiring F]
    [AddCommMonoid G₁] [Module F G₁] [AddCommMonoid G₂] [Module F G₂]
    [AddCommMonoid Gₜ] [Module F Gₜ] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (A : OracleComp (genSpec F pairingSig) F)
    (g₁ x₁ : G₁) (g₂ x₂ : G₂) :
    Adversary.ofGeneric e A g₁ x₁ g₂ x₂ = Prod.fst <$> runGen (pairingReal e) (fun _ => id) A
      (fun | .g₁ => [g₁, x₁] | .g₂ => [g₂, x₂] | .gₜ => []) := by
  simp only [Adversary.ofGeneric, Adversary.ofPairing, PairingDLog.Adversary.ofGeneric]
  congr 2

/-- A generic common-exponent solver has the identical success experiment in both interfaces. -/
theorem experiment_ofGeneric {F G₁ G₂ Gₜ : Type} [CommSemiring F]
    [SampleableType F] [DecidableEq F]
    [AddCommMonoid G₁] [Module F G₁] [AddCommMonoid G₂] [Module F G₂]
    [AddCommMonoid Gₜ] [Module F Gₜ] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (A : OracleComp (genSpec F pairingSig) F) :
    experiment g₁ g₂ (Adversary.ofGeneric e A) =
      PairingDLog.experiment g₁ g₂ (PairingDLog.Adversary.ofGeneric (q₁ := 1) (q₂ := 1) e A) :=
  experiment_ofPairing g₁ g₂ _

/-- The total-operation bound for generic `(1,1)` recovery includes both source collision
terms, the target collision term, and the final scalar-guess root term. -/
theorem experiment_ofGeneric_le_of_total {F G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (he : e g₁ g₂ ≠ 0)
    (A : OracleComp (genSpec F pairingSig) F) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    Pr{let b ← experiment g₁ g₂ (Adversary.ofGeneric e A)}[b = true] ≤
      ((2 * (q + 3).choose 2 + 2 * (q + 1).choose 2 + 1 : ℕ) : ℝ≥0∞) /
        Fintype.card F := by
  rw [experiment_ofGeneric]
  simpa only [Nat.add_comm 1 q, Nat.add_assoc, Nat.reduceAdd, Nat.mul_one,
    ← two_mul, Nat.mul_comm _ 2] using
    PairingDLog.experiment_ofGeneric_le_of_total e g₁ g₂ he 1 1 A q hq

end DLog11
