/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.XDH
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Computational and decisional uber problems

The uber assumption of Boneh, Boyen and Goh (2005), and Boyen's *The Uber-Assumption
Family* (2008), supplies polynomially related group elements. At the Type 3 signature,
the independence condition requires the target polynomial to lie outside the linear span
of the supplied target polynomials and products of supplied source polynomials.
The pairing is public and may be captured by the adversary. These experiments themselves
impose neither the independence condition nor a resource restriction.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Uber

/-- A computational adversary receives the ordered lists in all three sorts and returns a
candidate target-group element. The public pairing may be captured in the adversary. -/
abbrev ComputationalAdversary (G₁ G₂ Gₜ : Type) :=
  List G₁ → List G₂ → List Gₜ → ProbComp Gₜ

/-- A decisional adversary receives the ordered lists and a target-sort challenge. -/
abbrev DecisionalAdversary (G₁ G₂ Gₜ : Type) :=
  List G₁ → List G₂ → List Gₜ → Gₜ → ProbComp Bool

/-- The computational uber experiment samples the polynomial variables uniformly and
checks recovery of the target polynomial in the target group. -/
@[expose] def computationalExperiment {F G₁ G₂ Gₜ : Type} {n : ℕ} [Field F]
    [SampleableType (Fin n → F)]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (P R Q : List (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F)
    (A : ComputationalAdversary G₁ G₂ Gₜ) : ProbComp Bool := do
  let x ← $ᵗ (Fin n → F)
  let z ← A (P.map (fun p => MvPolynomial.eval x p • g₁))
    (R.map (fun p => MvPolynomial.eval x p • g₂))
    (Q.map (fun p => MvPolynomial.eval x p • e g₁ g₂))
  return decide (z = MvPolynomial.eval x f • e g₁ g₂)

/-- The real decisional uber experiment supplies the target polynomial as the challenge. -/
@[expose] def realExperiment {F G₁ G₂ Gₜ : Type} {n : ℕ} [Field F]
    [SampleableType (Fin n → F)]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (P R Q : List (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F)
    (A : DecisionalAdversary G₁ G₂ Gₜ) : ProbComp Bool := do
  let x ← $ᵗ (Fin n → F)
  A (P.map (fun p => MvPolynomial.eval x p • g₁))
    (R.map (fun p => MvPolynomial.eval x p • g₂))
    (Q.map (fun p => MvPolynomial.eval x p • e g₁ g₂))
    (MvPolynomial.eval x f • e g₁ g₂)

/-- The random decisional uber experiment uses an independent uniform target scalar. -/
@[expose] def randomExperiment {F G₁ G₂ Gₜ : Type} {n : ℕ} [Field F]
    [SampleableType (Fin n → F)] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (P R Q : List (MvPolynomial (Fin n) F))
    (A : DecisionalAdversary G₁ G₂ Gₜ) : ProbComp Bool := do
  let x ← $ᵗ (Fin n → F)
  let y ← $ᵗ F
  A (P.map (fun p => MvPolynomial.eval x p • g₁))
    (R.map (fun p => MvPolynomial.eval x p • g₂))
    (Q.map (fun p => MvPolynomial.eval x p • e g₁ g₂)) (y • e g₁ g₂)

/-- Decisional uber advantage is the Boolean distance between the real and random games. -/
@[expose] noncomputable def advantage {F G₁ G₂ Gₜ : Type} {n : ℕ} [Field F]
    [SampleableType (Fin n → F)] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (P R Q : List (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F)
    (A : DecisionalAdversary G₁ G₂ Gₜ) : ℝ≥0∞ :=
  𝒟[realExperiment e g₁ g₂ P R Q f A].boolDist 𝒟[randomExperiment e g₁ g₂ P R Q A]

end Uber
