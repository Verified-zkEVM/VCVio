/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.OOPS.AGM.Adversary
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedExecution
public import VCVio.CryptoFoundations.HardnessAssumptions.DLog11
import Mathlib.Algebra.Module.Prod

/-! # Two straight-line OOPS discrete-log reductions

Both reductions maintain a shared lazy cache indexed by topic/degree bases. The good
reduction uses known scalar bases and signs with the challenge point. The bad reduction
chooses its own signing key and masks each base as an affine function of the challenge.
Neither reduction enumerates topics or attempts to compute a discrete logarithm directly.

These adapt the weighted solvers used by `Proofs/OOPS/LazyAGMSecurity.lean` in
Gurkan's signature-security-lean to the shared random-oracle cache. Representations are
stored when replies arrive. The final quotients use the explanations of the actual
received group inputs in their chronological order.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace OOPS

private def reductionRun {F T G₁ G₂ R V : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddMonoid R] [SMul F R] [DecidableEq T] [SampleableType R] {degree : ℕ}
    (A : GroupModel.Interaction.Adversary F (SourceGroup G₁ G₂) Unit
      (AGM.Query F T degree) AGM.Reply (F × T))
    (g₁ : G₁) (g₂ pk : G₂) (hash sign : R → G₁)
    (hashRep signRep : R → V) (initial : List V) :
    ProbComp (Explained F (F × T) (SourceGroup G₁ G₂) × List V × R) :=
  (simulateQ ((T × Fin (degree + 1)) →ₒ R).romImpl
    (weightedExtractionProgram (terms degree) (fun out => out.value.data)
      hash sign hashRep signRep initial
      (simulateQ (fun q => AGM.oracle q.value)
        (A.main (AGM.initialInput g₁ g₂ pk))))).run' ∅

private def coefficients {F T G₁ G₂ : Type}
    (out : Explained F (F × T) (SourceGroup G₁ G₂)) : List F :=
  (out.coefficients false).headD []

/-- Program bases as `ρ • g₁`, sign their polynomial combinations using `X₁`, and extract
from the nonzero verification denominator. The adversary receives no `X₁` public-key input. -/
def goodReduction {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [DecidableEq T] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) : DLog11.Adversary F G₁ G₂ :=
  fun g X h Y => do
    let (out, basis, target) ← reductionRun A.toAdversary g h Y
      (fun ρ : F => ρ • g) (fun ρ => ρ • X)
      (fun ρ => (ρ, (0 : F))) (fun ρ => ((0 : F), ρ)) [(1, 0)]
    let repr := evaluate (coefficients out) basis
    return repr.1 / (target - repr.2)

/-- Program each base as `a • X₁ + b • g₁` and use an independent signing key. Signing
coefficients define the affine equation used to extract the challenge in the zero-gap branch. -/
def badReduction {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [DecidableEq T] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) : DLog11.Adversary F G₁ G₂ :=
  fun g X h _ => do
    let κ ← $ᵗ F
    let point := fun r : F × F => r.1 • X + r.2 • g
    let (out, basis, target) ← reductionRun A.toAdversary g h (κ • h)
      point (fun r => κ • point r) (fun _ => ((0 : F), (0 : F))) id [(0, 0)]
    let repr := evaluate (coefficients out) basis
    return (repr.2 - target.2) / (target.1 - repr.1)

end OOPS
