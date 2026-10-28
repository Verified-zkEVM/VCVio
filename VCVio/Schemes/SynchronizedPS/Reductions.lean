/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.SynchronizedPS.Adversary
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.IndexedWeightedTrace
public import VCVio.CryptoFoundations.HardnessAssumptions.DLog11
import Mathlib.Algebra.Module.Prod

/-! # Three lazy discrete-log reductions for synchronized PS

The challenge occupies the first key, the second key, or the period hashes. Private period
scalars are sampled on demand through the shared random-oracle cache. The final target lookup
uses that same cache. Explanations are evaluated against the chronological public replies,
including repeated hash or signing calls.

The extraction equations follow `Signatures/SynchronizedPS/Spec/Reduction.lean` in Gurkan's
signature-security-lean at revision 3eaa8c4. No enumeration of periods is used.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace SynchronizedPS

/-- The single unit-weighted base shared by every signature in a period. -/
@[expose] def terms {F T : Type} [One F] (tm : T × F) : List (T × F) := [(tm.1, 1)]

private def reductionRun {F T G₁ G₂ R V : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddMonoid R] [SMul F R] [DecidableEq T] [SampleableType R]
    (A : GroupModel.Interaction.Adversary F (SourceGroup G₁ G₂) Unit
      (AGM.Query F T) AGM.Reply ((T × F) × List ((F × F) × F)))
    (g₁ : G₁) (g₂ : G₂) (pk : G₂ × G₂)
    (hash : R → G₁) (sign : (T × F) → R → G₁)
    (hashRep : R → V) (signRep : (T × F) → R → V) (initial : List V) :
    ProbComp (Explained F ((T × F) × List ((F × F) × F)) (SourceGroup G₁ G₂) ×
      List V × R) :=
  (simulateQ (T →ₒ R).romImpl
    (indexedWeightedExtractionProgram terms (fun out => out.value.data.1)
      hash sign hashRep signRep initial
      (simulateQ (fun q => AGM.oracle q.value)
        (A.main (AGM.initialInput g₁ g₂ pk))))).run' ∅

private def coefficients {F T G₁ G₂ : Type}
    (out : Explained F ((T × F) × List ((F × F) × F)) (SourceGroup G₁ G₂)) : List F :=
  (out.coefficients false).headD []

/-- Embed the challenge in the first key and solve `x*D + y*D' = K` for `x`.
The second key is independently sampled and all period exponents are known to the reduction. -/
def xReduction {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [DecidableEq T] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) : DLog11.Adversary F G₁ G₂ :=
  fun g X h Y => do
    let y ← $ᵗ F
    let (out, basis, ρ) ← reductionRun A.toAdversary g h (Y, y • h)
      (fun r : F => r • g) (fun tm r => r • X + (r * (y * tm.2)) • g)
      (fun r => (r, (0 : F), (0 : F))) (fun tm r => (0, r, r * tm.2)) [(1, 0, 0)]
    let repr := evaluate (coefficients out) basis
    let k := repr.1 - offset out.value.data.2 * ρ
    return (k - y * (ρ * out.value.data.1.2 - repr.2.2)) / (ρ - repr.2.1)

/-- Embed the challenge in the second key and solve `x*D + y*D' = K` for `y`.
The first key is independently sampled and period exponents are cached lazily. -/
def yReduction {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [DecidableEq T] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) : DLog11.Adversary F G₁ G₂ :=
  fun g X h Y => do
    let x ← $ᵗ F
    let (out, basis, ρ) ← reductionRun A.toAdversary g h (x • h, Y)
      (fun r : F => r • g) (fun tm r => (r * x) • g + (r * tm.2) • X)
      (fun r => (r, (0 : F), (0 : F))) (fun tm r => (0, r, r * tm.2)) [(1, 0, 0)]
    let repr := evaluate (coefficients out) basis
    let k := repr.1 - offset out.value.data.2 * ρ
    return (k - x * (ρ - repr.2.1)) / (ρ * out.value.data.1.2 - repr.2.2)

private def hashQuotient {F T : Type} [Field F] [DecidableEq F] [DecidableEq T]
    (coeff : List F) (tmstar : T × F) (basis : List (Option ((T × F) × (F × F))))
    (target : F × F) : F :=
  let reuse : F := 1 - evaluate coeff (basis.map fun p => p.elim 0
    (fun mr => if mr.1.1 = tmstar.1 then 1 else 0))
  let dx := target - evaluate coeff (basis.map fun p => p.elim 0 Prod.snd)
  let dy := tmstar.2 • target -
    evaluate coeff (basis.map fun p => p.elim 0 (fun mr => mr.1.2 • mr.2))
  let d := if reuse ≠ 0 then dx else dy
  (-d.2 / d.1)

/-- Hide the challenge in affine period hashes, with both signing keys independently sampled.
The target-period coefficient selects the first denominator unless it is zero, in which case
the message-weighted denominator is used. Only signing occurrences contribute to either one. -/
def hashReduction {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [DecidableEq F] [DecidableEq T] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) : DLog11.Adversary F G₁ G₂ :=
  fun g X h _ => do
    let x ← $ᵗ F
    let y ← $ᵗ F
    let point := fun r : F × F => r.1 • X + r.2 • g
    let (out, basis, target) ← reductionRun A.toAdversary g h (x • h, y • h)
      point (fun tm r => (x + y * tm.2) • point r)
      (fun _ => none) (fun tm r => some (tm, r)) [none]
    return hashQuotient (coefficients out) out.value.data.1 basis target

end SynchronizedPS
