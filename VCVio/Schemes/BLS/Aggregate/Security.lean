/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Guess
public import VCVio.Schemes.BLS.Aggregate.Averaging

/-! # BGLS chosen-key security under Type 2 co-CDH

The aggregate signature scheme of Boneh, Gentry, Lynn and Shacham (EUROCRYPT 2003)
is secure in the random-oracle model through the named Type 2 co-CDH reduction.
The public map `ψ` transfers arbitrary chosen keys to the first source. Generation of
the second source by `g₂` supplies its pairing compatibility, which extraction needs
when subtracting the other signers' contributions.

The reduction guesses among `max 1 (qH + qS + N)` insertion slots: direct hash queries,
signing-query hashes, and every final verification message. The maximum provides an
inhabited guessing range even when all three budgets vanish. The proof reuses the BLS
indexed execution, programming, until-abort comparison, and uniform-guess averaging.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace BLS.Aggregate

/-- BGLS chosen-key advantage under the shared lazy random oracle is at most
`max 1 (qH + qS + N)` times the success probability of the named Type 2 co-CDH solver.
The budgets bound direct hashes, signing requests, and final aggregate length.
Surjectivity of second-source scalar multiplication expresses that `g₂` generates the
whole second source; it makes the public map compatible with every adversarial key's
pairing contribution, as required when extracting from an accepted aggregate. -/
theorem unforgeableAdvantage_le {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [SampleableType G₁] [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (qH qS N : ℕ) (hQ : QueryBound A qH qS N)
    (hg₁ : Function.Bijective (· • ψ g₂ : F → G₁))
    (hg₂ : Function.Surjective (· • g₂ : F → G₂)) (he : e (ψ g₂) g₂ ≠ 0) :
    AggregateSignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁)) A ≤
      (max 1 (qH + qS + N) : ℕ) *
        Pr{let b ← CoCDH.isoExperiment g₂ (BLS.Aggregate.reduction ψ A qH qS N)}[b = true] := by
  rw [unforgeableAdvantage_eq_indexed (ψ g₂) A hg₁,
    mul_prEvent_isoExperiment_reduction]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete]
  calc
    _ ≤ ∫⁻ x : F, ∑ j : Fin (max 1 (qH + qS + N)),
        Pr{let h ← ($ᵗ G₁ : ProbComp G₁)
           let y ← reductionAt ψ A j.val g₂ (x • g₂) h}[y = x • h]
        ∂𝒟[($ᵗ F : ProbComp F)] :=
      lintegral_mono fun x => prEvent_winning_le_sum_reductionAt ψ A hg₁ hg₂ he x qH qS N hQ
    _ = _ := by
      rw [lintegral_finsetSum _ (fun _ _ => Measurable.of_discrete)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [CoCDH.isoExperiment, prEvent_norm]
      rw [prEvent_bind_of_discrete]
      simp only [decide_eq_true_eq]

end BLS.Aggregate
