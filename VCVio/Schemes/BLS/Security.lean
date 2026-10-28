/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.GameIdentification
public import VCVio.Schemes.BLS.Averaging

/-! # BLS EUF-CMA security under Type 3 co-CDH

The signature scheme of Boneh, Lynn and Shacham, *Short Signatures from the Weil Pairing*
(ASIACRYPT 2001), is EUF-CMA secure in the random-oracle model under Type 3 co-CDH.
The named reduction guesses one of `qH + qS + 1` distinct hash-input slots, programs it
with the challenge, answers other hashes and signatures with sampled scalars, and aborts
if the programmed message is signed. The extra slot includes final verification; signing
queries account for their own hash lookups.

The proof identifies the standard ROM experiment with the indexed game, sums over the
forgery's insertion index, defers the independent challenge sample, applies stateful
domination until abort, and extracts the co-CDH solution by bilinear nondegeneracy.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace BLS

/-- BLS EUF-CMA advantage under the standard lazy random-oracle runtime is at most
`qH + qS + 1` times the success probability of the named index-guessing co-CDH reduction.
Only the direct-hash and signing query budgets restrict the adversary. -/
theorem unforgeableAdvantage_le {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [SampleableType G₁] [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂))
    (qH qS : ℕ) (hQ : QueryBound A qH qS)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁)) A ≤
      (qH + qS + 1) * Pr{let b ← CoCDH.experiment g₁ g₂ (BLS.reduction A qH qS)}[b = true] := by
  rw [unforgeableAdvantage_eq_indexed A hg₁ he, mul_prEvent_experiment_reduction]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete]
  calc
    _ ≤ ∫⁻ x : F, ∑ j : Fin (qH + qS + 1),
        Pr{let h ← ($ᵗ G₁ : ProbComp G₁)
           let y ← reductionAt A j.val g₁ g₂ (x • g₁) (x • g₂) h}[y = x • h]
        ∂𝒟[($ᵗ F : ProbComp F)] :=
      lintegral_mono fun x => prEvent_winning_le_sum_reductionAt A hg₁ x qH qS hQ
    _ = _ := by
      rw [lintegral_finsetSum _ (fun _ _ => Measurable.of_discrete)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [CoCDH.experiment, prEvent_norm]
      rw [prEvent_bind_of_discrete]
      simp only [decide_eq_true_eq]

end BLS
