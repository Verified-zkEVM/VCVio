/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.GameIdentification
public import VCVio.Schemes.BLS.Aggregate.ExtractionProbability

/-! # Guessing a fresh honest position in an aggregate

Every winning list contains a fresh honest-key message. Its cached insertion index lies
in the range accounting for adversary hashes, signing hashes, and final verification.
A union bound over these indices combines with the fixed-index co-CDH extraction bound.
-/

public section

open OracleComp OracleSpec

namespace BLS.Aggregate

/-- For every fixed honest secret, the scalar-sampled aggregate game is bounded by the
sum of fixed-index Type 2 solver success probabilities. Multiple honest positions cause
no additional factor: any one of their insertion indices witnesses the union event. -/
theorem prEvent_winning_le_sum_reductionAt {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [SampleableType G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (hg₁ : Function.Bijective (· • ψ g₂ : F → G₁))
    (hg₂ : Function.Surjective (· • g₂ : F → G₂)) (he : e (ψ g₂) g₂ ≠ 0)
    (x : F) (qH qS N : ℕ) (hQ : QueryBound A qH qS N) :
    Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • ψ g₂)
        (fun r => x • (r • ψ g₂)) none)
        (withFinalPairings e (A.main (x • g₂)))).run OracleState.empty}[
      Winning e g₂ (x • g₂) z] ≤
    ∑ j : Fin (max 1 (qH + qS + N)),
      Pr{let h ← ($ᵗ G₁ : ProbComp G₁)
         let y ← reductionAt ψ A j.val g₂ (x • g₂) h}[y = x • h] := by
  let P : ((List (G₂ × M) × G₁) × Gₜ) → List M → Prop :=
    fun z _ => (z.1.1.map Prod.snd).Nodup ∧ e z.1.2 g₂ = z.2
  let eligible : ((List (G₂ × M) × G₁) × Gₜ) → M → Prop :=
    fun z msg => (x • g₂, msg) ∈ z.1.1
  have hsum :
      Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • ψ g₂)
          (fun r => x • (r • ψ g₂)) none)
          (withFinalPairings e (A.main (x • g₂)))).run OracleState.empty}[
        Winning e g₂ (x • g₂) z] ≤
      ∑ j : Fin (max 1 (qH + qS + N)),
        Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • ψ g₂)
            (fun r => x • (r • ψ g₂)) none)
            (withFinalPairings e (A.main (x • g₂)))).run OracleState.empty}[
          FreshTarget P eligible j.val z] := by
    refine (prEvent_mono_of_support _ _
      (fun z => ∃ j : Fin (max 1 (qH + qS + N)), FreshTarget P eligible j.val z) ?_).trans
        (prEvent_exists_le _ _)
    intro z hz hw
    obtain ⟨⟨msg, hm, hf⟩, hd, hv⟩ := hw
    obtain ⟨v, i, hc, hi⟩ := withFinalPairings_support_index_lt e (fun _ => $ᵗ F)
      (· • ψ g₂) (fun r => x • (r • ψ g₂)) none (A.main (x • g₂))
      qH qS N (hQ _).1 (hQ _).2.1 (hQ _).2.2 z hz (x • g₂, msg) hm
    exact ⟨⟨i, hi⟩, ⟨hd, hv⟩, msg, hm, hf, v, hc⟩
  refine hsum.trans (Finset.sum_le_sum fun j _ => ?_)
  rw [prEvent_freshTarget_eraseSelection]
  exact prEvent_freshTarget_le_reductionAt ψ A hg₁ hg₂ he x j.val

end BLS.Aggregate
