/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Reduction
public import VCVio.Schemes.BLS.Averaging

/-! # Averaging the aggregate BLS insertion-index guess

The independent uniform guess is exchanged with the Type 2 co-CDH challenge sampling.
Multiplying by the number of slots recovers the sum of fixed-index success probabilities.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace BLS.Aggregate

private theorem isoExperiment_reduction_evalDistEq {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [SampleableType G₁] [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (qH qS N : ℕ) :
    let : NeZero (max 1 (qH + qS + N)) := ⟨by omega⟩
    CoCDH.isoExperiment g₂ (reduction ψ A qH qS N) =ᵈ
      (do let j ← ($ᵗ Fin (max 1 (qH + qS + N)) : ProbComp _)
          CoCDH.isoExperiment g₂ (reductionAt ψ A j.val)) := by
  unfold CoCDH.isoExperiment reduction
  simp only [bind_assoc]
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  apply EvalDistEq.bind_right
  intro x
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- The exact uniform-guess identity for the Type 2 solver. The factor counts direct hashes,
signing hashes, and final verification messages; the maximum ensures a nonempty range. -/
theorem mul_prEvent_isoExperiment_reduction {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [SampleableType G₁] [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    (ψ : G₂ →ₗ[F] G₁) {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (qH qS N : ℕ) :
    (max 1 (qH + qS + N) : ℕ) *
        Pr{let b ← CoCDH.isoExperiment g₂ (reduction ψ A qH qS N)}[b = true] =
      ∑ j : Fin (max 1 (qH + qS + N)),
        Pr{let b ← CoCDH.isoExperiment g₂ (reductionAt ψ A j.val)}[b = true] := by
  let : NeZero (max 1 (qH + qS + N)) := ⟨by omega⟩
  rw [(isoExperiment_reduction_evalDistEq ψ A qH qS N).prEvent_eq (· = true),
    prEvent_bind_eq_sum_fintype]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc]
  have hn : (↑(max 1 (qH + qS + N)) : ℝ≥0∞) ≠ 0 := by simp
  have ht : (↑(max 1 (qH + qS + N)) : ℝ≥0∞) ≠ ⊤ := by simp
  rw [ENNReal.mul_inv_cancel hn ht, one_mul]

end BLS.Aggregate
