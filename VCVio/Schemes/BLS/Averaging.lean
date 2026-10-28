/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Reduction

/-! # Averaging the BLS insertion-index guess

The uniform guess in the Boneh–Lynn–Shacham reduction is independent of the co-CDH
challenge. Multiplying its success probability by the number of slots gives the sum
of the fixed-slot success probabilities.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace BLS

/-- The reduction's independent guess may be sampled before the co-CDH secret and challenge. -/
private theorem experiment_reduction_evalDistEq {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [SampleableType G₁] [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂)) (qH qS : ℕ) :
    CoCDH.experiment g₁ g₂ (reduction A qH qS) =ᵈ
      (do let j ← ($ᵗ Fin (qH + qS + 1) : ProbComp _)
          CoCDH.experiment g₁ g₂ (reductionAt A j.val)) := by
  unfold CoCDH.experiment reduction
  simp only [bind_assoc]
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  apply EvalDistEq.bind_right
  intro x
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- Multiplying the guessed reduction's success probability by the number of possible slots
recovers the sum of fixed-slot success probabilities. -/
theorem mul_prEvent_experiment_reduction {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [SampleableType G₁] [DecidableEq G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂)) (qH qS : ℕ) :
    (qH + qS + 1 : ℝ≥0∞) *
        Pr{let b ← CoCDH.experiment g₁ g₂ (reduction A qH qS)}[b = true] =
      ∑ j : Fin (qH + qS + 1),
        Pr{let b ← CoCDH.experiment g₁ g₂ (reductionAt A j.val)}[b = true] := by
  rw [(experiment_reduction_evalDistEq A qH qS).prEvent_eq (· = true),
    prEvent_bind_eq_sum_fintype]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc]
  have hn : (↑(qH + qS + 1) : ℝ≥0∞) ≠ 0 := by simp
  have ht : (↑(qH + qS + 1) : ℝ≥0∞) ≠ ⊤ := by simp
  norm_cast
  rw [ENNReal.mul_inv_cancel hn ht, one_mul]

end BLS
