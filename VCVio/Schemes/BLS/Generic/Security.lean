/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.AlgebraicBound
public import VCVio.Schemes.BLS.Generic.ReductionEquivalence
public import VCVio.Schemes.BLS.Generic.ReductionCost

/-! # Unconditional generic BLS unforgeability in Type 3 pairing groups

The certified algebraic translation and the exact generic implementations of both extraction
branches compose with the generic common-exponent bound. The common operation budget is
`Q = 5 + q + 3 * qH + 4 * qS`; the resulting advantage is at most
`(4 * Q ^ 2 + 12 * Q + 15) / Fintype.card F`.
-/

public section

open OracleComp OracleSpec GroupModel
open scoped ENNReal

namespace BLS

private theorem twice_pairing_bound (q : ℕ) :
    2 * (2 * (q + 3).choose 2 + 2 * (q + 1).choose 2 + 1) + 1 =
      4 * q ^ 2 + 12 * q + 15 := by
  have h₁ := Nat.add_one_mul_choose_eq (q + 2) 1
  have h₂ := Nat.add_one_mul_choose_eq q 1
  simp only [Nat.choose_one_right, Nat.reduceAdd, Nat.add_assoc] at h₁ h₂
  nlinarith

/-- A generic Type 3 BLS forger has unconditional ROM advantage bounded solely by its group,
hash, and signing budgets and the field cardinality. The named reductions are `goodProgram`
and `badProgram`, with costs `3 + q + qH + qS` and `5 + q + 3 * qH + 4 * qS`. -/
theorem unforgeableAdvantage_le_generic {F M G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq M]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (A : Generic.Adversary F M) (hA : Generic.FollowsProtocol A)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0)
    (q qH qS : ℕ)
    (hq : IsQueryBoundP (A Generic.reductionInput) (fun i => isGroupOp i = true) q)
    (hqH : IsQueryBoundP (A Generic.reductionInput) Generic.isHash qH)
    (hqS : IsQueryBoundP (A Generic.reductionInput) Generic.isSign qS) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁))
      (A.toUnforgeableAdversary e g₁ g₂) ≤
      ((4 * (5 + q + 3 * qH + 4 * qS) ^ 2 +
        12 * (5 + q + 3 * qH + 4 * qS) + 15 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  have hg₁' : g₁ ≠ 0 := by intro h; simp [h] at he
  have hg₂' : g₂ ≠ 0 := by intro h; simp [h] at he
  let Q := 5 + q + 3 * qH + 4 * qS
  have hgood := DLog11.experiment_ofGeneric_le_of_total e g₁ g₂ hg₁' hg₂' he
    (Generic.goodProgram A) Q
    ((Generic.isQueryBoundP_goodProgram A q qH qS hq hqH hqS).mono (by dsimp [Q]; omega))
  have hbad := DLog11.experiment_ofGeneric_le_of_total e g₁ g₂ hg₁' hg₂' he
    (Generic.badProgram A) Q (Generic.isQueryBoundP_badProgram A q qH qS hq hqH hqS)
  have hge : DLog11.experiment g₁ g₂ (goodReduction (A.toAlgebraic hA e g₁ g₂)) =
      DLog11.experiment g₁ g₂ (DLog11.Adversary.ofGeneric e (Generic.goodProgram A)) := by
    unfold DLog11.experiment
    apply bind_congr
    intro a
    rw [Generic.goodReduction_toAlgebraic]
  have hbe : DLog11.experiment g₁ g₂ (badReduction (A.toAlgebraic hA e g₁ g₂)) =
      DLog11.experiment g₁ g₂ (DLog11.Adversary.ofGeneric e (Generic.badProgram A)) := by
    unfold DLog11.experiment
    apply bind_congr
    intro a
    rw [Generic.badReduction_toAlgebraic]
  have h := unforgeableAdvantage_le_of_generic_algebraic A hA e g₁ g₂ hg₁ he
  rw [hge, hbe] at h
  refine (h.trans (add_le_add (add_le_add hgood hbad) le_rfl)).trans_eq ?_
  rw [← ENNReal.add_div, ← ENNReal.add_div]
  congr 1
  norm_cast
  rw [← two_mul, twice_pairing_bound]

end BLS
