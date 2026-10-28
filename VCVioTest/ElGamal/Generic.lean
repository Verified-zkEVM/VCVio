/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Examples.ElGamal.Generic
public import Mathlib.Algebra.Field.ZMod

/-! # Generic ElGamal over the field with 101 elements

The adversary chooses the generator and an invalid handle, which denotes zero, without
performing any group operations. Its second phase compares the second ciphertext component
with the generator. The numerical bound and the interpreted computation are checked separately.
-/

public section

open OracleComp OracleSpec GroupModel elGamalAsymmEnc
open scoped ENNReal

namespace ElGamalGenericTest

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

local notation "testAdversary" =>
  GenericOneTimeAdversary.mk (F := ZMod 101) Unit (pure (0, 2, ()))
    (fun _ _ c₂ =>
      OracleComp.lift (OracleSpec.query (spec := genSpec (ZMod 101) groupSig)
        (Sum.inl (GroupModel.Query.eq () c₂ 0))))

/-- The zero-operation adversary has one-time advantage at most `126 / 101`. -/
theorem advantage_zmod101 :
    AsymmEncAlg.IND_CPA_OneTime_Advantage (elGamalAsymmEnc (ZMod 101) (ZMod 101) 1)
      ProbCompRuntime.probComp ((testAdversary).toOneTime 1) ≤ (126 : ℝ≥0∞) / 101 := by
  have hg : Function.Bijective (· • (1 : ZMod 101) : ZMod 101 → ZMod 101) := by
    constructor
    · intro x y h
      simpa only [smul_eq_mul, mul_one] using h
    · intro x
      exact ⟨x, by simp only [smul_eq_mul, mul_one]⟩
  have h₁ : IsQueryBoundP (testAdversary).chooseMessages (fun i => isGroupOp i = true) 0 := by
    exact isQueryBoundP_pure _ _ _
  have h₂ : ∀ s a b, IsQueryBoundP ((testAdversary).distinguish s a b)
      (fun i => isGroupOp i = true) 0 := by
    intro s a b
    change IsQueryBoundP (liftM ((genSpec (ZMod 101) groupSig).query (.inl (.eq () b 0)))) _ 0
    rw [isQueryBoundP_query_iff]
    simp [isGroupOp, Query.isOp]
  have h := oneTimeAdvantage_toOneTime_le hg testAdversary 0 0 h₁ h₂
  norm_num [Nat.choose, ZMod.card, ← mul_div_assoc] at h ⊢
  exact h

/-- The generic reduction reads the invalid message handle as zero even though its outer
DDH table has a nonzero entry at that handle. -/
theorem reduction_zmod101 (X Y T : ZMod 101) :
    DDHAdversary.ofGeneric (ddhOfGeneric testAdversary) 1 X Y T =
      (do
        let bit ← $ᵗ Bool
        pure (bit == decide (T + (if bit then 1 else 0) = 1))) := by
  rw [← oneTimeDDHReduction_toOneTime_eq]
  rfl

end ElGamalGenericTest
