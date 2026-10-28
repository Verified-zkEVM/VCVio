/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Examples.ElGamal.GenericINDCPA
public import Mathlib.Algebra.Field.ZMod

/-! # Generic multi-query ElGamal regression tests

Two identical message-handle queries exercise repeated responses. The adversary compares
the ciphertext components with each other and with a message handle, and checks that repeated
responses receive distinct handles. An invalid message handle denotes zero.
-/

public section

open OracleComp OracleSpec GroupModel elGamalAsymmEnc
open scoped ENNReal

namespace ElGamalGenericINDCPATest

local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

local notation "testSpec" =>
  spec (ZMod 101) groupSig + (unifSpec + (Handle × Handle →ₒ Handle × Handle))

local notation "testAdversary" =>
  ((OracleComp.lift (OracleSpec.query (spec := testSpec) (Sum.inr (Sum.inr (0, 99)))) >>= fun c =>
    OracleComp.lift (OracleSpec.query (spec := testSpec) (Sum.inr (Sum.inr (0, 99)))) >>= fun d =>
    OracleComp.lift (OracleSpec.query (spec := testSpec)
      (Sum.inl (GroupModel.Query.eq () (Prod.snd c) (Prod.snd d)))) >>= fun same =>
    OracleComp.lift (OracleSpec.query (spec := testSpec)
      (Sum.inl (GroupModel.Query.eq () (Prod.snd d) 0))) >>= fun guess =>
    pure (same && guess && decide (Prod.snd c ≠ Prod.snd d))) : OracleComp testSpec Bool)

private theorem operation_bound :
    IsQueryBoundP testAdversary (fun i => isGroupOp i = true) 0 := by
  simp [isGroupOp, Query.isOp]

private theorem query_bound :
    IsQueryBoundP testAdversary (· matches .inr (.inr _)) 2 := by
  simp

/-- Both LR calls are counted, even though the game answers the second from its cache. -/
theorem makesAtMostQueries_zmod101 :
    (GenericAdversary.toAdversary (1 : ZMod 101) testAdversary).MakesAtMostQueries 2 :=
  GenericAdversary.makesAtMostQueries_toAdversary 1 testAdversary 2 query_bound

/-- Handle interpretation forwards the same value pair twice, reads an invalid handle as zero,
and allocates distinct ciphertext handles on both responses. -/
theorem toAdversary_zmod101 (pk : ZMod 101) :
    GenericAdversary.toAdversary (1 : ZMod 101) testAdversary pk = (do
      let c ← (elGamalAsymmEnc (ZMod 101) (ZMod 101) 1).IND_CPA_oracleSpec.query (.inr (1, 0))
      let d ← (elGamalAsymmEnc (ZMod 101) (ZMod 101) 1).IND_CPA_oracleSpec.query (.inr (1, 0))
      pure (decide (c.2 = d.2) && decide (d.2 = 1))) := by
  change (do
    let c ← (elGamalAsymmEnc (ZMod 101) (ZMod 101) 1).IND_CPA_oracleSpec.query (.inr (1, 0))
    let d ← (elGamalAsymmEnc (ZMod 101) (ZMod 101) 1).IND_CPA_oracleSpec.query (.inr (1, 0))
    pure (decide (c.2 = d.2) && decide (d.2 = 1) && true) :
      OracleComp (elGamalAsymmEnc (ZMod 101) (ZMod 101) 1).IND_CPA_oracleSpec Bool) = _
  simp only [Bool.and_true]

/-- A repeated LR pair consumes only one encryption in every counted hybrid. The comparison
between the two ciphertext values succeeds, while their numeric handles remain distinct. -/
theorem repeated_hybrid_zmod101 (pk : ZMod 101) (n : ℕ) :
    (simulateQ ((elGamalAsymmEnc (ZMod 101) (ZMod 101) 1).IND_CPA_queryImpl_hybridLR_counted pk n)
      (GenericAdversary.toAdversary 1 testAdversary pk)).run' (∅, 0) = (do
        let r ← $ᵗ (ZMod 101)
        pure (decide ((if 0 < n then 1 else 0) + r • pk = 1))) := by
  rw [toAdversary_zmod101]
  simp [AsymmEncAlg.IND_CPA_queryImpl_hybridLR_counted,
    AsymmEncAlg.IND_CPA_queryImplFromChallenge,
    AsymmEncAlg.IND_CPA_hybridChallengeOracleLR_counted,
    AsymmEncAlg.IND_CPA_countedChallengeOracle, elGamalAsymmEnc, StateT.run'_eq, monad_norm]

/-- Each of the two extracted steps has one-time advantage at most `1026 / 101`.
The phase bound is six operations and the collision-table bound uses nineteen entries. -/
theorem step_advantage_zmod101 (k : ℕ) (hk : k < 2) :
    AsymmEncAlg.IND_CPA_OneTime_Advantage (elGamalAsymmEnc (ZMod 101) (ZMod 101) 1)
      ProbCompRuntime.probComp ((GenericAdversary.step testAdversary k).toOneTime (1 : ZMod 101)) ≤
        (1026 : ℝ≥0∞) / 101 := by
  have hg : Function.Bijective (· • (1 : ZMod 101) : ZMod 101 → ZMod 101) := by
    constructor
    · intro x y h
      simpa only [smul_eq_mul, mul_one] using h
    · intro x
      exact ⟨x, by simp only [smul_eq_mul, mul_one]⟩
  have h := GenericAdversary.oneTimeAdvantage_step_toOneTime_le hg testAdversary 0 2 k
    operation_bound query_bound hk
  norm_num [Nat.choose, ZMod.card, ← mul_div_assoc] at h ⊢
  exact h

/-- The unconditional multi-query theorem applies to two repeated LR calls and two free
value comparisons over `ZMod 101`; its explicit bound evaluates to `2052 / 101`. -/
theorem advantage_zmod101 :
    (elGamalAsymmEnc (ZMod 101) (ZMod 101) 1).IND_CPA_Advantage
      (GenericAdversary.toAdversary 1 testAdversary) ≤ (2052 : ℝ≥0∞) / 101 := by
  have hg : Function.Bijective (· • (1 : ZMod 101) : ZMod 101 → ZMod 101) := by
    constructor
    · intro x y h
      simpa only [smul_eq_mul, mul_one] using h
    · intro x
      exact ⟨x, by simp only [smul_eq_mul, mul_one]⟩
  have h := IND_CPA_Advantage_toAdversary_le hg testAdversary 0 2 operation_bound query_bound
  norm_num [Nat.choose, ZMod.card, ← mul_div_assoc] at h ⊢
  exact h

end ElGamalGenericINDCPATest
