/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.BySourceAnswer
public import HashSig.SLHDSA.SHAKE128s.Proof.BySourceShared

/-!
# The answer half of the `127` bound

`answerBound` is the answer half at `TailBudgetW`: at a good walk, the answer-side event outside
the late event is within `q / 2 ^ 128 + 2 ^ -126`. The structural faults are charged per fresh
entry and the target record per entry, and together they are within the adversary's work and
the requests (`BySourceAnswer.fresh_add_right_le`), whatever the signer asks.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BySourceTarget

open Security CanonicalGraph WarmedGame Target RoutedSplit BracketedRun CarrierTail CarrierThin
  FreshExpectation BySourceBridge BySourceAnswer

/-! ## The answer half -/

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

/-- **The answer half at `127`, the signer's calls free.** -/
theorem answerBound (q : Nat) (adversary : Adversary) (hbudget : TailBudgetW adversary q)
    (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk) :
    Pr{let result ← carrierTail keep127 adversary walk}[RoutedSplit.AnswerBad
          ((walk.1, (FinalAssembly.forgetFused result).1), (FinalAssembly.forgetFused result).2) ∧
        ¬ Target127.late (walk, result)] ≤
      (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126 := by
  classical
  by_cases hq : 2 ^ 128 ≤ q
  · refine le_trans (prEvent_le_one _) (le_trans ?_ le_self_add)
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  have hqlt : q < 2 ^ 128 := Nat.lt_of_not_le hq
  have hpublic : ¬ HashSeparation.Possible ((keyAt walk).seed, (keyAt walk).root) :=
    AnswerSide.not_possible_generatedKey hwalk hgood.2
  set split := SplitTail.splitCarrierTail (CombinedCharge.IsMessageInput (keyAt walk))
    Game.QueryKind.hash Game.QueryKind.verification keep127 adversary walk with hsplitDef
  have hmap : Prod.fst <$> split = carrierTail keep127 adversary walk :=
    SplitTail.map_splitCarrierTail _ AnswerFired.hash_ne_verification keep127 adversary walk
  have hmapR := SplitCarrierTail.forget_splitCarrierTail
    (CombinedCharge.IsMessageInput (keyAt walk)) Game.QueryKind.hash Game.QueryKind.verification
    keep127 adversary walk
  have hfst : ∀ z ∈ support split, z.1 ∈ support (carrierTail keep127 adversary walk) := by
    intro z hz
    rw [← hmap, support_map]
    exact ⟨z, hz, rfl⟩
  have htailOf : ∀ result ∈ support (carrierTail keep127 adversary walk),
      FinalAssembly.forgetFused result ∈ support (WarmedGame.tail adversary walk) := by
    intro result hresult
    rw [← CarrierTail.forgetFused_carrierTail keep127 adversary walk, support_map]
    exact ⟨result, hresult, rfl⟩
  -- The two charges' counts, on every run, within the budget.
  have hpath : ∀ z ∈ support split,
      freshMass (Deviating walk) walk.2 z.1.2.1 + (z.1.2.2.2.length : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    intro z hz
    refine le_trans (fresh_add_right_le adversary hwalk hgood z hz) ?_
    have h := (hbudget walk hwalk _ (htailOf z.1 (hfst z hz))).2
    exact_mod_cast (show z.1.1.1.1.counts.work + z.1.1.1.1.counts .signing ≤ q by
      simp only [FinalAssembly.forgetFused] at h
      omega)
  have hrightBound : ∀ result ∈ support (carrierTail keep127 adversary walk),
      result.2.2.2.length ≤ q := by
    intro result hresult
    rw [← hmap, support_map] at hresult
    obtain ⟨z, hz, rfl⟩ := hresult
    have h := le_trans le_add_self (hpath z hz)
    exact_mod_cast h
  have hleftBound := CarrierCap.leftRecord_le_cap_carrierTail keep127 adversary walk hpublic
    (fun keys hkeys => CarrierRecord.keys_publicKey keep127 walk hwalk keys hkeys)
    (fun result hresult => le_trans
      (SigningFaithful.signed_length_le_signing_tail adversary (htailOf result hresult))
      (hbudget walk hwalk _ (htailOf result hresult)).1)
  -- The event, at the split tail.
  have hevent : Pr{let result ← carrierTail keep127 adversary walk}[RoutedSplit.AnswerBad ((walk.1,
          (FinalAssembly.forgetFused result).1), (FinalAssembly.forgetFused result).2) ∧
          ¬ Target127.late (walk, result)] =
      Pr{let z ← split}[RoutedSplit.AnswerBad ((walk.1, (FinalAssembly.forgetFused z.1).1),
            (FinalAssembly.forgetFused z.1).2) ∧ ¬ Target127.late (walk, z.1)] := by
    rw [← hmap, prEvent_map]
  -- The structural faults, per fresh entry.
  have hbad : Pr{let z ← split}[GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2)
        (z.1.1, z.1.2.1)] ≤
      (∑' z, Pr{let x ← split}[x = z] * freshMass (Deviating walk) walk.2 z.1.2.1) *
        (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
    have hprob : Pr{let z ← split}[GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2)
            (z.1.1, z.1.2.1)] =
        Pr{let x ← ((simulateQ KeygenUniform.rom (countQueries (ClassGrowth.splitCost
            (CombinedCharge.IsMessageInput (keyAt walk)) Game.QueryKind.hash
            Game.QueryKind.verification)
            (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2)}[
          (GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2)) x] := by
      rw [← hmapR, prEvent_map]
      rfl
    rw [hprob]
    refine le_trans (prob_bad_le_expected_fresh (Deviating walk)
      (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2) _
      (fun input => AnswerSide.prob_canonicalBad_le walk.1.1.2.2 walk.1.2 input)
      (fun input answer hbadness hnone => by
        unfold AnswerSide.CanonicalBad at hbadness
        rw [hnone] at hbadness
        cases hbadness)
      _ walk.2 (CanonicalTarget.clean_of_canonical_cache walk.1.1.2.2 walk.1.2 walk.2
        (WarmedCharges.walk_cache_canonical hwalk))) (le_of_eq ?_)
    rw [← hmapR, tsum_map_mul]
  -- The coverage, per target entry.
  have hcover : Pr{let z ← split}[AnswerFired.FiredCoveredRec walk z.1] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 +
        (∑' z, Pr{let x ← split}[x = z] * (z.1.2.2.2.length : ℝ≥0∞)) *
          (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
    have hprob : Pr{let z ← split}[AnswerFired.FiredCoveredRec walk z.1] =
        Pr{let x ← carrierTail keep127 adversary walk}[(AnswerFired.FiredCoveredRec walk) x] := by
      rw [← hmap, prEvent_map]
    have hexpect : (∑' result, Pr{let x ← carrierTail keep127 adversary walk}[x = result] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
        ∑' z, Pr{let x ← split}[x = z] * (z.1.2.2.2.length : ℝ≥0∞) := by
      rw [← hmap, tsum_map_mul]
    rw [hprob]
    refine le_trans (AnswerFired.prob_carrierTail_firedCovered_le adversary walk hwalk hgood
      (5 * 2 ^ 62) q le_rfl hleftBound hrightBound) (add_le_add le_rfl ?_)
    rw [hexpect]
    exact mul_le_mul' le_rfl (AnswerFired.second_order_fits q (by omega))
  have hsum : (∑' z, Pr{let x ← split}[x = z] * freshMass (Deviating walk) walk.2 z.1.2.1) +
        (∑' z, Pr{let x ← split}[x = z] * (z.1.2.2.2.length : ℝ≥0∞)) ≤ (q : ℝ≥0∞) := by
    rw [← ENNReal.tsum_add]
    simp_rw [← mul_add]
    exact tsum_mul_le_const split _ _ hpath
  rw [hevent]
  calc Pr{let z ← split}[RoutedSplit.AnswerBad ((walk.1, (FinalAssembly.forgetFused z.1).1),
            (FinalAssembly.forgetFused z.1).2) ∧ ¬ Target127.late (walk, z.1)]
      ≤ Pr{let z ← split}[GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2)
            (z.1.1, z.1.2.1) ∨
            AnswerFired.FiredCoveredRec walk z.1] :=
        prEvent_mono_of_support _ _ _ fun z hz hev =>
          AnswerFired.join_carrierTail adversary walk hwalk hgood z.1 (hfst z hz) hev.1 hev.2
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ (∑' z, Pr{let x ← split}[x = z] * freshMass (Deviating walk) walk.2 z.1.2.1) *
          (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) +
        ((1 : ℝ≥0∞) / 2 ^ 126 +
          (∑' z, Pr{let x ← split}[x = z] * (z.1.2.2.2.length : ℝ≥0∞)) *
            (1 / ((2 ^ 128 : Nat) : ℝ≥0∞))) := add_le_add hbad hcover
    _ = ((∑' z, Pr{let x ← split}[x = z] * freshMass (Deviating walk) walk.2 z.1.2.1) +
          (∑' z, Pr{let x ← split}[x = z] * (z.1.2.2.2.length : ℝ≥0∞))) *
            (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) + (1 : ℝ≥0∞) / 2 ^ 126 := by ring
    _ ≤ (q : ℝ≥0∞) * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) + (1 : ℝ≥0∞) / 2 ^ 126 :=
        add_le_add (mul_le_mul' hsum le_rfl) le_rfl
    _ = (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126 := by
        rw [div_eq_mul_one_div (q : ℝ≥0∞)]

end SlhDsaSecurity.BySourceTarget
