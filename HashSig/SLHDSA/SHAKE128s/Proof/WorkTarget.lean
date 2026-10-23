/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.BySourceTarget

/-!
# `127` bits on the adversary's own work: the assembly

The three terms of the `127` proof at `BySourceBridge.TailBudgetW`, where key generation's and
the signer's calls are free. The answer half is `BySourceTarget.answerBound` at `q / 2 ^ 128 +
2 ^ -126`. The shared half is read **with an accepted forgery**: a win verifies, and an accepted
verification is what pays for the shared half's fixed costs once key generation no longer does.
Given the shared half at `(q - 8) / 2 ^ 128`, the three terms sum to at most `q / 2 ^ 127`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.WorkTarget

open Security CanonicalGraph WarmedGame Target RoutedSplit BracketedRun CarrierTail CarrierThin
  BySourceBridge

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
/-- **The adversary's-work budget bounds the win by the three terms**, the shared one read with
an accepted forgery. -/
theorem warmed_le (q : Nat) (adversary : Adversary) (hbudget : TailBudgetW adversary q)
    (shared : ℝ≥0∞)
    (hshared : Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[GoodWalk pair.1 ∧
        (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1),
          (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair) ∧
        (FinalAssembly.forgetFused pair.2).1.1.verified = true] ≤ shared) :
    Pr{let result ← WarmedGame.warmedRun adversary}[Wins result.1.2.1] ≤
      ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126) +
        (shared + (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞))) := by
  classical
  rw [WarmedGame.warmedRun_eq, prEvent_map,
    show (do let walk ← graphWalk; let result ← tail adversary walk; pure (walk, result)) =
      pairedRun adversary from rfl,
    pairedRun_eq_map_pairedFused adversary (CarrierTail.carrierTail CarrierThin.keep127 adversary) FinalAssembly.forgetFused (CarrierTail.forgetFused_carrierTail CarrierThin.keep127 adversary),
    prEvent_map]
  have hgoodAnswer :
      Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[GoodWalk pair.1 ∧
          AnswerBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∧ ¬ Target127.late pair] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126 := by
    refine Averaging.probEvent_bind_pair_le graphWalk (CarrierTail.carrierTail CarrierThin.keep127 adversary)
      (fun walk result => GoodWalk walk ∧
        AnswerBad ((walk.1, (FinalAssembly.forgetFused result).1), (FinalAssembly.forgetFused result).2) ∧ ¬ Target127.late (walk, result)) _
      fun walk hwalk => ?_
    by_cases hgood : GoodWalk walk
    · exact le_trans (prEvent_mono fun result _ hbad => hbad.2)
        (BySourceTarget.answerBound q adversary hbudget walk hwalk hgood)
    · rw [show (fun result => GoodWalk walk ∧
        AnswerBad ((walk.1, (FinalAssembly.forgetFused result).1), (FinalAssembly.forgetFused result).2) ∧
          ¬ Target127.late (walk, result)) = fun _ => False from by funext _; simp [hgood]]
      simp
  calc Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[Wins (FinalAssembly.forgetFused pair.2).1.1]
      ≤ Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[(GoodWalk pair.1 ∧
            AnswerBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∧ ¬ Target127.late pair) ∨
          ((GoodWalk pair.1 ∧
            (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair) ∧
              (FinalAssembly.forgetFused pair.2).1.1.verified = true) ∨
              ¬ GoodWalk pair.1)] := by
        refine prEvent_mono fun pair hpair hwin => ?_
        by_cases hgood : GoodWalk pair.1
        · obtain ⟨walk, hwalk, result, hresult, hpair⟩ : ∃ walk ∈ support graphWalk,
              ∃ result ∈ support (CarrierTail.carrierTail CarrierThin.keep127 adversary walk), (walk, result) = pair := by
            simpa [pairedFused, eq_comm] using hpair
          subst hpair
          have hforgetMem : FinalAssembly.forgetFused result ∈ support (tail adversary walk) := by
            rw [← CarrierTail.forgetFused_carrierTail CarrierThin.keep127 adversary walk, support_map]
            exact ⟨result, hresult, rfl⟩
          by_cases hlate : Target127.late (walk, result)
          · exact Or.inr (Or.inl ⟨hgood, Or.inr hlate, hwin.1⟩)
          · rcases SigningFaithful.cases_of_win_charged adversary hwalk hforgetMem hwin with
              hAnswerBad | hInputBad
            · exact Or.inl ⟨hgood, hAnswerBad, hlate⟩
            · exact Or.inr (Or.inl ⟨hgood, Or.inl hInputBad, hwin.1⟩)
        · exact Or.inr (Or.inr hgood)
    _ ≤ Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[GoodWalk pair.1 ∧
            AnswerBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∧ ¬ Target127.late pair] +
          Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[(GoodWalk pair.1 ∧
            (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair) ∧
              (FinalAssembly.forgetFused pair.2).1.1.verified = true) ∨
              ¬ GoodWalk pair.1] := prEvent_or_le _ _ _
    _ ≤ Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[GoodWalk pair.1 ∧
            AnswerBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∧ ¬ Target127.late pair] +
          (Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[GoodWalk pair.1 ∧
              (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1), (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair) ∧
              (FinalAssembly.forgetFused pair.2).1.1.verified = true] +
            Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[¬ GoodWalk pair.1]) :=
        add_le_add le_rfl (prEvent_or_le _ _ _)
    _ ≤ ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 126) +
          (shared +
            (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞))) :=
        add_le_add hgoodAnswer
          (add_le_add hshared
            (prob_bad_walk_pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)))

/-- **The win at the warmed run, within `q / 2 ^ 127`**, given the shared half at
`(q - 8) / 2 ^ 128` on accepted forgeries. -/
theorem warmed_bound (q : Nat) (adversary : Adversary) (hbudget : TailBudgetW adversary q)
    (hq : 8 ≤ q)
    (hshared : Pr{let pair ← pairedFused (CarrierTail.carrierTail CarrierThin.keep127 adversary)}[GoodWalk pair.1 ∧
        (InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1),
          (FinalAssembly.forgetFused pair.2).2) ∨ Target127.late pair) ∧
        (FinalAssembly.forgetFused pair.2).1.1.verified = true] ≤
        ((q - 8 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr{let result ← WarmedGame.warmedRun adversary}[Wins result.1.2.1] ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  refine le_trans (warmed_le q adversary hbudget _ hshared) ?_
  have hdefects := AnswerFired.defects_le
  calc _ = ((q - 8 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defectsAt ((1 : ℝ≥0∞) / 2 ^ 126)) := by
        unfold defectsAt
        ring
    _ ≤ ((q - 8 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            ((6 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        add_le_add le_rfl (add_le_add le_rfl hdefects)
    _ = ((q - 8 + q + 6 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
        congr 2
    _ ≤ ((2 * q : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _
    _ = (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
        rw [show (2 ^ 128 : Nat) = 2 * 2 ^ 127 by norm_num, Nat.cast_mul, Nat.cast_mul,
          ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

end SlhDsaSecurity.WorkTarget
