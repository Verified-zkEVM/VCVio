/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.ColdKey
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.RootCharge

/-! # Charging a successful forgery to coverage, graph events and weak keys -/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open scoped SLHDSA.SHAKE128s.Bridge.SharedExperiment.SampleSpaces
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
open GuardedFill

/-- The original FIPS game is bounded by its still-unpaid winning branches, the same-run
deferred graph/key charge, and the two initial-key address masses. -/
theorem original_win_le_uncharged_charge_two_weak (adv : Game.Adversary FIPS205.Answer PK)
    (q : Nat) (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q)
    (fallback : (s : FIPS205.core.PkSeed) →
      (input : LabCommon.Domain) → LabCommon.Range input) :
    let program := fun s => labProgram s adv true true (32*q-1, 2^64) (fallback s)
    let law := fun s => (slhGraph FIPS205.core s).deferredFillDraw ($ᵗ Secret) (program s)
    let wins := fun r : Filled =>
      ∃ out, (observe r.1.1).2.1 = some out ∧ SigningView.Wins id out
    let charged := fun s (r : Filled) => ((slhGraph FIPS205.core s).Conflict r.2.1 ∨
      (slhNodeKeys FIPS205.core s).TCHazard r.2.1) ∨ keyHazard s r.1.1 r.2.2 r.2.1
    let charge := fun s => ∫⁻ cost, cost ∂𝒟[(fun r =>
      2 * (((slhNodeKeys FIPS205.core s).keyEntries r.2.1.1).encard : ℝ≥0∞) /
        Nat.card FIPS205.core.Y + keyCharge s r.1 r.2.1.1) <$>
      (simulateQ (slhGraph FIPS205.core s).deferredImpl (program s)).run ((∅, ∅), [])]
    Pr{let out ← (Game.securityGame FIPS205.scheme).experiment () adv}[out.1 = true] ≤
      (∫⁻ s, Pr{let r ← law s}[
          wins r ∧ ¬IsWeakKey FIPS205.params r.1.1.1.1.1.1.1 ∧ ¬charged s r] + charge s
        ∂𝒟[($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)]) +
        2 * ((1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞)) := by
  classical
  intro program law wins charged charge
  let weak := fun r : Filled => IsWeakKey FIPS205.params r.1.1.1.1.1.1.1
  let M := (1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞)
  let μ := 𝒟[($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)]
  have initial := original_win_le_remaining_charge_mass adv q hlimit hbound fallback
  change _ ≤ (∫⁻ s, Pr{let r ← law s}[(wins r ∨ weak r) ∧ ¬charged s r] + charge s ∂μ) + M
    at initial
  have mass : (∫⁻ s, Pr{let r ← law s}[weak r] ∂μ) ≤ M :=
    deferred_weak_mass adv true (32*q-1, 2^64) fallback
  apply initial.trans
  rw [two_mul, ← add_assoc]
  apply add_le_add _ le_rfl
  apply le_trans _ (add_le_add le_rfl mass)
  rw [← lintegral_add_left Measurable.of_discrete]
  apply lintegral_mono
  intro s
  change Pr{let r ← law s}[(wins r ∨ weak r) ∧ ¬charged s r] + charge s ≤
    (Pr{let r ← law s}[wins r ∧ ¬weak r ∧ ¬charged s r] + charge s) +
      Pr{let r ← law s}[weak r]
  rw [add_right_comm]
  apply add_le_add _ le_rfl
  apply (prEvent_mono (law s) _ (fun r => (wins r ∧ ¬weak r ∧ ¬charged s r) ∨ weak r) ?_).trans
  · exact prEvent_or_le (law s) _ _
  · rintro r ⟨win | w, h⟩
    · by_cases w : weak r
      · exact Or.inr w
      · exact Or.inl ⟨win, w, h⟩
    · exact Or.inr w

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
