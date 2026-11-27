/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Average
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Cache
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coverage.ExpectedCredit

/-!
# Summing coverage and graph charges at the terminal cache

FORS coverage and graph or encoding hazards are bounded by a single expected charge evaluated on
the same terminal block.
-/

public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open scoped SLHDSA.SHAKE128s.Bridge.SharedExperiment.SampleSpaces
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical

/-- The FORS coverage event and graph/encoding charge are paid by one expectation on the same
actual native block, with no fixed-seed resource premise. -/
theorem covered_plus_graph_le_price (s : Seed) (adv : Game.Adversary FIPS205.Answer PK)
    (q : Nat) (fb : LabFallback) :
    let R := 16 * 2 ^ 128
    let blocks := NoticingTape.blockRunOf
      (Native.nativeRun s adv true (32 * q - 1, 2 ^ 64) fb) (2 ^ 64 + 1) R
    Pr{let b ← blocks}[GuardedFill.actualCoverage b] + (∫⁻ cost, cost ∂𝒟[graphPrice s <$> blocks]) ≤
      ∫⁻ b, Native.completeCharge s R b.2 ∂𝒟[blocks] := by
  classical
  intro R blocks
  let A : ℝ≥0∞ := 1 / ((8 * 2 ^ 128 : Nat) : ℝ≥0∞)
  let B : ℝ≥0∞ := ((9 * 2 ^ 99 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞) +
    (R : ℝ≥0∞) / ((2 ^ 303 : Nat) : ℝ≥0∞)
  let N := fun b : Block => (b.2.2.1.2.2.1.cnt .forger : ℝ≥0∞)
  let rare := fun b : Block => 2 ≤ b.2.2.1.2.2.1.cnt .signer
  let μ := 𝒟[blocks]
  have coverage := GuardedFill.actualCoverage_le_paid q s adv fb
  change Pr{let b ← blocks}[GuardedFill.actualCoverage b] ≤
    A * Pr{let b ← blocks}[rare b] + (∫⁻ k, k ∂𝒟[N <$> blocks]) * B at coverage
  have rareMass : (∫⁻ b, (if rare b then (1 : ℝ≥0∞) else 0) ∂μ) =
      Pr{let b ← blocks}[rare b] := by
    have eq (b : Block) : (if rare b then (1 : ℝ≥0∞) else 0) =
        ({b | rare b} : Set Block).indicator (fun _ => (1 : ℝ≥0∞)) b := by
      by_cases hr : rare b <;> simp [hr, Set.indicator]
    simp_rw [eq]
    rw [lintegral_indicator_const MeasurableSet.of_discrete, one_mul]
    exact (prEvent_eq_evalDist_of_discrete _ _).symm
  apply (add_le_add coverage le_rfl).trans
  rw [← rareMass, lintegral_id_evalDist_map, lintegral_id_evalDist_map,
    ← lintegral_const_mul A Measurable.of_discrete, ← lintegral_mul_const B Measurable.of_discrete,
    ← lintegral_add_left Measurable.of_discrete, ← lintegral_add_left Measurable.of_discrete]
  apply lintegral_mono
  intro b
  have graph := Native.joint_charge_le_cache_alias s b.2
  change graphPrice s b ≤ _ at graph
  apply (add_le_add le_rfl graph).trans
  unfold Native.completeCharge
  dsimp only
  apply le_trans _ le_self_add
  apply le_of_eq
  have pay : A * (if rare b then 1 else 0) =
      (if 2 ≤ b.2.2.1.2.2.1.cnt .signer then 1 else 0) / ((8 * 2 ^ 128 : Nat) : ℝ≥0∞) := by
    by_cases hr : 2 ≤ b.2.2.1.2.2.1.cnt .signer <;> simp [A, rare, hr]
  rw [pay]
  dsimp only [N, B]
  ac_rfl

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
