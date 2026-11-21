/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Average
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Cache
import VCVio.OracleComp.EvalDist.Sum

/-!
# Remaining work after paying for weak keys
-/

public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal NNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open scoped SLHDSA.SHAKE128s.Bridge.SharedExperiment.SampleSpaces
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical


/-- At every global cap in the nontrivial regime, averaging the complete native charge and
paying both physical comparison escape terms gives the strict-cap expression. -/
theorem native_price_with_escapes_le_strict_cap (q : Nat) (small : 2 * q < 2 ^ 128)
    (adv : Game.Adversary FIPS205.Answer PK) (fb : Seed → LabFallback) (L : Nat) :
    let K := 32 * q - 1
    let R := 16 * 2 ^ 128
    let blocks := fun s =>
      NoticingTape.blockRunOf (Native.nativeRun s adv true (K, 2 ^ 64) (fb s)) L R
    (∫⁻ s, (∫⁻ b, Native.completeCharge s R b.2 ∂𝒟[blocks s])
        ∂𝒟[($ᵗ Seed : ProbComp Seed)]) + 2 * weakMass ≤
      ((32 * q - 1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) + 34 * weakMass := by
  classical
  intro K R blocks
  let den : ℝ≥0∞ := ((16 * 2 ^ 128 : Nat) : ℝ≥0∞)
  let weak := fun b : Block => IsWeakKey FIPS205.params b.2.1.1.1
  let mass := fun s => Pr{let b ← blocks s}[weak b]
  have atSeed (s : Seed) : (∫⁻ b, Native.completeCharge s R b.2 ∂𝒟[blocks s]) ≤
      (K : ℝ≥0∞) / den + 32 * mass s := by
    have pointwise (b : Block) (hb : b ∈ support (blocks s)) :
        Native.completeCharge s R b.2 ≤ (K : ℝ≥0∞) / den + 32 * (if weak b then 1 else 0) := by
      have hr := (NoticingTape.mem_support_blockRunOf _ _ _ b hb).2.2
      have reserve := Native.native_whole_reserve s adv (K, 2 ^ 64) (fb s) b.1.1 b.1.2 b.2 hr
      have cap : b.2.2.2.1.1 ≤ K := reserve.paid_le.1
      apply (reserve.complete_charge_le (cap.trans (by dsimp only [K]; omega))).trans
      apply add_le_add _ le_rfl
      simpa only [div_eq_mul_inv] using mul_le_mul_left (Nat.cast_le.mpr cap :
        (b.2.2.2.1.1 : ℝ≥0∞) ≤ K) den⁻¹
    have integrated := lintegral_mono_ae ((evalDist_ae_mem_support (blocks s)).mono
      fun b hb => pointwise b hb)
    have indicator : (∫⁻ b, (if weak b then (1 : ℝ≥0∞) else 0) ∂𝒟[blocks s]) = mass s := by
      change (∫⁻ b, ({b | weak b} : Set Block).indicator (fun _ => (1 : ℝ≥0∞)) b ∂𝒟[blocks s]) = _
      rw [lintegral_indicator_const MeasurableSet.of_discrete, one_mul]
      exact (prEvent_eq_evalDist_of_discrete _ _).symm
    simpa only [lintegral_add_left Measurable.of_discrete, lintegral_const,
      lintegral_const_mul _ Measurable.of_discrete,
      measure_univ, mul_one, indicator] using integrated
  have averaged := lintegral_mono (μ := 𝒟[($ᵗ Seed : ProbComp Seed)]) atSeed
  have allWeak := native_block_weak_average adv true (K, 2 ^ 64) fb L R
  calc
    _ ≤ ((K : ℝ≥0∞) / den + 32 * (∫⁻ s, mass s ∂𝒟[($ᵗ Seed : ProbComp Seed)])) +
          2 * weakMass := by
      apply add_le_add _ le_rfl
      simpa only [lintegral_add_left Measurable.of_discrete, lintegral_const,
      lintegral_const_mul _ Measurable.of_discrete,
        measure_univ, mul_one] using averaged
    _ ≤ ((K : ℝ≥0∞) / den + 32 * weakMass) + 2 * weakMass := by
      gcongr
    _ = _ := by rw [add_assoc, ← add_mul, show (32 : ℝ≥0∞) + 2 = 34 by norm_num]

theorem retained_reserve_lt_headline (q : Nat) (hq : 1 ≤ q) :
    ((32*q-1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) + 34 * weakMass <
      (q : ℝ≥0∞) / ((2^127 : Nat) : ℝ≥0∞) := by
  have weak : 34 * weakMass < (1 : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) := by
    have hn : (34 : ℝ≥0) * (1591788895347057694892543 / (2 ^ 256)) < 1 / (16 * 2 ^ 128) := by
      rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity)]
      norm_num
    have hc := ENNReal.coe_lt_coe.mpr hn
    push_cast [ENNReal.coe_div (by positivity : (2:NNReal)^256 ≠ 0),
      ENNReal.coe_div (by positivity : (16:NNReal)*2^128 ≠ 0)] at hc
    simpa only [weakMass, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul] using hc
  let K := 32*q-1
  have gap : K + 1 = 32 * q := by dsimp only [K]; omega
  calc
    _ < (K : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) := ENNReal.add_lt_add_left (by finiteness) weak
    _ = ((K + 1 : Nat) : ℝ≥0∞) / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞) := by
      rw [Nat.cast_add, Nat.cast_one, ENNReal.add_div]
    _ = (q : ℝ≥0∞) * (32 / ((16 * 2 ^ 128 : Nat) : ℝ≥0∞)) := by
      rw [gap, Nat.cast_mul]
      simp only [Nat.cast_ofNat, mul_div_assoc, mul_comm]
    _ = (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
      rw [div_eq_mul_inv]
      congr 1
      have hn : (32 : NNReal) / (16 * 2 ^ 128) = (2 ^ 127)⁻¹ := by norm_num
      have hc := congrArg (fun x : NNReal => (x : ℝ≥0∞)) hn
      push_cast [ENNReal.coe_div (by positivity : (16:NNReal)*2^128 ≠ 0),
        ENNReal.coe_inv (by positivity : (2:NNReal)^127 ≠ 0)] at hc
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using hc

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
