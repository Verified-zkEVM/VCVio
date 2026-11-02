/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import PairRun
import all PairRun
import all NativePotential
import all Thin1Header
import VCVio.EvalDist.Monad.Branch

/-! # Reach-conditioned actual-key pair thinning in the native role experiment -/

public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
namespace SLHDSA.Security.Coverage
open NativeThin1 NativeThin2

/-- Distinct actual-key slots incur squared reciprocal-cardinality cost before both fire. -/
theorem prEvent_roleRun_pair_firedAtActualKey_le
    {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
    (e : core.SkSeed ≃ core.Y)
    (kappa : PublicKeyCore core → core.Y) (pkSeed : core.PkSeed)
    (adv : UnforgeableAdversary
      (romScheme core e (fun pk => pure (kappa pk)) (pure pkSeed)))
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (first second : Nat) (horder : first < second) :
    Pr{let z ← roleRun core adv pkSeed L}[
        second < z.2.2.1.cnt TapeClass.forger ∧
          FiredAtActualKey z first ∧ FiredAtActualKey z second] ≤
      ((Nat.card core.Y : ℝ≥0∞)⁻¹) ^ 2 *
        Pr{let z ← roleRun core adv pkSeed L}[
          first < z.2.2.1.cnt TapeClass.forger] :=
 by
  classical
  let mx := roleRun core adv pkSeed L
  let reach : DeriveOutcome core × RoleState core → Prop :=
    fun z => first < z.2.2.1.cnt TapeClass.forger
  let fire : DeriveOutcome core × RoleState core → Prop :=
    fun z => Fired core z.1.pk z.2 first ∧ Fired core z.1.pk z.2 second
  let epsilon : ℝ≥0∞ := ((Nat.card core.Y : ℝ≥0∞)⁻¹)^2
  let _ : MeasurableSpace (DeriveOutcome core × RoleState core) := ⊤
  have expected : ∫⁻ r, r ∂𝒟[(fun z => pairTerminalValue core z.1.pk first second z.2) <$> mx] ≤
      epsilon :=
    (lintegral_id_evalDist_map_mono mx fun z =>
      pair_terminal_credit core z.1.pk kappa L first second horder z.2).trans
      (whole_product_potential core kappa pkSeed e adv L hL first second (Nat.ne_of_lt horder))
  have eventIntegral (P : DeriveOutcome core × RoleState core → Prop) (a : ℝ≥0∞) :
      ∫⁻ z, (if P z then a else 0) ∂𝒟[mx] = a * Pr{let z ← mx}[P z] := by
    change ∫⁻ z, ({z | P z} : Set _).indicator (fun _ => a) z ∂𝒟[mx] = _
    rw [lintegral_indicator_const MeasurableSet.of_discrete, prEvent_eq_evalDist_of_discrete]
  rw [lintegral_id_evalDist_map] at expected
  change (∫⁻ z, (if fire z then 1 else 0) +
    (if ¬reach z then epsilon else 0) ∂𝒟[mx]) ≤ epsilon at expected
  have fireIntegral : (∫⁻ z, (if fire z then (1 : ℝ≥0∞) else 0) ∂𝒟[mx]) =
      1 * Pr{let z ← mx}[fire z] := by
    convert eventIntegral fire 1 using 1
    apply lintegral_congr
    intro z
    by_cases h : fire z <;> simp [h]
  have notIntegral : (∫⁻ z, (if ¬reach z then epsilon else 0) ∂𝒟[mx]) =
      epsilon * Pr{let z ← mx}[¬reach z] := by
    convert eventIntegral (fun z => ¬reach z) epsilon using 1
    apply lintegral_congr
    intro z
    by_cases h : reach z <;> simp [h]
  rw [lintegral_add_left Measurable.of_discrete, fireIntegral, notIntegral, one_mul]
    at expected
  have complement : Pr{let z ← mx}[reach z] + Pr{let z ← mx}[¬reach z] = 1 := by
    simpa only [measure_univ] using prEvent_add_prEvent_not mx reach
  have partition : epsilon * Pr{let z ← mx}[reach z] +
      epsilon * Pr{let z ← mx}[¬reach z] = epsilon := by
    rw [← mul_add, complement, mul_one]
  have singleFinite : (Nat.card core.Y : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    simpa only [one_div] using
      (ENNReal.div_ne_top ENNReal.one_ne_top (Nat.cast_ne_zero.mpr Nat.card_pos.ne') :
        (1 : ℝ≥0∞) / (Nat.card core.Y : ℝ≥0∞) ≠ ⊤)
  have epsilonFinite : epsilon ≠ ⊤ := by
    simpa only [epsilon, pow_two] using ENNReal.mul_ne_top singleFinite singleFinite
  have thin := (ENNReal.add_le_add_iff_right
    (ENNReal.mul_ne_top epsilonFinite (prEvent_ne_top _))).mp (expected.trans_eq partition.symm)
  exact (prEvent_mono mx _ fire fun _ h => h.2).trans thin


end SLHDSA.Security.Coverage
#print axioms SLHDSA.Security.Coverage.prEvent_roleRun_pair_firedAtActualKey_le
