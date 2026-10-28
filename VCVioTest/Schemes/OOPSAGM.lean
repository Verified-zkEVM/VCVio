/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.OOPS.Admissibility
public import VCVio.Schemes.OOPS.AGM.Security
import all VCVio.Schemes.OOPS.AGM.Reductions
public import Mathlib.Algebra.Field.ZMod

/-! # Concrete OOPS checks over the field of order 101

Multiplication supplies the pairing and both generators are one. The tests check an honest
polynomial signature, target-topic counting, the nonzero polynomial gap, and an explicit
execution of the good reduction. Uniform field sampling uses `Fin 101` without a load-time
enumeration of the field.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional
open scoped ENNReal

namespace OOPSAGMTest

/-- Primality of the test field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩
/-- Uniform field sampling with no initialization-time enumeration. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

private abbrev Groups := SourceGroup (ZMod 101) (ZMod 101)

/-- A degree-zero algebraic adversary that returns the first generator without queries. -/
@[expose] def generatorForgery :
    OOPS.AlgebraicAdversary (ZMod 101) Bool (ZMod 101) (ZMod 101)
      (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1 0 where
  main input := pure (Explained.ofVectors input.groups (0, false) (fun s => match s with
    | false => [fun i => if i.val = 0 then 1 else 0]
    | true => []))
  algebraic input := Explained.valid_ofVectors _ _ _
  protocol input := by simp [Explained.ofVectors]

private theorem generatorForgery_raw (pk : (ZMod 101)) :
    generatorForgery.toUnforgeableAdversary.main pk = pure ((0, false), 1) := by
  simp [OOPS.AlgebraicAdversary.toUnforgeableAdversary, generatorForgery,
    Explained.ofVectors, OOPS.AGM.forgery, OOPS.AGM.initialInput, sourceInputs, evaluate]

/-- The generator fixture obeys the degree-zero rule on every actual ROM execution. -/
theorem generatorForgery_admissible : generatorForgery.Admissible := by
  intro x z hz
  simp only [generatorForgery_raw, SignatureAlg.runWithSigningOracle, simulateQ_pure,
    WriterT.run_pure, StateT.run'_eq, StateT.run_pure, map_pure, support_pure,
    Set.mem_singleton_iff] at hz
  subst z
  decide

/-- Degree-two OOPS is perfectly complete over the concrete field in the actual lazy ROM. -/
theorem perfectlyComplete :
    (OOPS.scheme (T := Bool) (LinearMap.mul (ZMod 101) (ZMod 101)) 1 2).PerfectlyComplete
      (ProbCompRuntime.rom ((Bool × Fin 3) →ₒ (ZMod 101))) :=
  OOPS.perfectlyComplete _ _ _

/-- With all three bases equal to seven, message three hashes to ninety-one and secret five
signs it as fifty-one. This checks the actual signing program against a fixed oracle table. -/
theorem honest_signature :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (fun _ : Bool × Fin 3 => (7 : (ZMod 101)))))
      ((OOPS.scheme (T := Bool) (LinearMap.mul (ZMod 101) (ZMod 101)) 1 2).sign 5 5 (3, false)) =
      pure (51 : (ZMod 101)) := by
  simp only [OOPS.scheme, simulateQ_bind, OOPS.hash, simulateQ_unifFwd_weightedQuery,
    pure_bind, simulateQ_pure]
  congr 1

/-- The honestly computed signature satisfies the actual verification program. -/
theorem honest_verification :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (fun _ : Bool × Fin 3 => (7 : (ZMod 101)))))
      ((OOPS.scheme (T := Bool) (LinearMap.mul (ZMod 101) (ZMod 101)) 1 2).verify 5 (3, false) 51) =
      pure true := by
  simp only [OOPS.scheme, simulateQ_bind, OOPS.hash, simulateQ_unifFwd_weightedQuery,
    pure_bind, simulateQ_pure]
  congr 1

/-- Duplicate messages and other topics do not increase the forged topic's distinct count. -/
theorem admissible_repeated_and_other_topic :
    OOPS.admissible 1 ((2 : (ZMod 101)), false) [(1, false), (1, false), (2, true), (3, true)] := by
  decide

/-- Two distinct messages on the forged topic violate a degree-one allowance. -/
theorem not_admissible_two_messages :
    ¬ OOPS.admissible 1 ((3 : (ZMod 101)), false) [(1, false), (2, false)] := by decide

/-- The polynomial gap theorem applies to an arbitrary coefficient on one signed message. -/
theorem nonzero_gap (ξ : Fin 1 → (ZMod 101)) :
    ∃ j : Fin 2,
      gapCoeff (OOPS.weight (F := (ZMod 101)) 1) (2, false)
        (fun _ : Fin 1 => (1, false)) ξ (false, j) ≠ 0 := by
  apply OOPS.exists_gapCoeff_ne_zero
  · decide
  · intro q h
    have h' : (2 : (ZMod 101)) = 1 := congrArg Prod.fst h
    exact (by decide : (2 : (ZMod 101)) ≠ 1) h'

/-- A certified generator forgery forgets to the corresponding ordinary signature adversary. -/
theorem generator_forgery_exists :
    ∃ A : OOPS.AlgebraicAdversary (ZMod 101) Bool (ZMod 101) (ZMod 101)
      (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1 0,
      ∀ pk, A.toUnforgeableAdversary.main pk = pure ((0, false), 1) :=
  ⟨generatorForgery, generatorForgery_raw⟩

private theorem generatorForgery_good (X Y : (ZMod 101)) :
    OOPS.goodReduction generatorForgery 1 X 1 Y =
      (fun ρ : (ZMod 101) => 1 / ρ) <$> ($ᵗ (ZMod 101)) := by
  simp [OOPS.goodReduction, OOPS.reductionRun, weightedExtractionProgram,
    generatorForgery, Explained.ofVectors, OOPS.AGM.initialInput, sourceInputs,
    OOPS.coefficients, evaluate, OOPS.terms, weightedQuery,
    QueryImpl.simulateQ_add_liftM_right]

/-- A concrete good-reduction execution with base value seventy-one extracts thirty-seven. -/
theorem good_reduction_run :
    (37 : (ZMod 101)) ∈ support (OOPS.goodReduction generatorForgery 1 37 1 37) := by
  rw [generatorForgery_good, support_map]
  refine ⟨71, ?_, ?_⟩
  · simp
  · exact (div_eq_iff (by decide : (71 : ZMod 101) ≠ 0)).2 (by decide)

/-- The concrete admissible adversary instantiates the main EUF-CMA bound over `ZMod 101`
with the existing random-oracle game and both named reductions. -/
theorem generatorForgery_unforgeable_bound :
    SignatureAlg.unforgeableAdvantage
        (ProbCompRuntime.rom ((Bool × Fin 1) →ₒ ZMod 101))
        generatorForgery.toUnforgeableAdversary ≤
      Pr{let b ← DLog11.experiment 1 1 (OOPS.goodReduction generatorForgery)}[b = true] +
      Pr{let b ← DLog11.experiment 1 1 (OOPS.badReduction generatorForgery)}[b = true] +
      (1 / 101 : ℝ≥0∞) := by
  have h := OOPS.unforgeableAdvantage_le_of_algebraic generatorForgery
    generatorForgery_admissible
    (by
      constructor
      · intro a b hab
        simpa only [smul_eq_mul, mul_one] using hab
      · intro a
        exact ⟨a, by simp⟩)
    (by simp)
  simpa using h

end OOPSAGMTest
