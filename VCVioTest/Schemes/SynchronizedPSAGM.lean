/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.SynchronizedPS.Security
public import VCVio.Schemes.SynchronizedPS.Game
import all VCVio.Schemes.SynchronizedPS.Reductions
public import Mathlib.Algebra.Field.ZMod

/-! # Synchronized PS regression checks over the field of order 101

Multiplication is the pairing and both generators are one. The fixtures exercise honest
aggregation, the signing-log synchronization condition, and a concrete lazy reduction.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional
open SynchronizedPS
open scoped ENNReal

namespace SynchronizedPSAGMTest

/-- Primality of the concrete scalar field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩
/-- Uniform scalar sampling without eager initialization of a field enumeration. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

/-- Honest two-signer aggregation is perfectly correct with a shared period hash cache. -/
theorem two_signers_correct :
    (ProbCompRuntime.rom (ℕ →ₒ ZMod 101)).evalDist (do
      let a := scheme (Period := ℕ) (LinearMap.mul (ZMod 101) (ZMod 101)) 1
      let sigs ← ([((3, 5), 7), ((11, 13), 17)] : List ((ZMod 101 × ZMod 101) × ZMod 101)).mapM
        fun p => a.sign (publicKeyOf 1 p.1) p.1 (23, p.2)
      let σ ← a.aggregate sigs
      a.aggregateVerify [((3, 5), (23, 7)), ((11, 13), (23, 17))] σ) {true} = 1 := by
  simpa [publicKeyOf] using aggregate_correctness
    (LinearMap.mul (ZMod 101) (ZMod 101)) 1 (23 : ℕ) [((3, 5), 7), ((11, 13), 17)]

/-- A target-period log with two distinct signed messages loses even when the forged message
is fresh and the aggregate verification bit is true. -/
theorem duplicate_period_rejected :
    AggregateSignatureAlg.Synchronized.winningEvent (23, (2 : ZMod 101))
      ([⟨(23, 0), 19⟩, ⟨(23, 1), 31⟩] : QueryLog ((ℕ × ZMod 101) →ₒ ZMod 101)) true = false := by
  apply AggregateSignatureAlg.Synchronized.winningEvent_eq_false_of_not_onePerPeriod
  simp [AggregateSignatureAlg.Synchronized.OnePerPeriod]

/-- Two same-period signatures interpolate a fresh valid message; synchronization is therefore
an essential winning condition in addition to ordinary freshness and verification. -/
theorem interpolated_signature_verifies (x y h : ZMod 101) :
    (LinearMap.mul (ZMod 101) (ZMod 101)) h (x + (2 : ZMod 101) * y) =
      (LinearMap.mul (ZMod 101) (ZMod 101))
        (2 * ((x + y) * h) - x * h) 1 := by
  simp only [LinearMap.mul_apply']
  ring

/-- An ordinary attacker interpolates a fresh message from two same-period signatures. -/
@[expose] def repeatedPeriodAdversary : AggregateSignatureAlg.Synchronized.Adversary
    (scheme (Period := ℕ) (LinearMap.mul (ZMod 101) (ZMod 101)) 1) where
  main _ := do
    let σ₀ : ZMod 101 ← (AGM.rawSpec (ZMod 101) ℕ (ZMod 101)).query (.inr (23, 0))
    let σ₁ : ZMod 101 ← (AGM.rawSpec (ZMod 101) ℕ (ZMod 101)).query (.inr (23, 1))
    return ((23, 2), [], 2 * σ₁ - σ₀)

/-- Running the actual signing oracle, aggregate verifier, and final winning test rejects the
interpolating adversary under every consistent period hash, despite its fresh valid aggregate. -/
theorem repeatedPeriod_run_rejected (x y : ZMod 101) (H : ℕ → ZMod 101) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) (do
      let a := scheme (Period := ℕ) (LinearMap.mul (ZMod 101) (ZMod 101)) 1
      let (out, log) ← a.runWithSigningOracle (publicKeyOf 1 (x, y)) (x, y)
        (repeatedPeriodAdversary.main (publicKeyOf 1 (x, y)))
      let verified ← a.aggregateVerify [(publicKeyOf 1 (x, y), out.1)] out.2.2
      return AggregateSignatureAlg.Synchronized.winningEvent out.1 log verified) =
      (pure false : ProbComp Bool) := by
  have hId (a : ZMod 101) : (liftM (m := Id) (a : Id (ZMod 101)) :
      ProbComp (ZMod 101)) = pure a := rfl
  simp [repeatedPeriodAdversary, SignatureAlg.runWithSigningOracle,
    SignatureAlg.signingOracle, QueryImpl.withLogging_apply, scheme,
    AggregateSignatureAlg.Synchronized.winningEvent,
    AggregateSignatureAlg.Synchronized.OnePerPeriod,
    unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_query_right, hId]

/-- The two gap coordinates separate a fresh target from one same-period signing occurrence,
including the branch where the signature coefficient is exactly one. -/
theorem weighted_gap_branch :
    AGM.verificationGap false ([0, 1] : List (ZMod 101)) [.inr (23, 3)] (23, 7) 23 = 0 ∧
      AGM.verificationGap true ([0, 1] : List (ZMod 101)) [.inr (23, 3)] (23, 7) 23 = 4 := by
  decide

/-- An algebraic fixture returns the first generator on message zero without making queries. -/
@[expose] def generatorForgery :
    AlgebraicAdversary (ZMod 101) ℕ (ZMod 101) (ZMod 101)
      (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1 where
  main input := pure (Explained.ofVectors input.groups ((23, 0), []) (fun s => match s with
    | false => [fun i => if i.val = 0 then 1 else 0]
    | true => []))
  algebraic input := Explained.valid_ofVectors _ _ _
  protocol input := by simp [Explained.ofVectors]

/-- The fixture's certified explanation erases to exactly its advertised aggregate forgery. -/
theorem generatorForgery_forget (pk : ZMod 101 × ZMod 101) :
    generatorForgery.toUnforgeableAdversary.main pk = pure ((23, 0), [], 1) := by
  simp [AlgebraicAdversary.toUnforgeableAdversary, generatorForgery,
    Explained.ofVectors, AGM.forgery, AGM.initialInput, sourceInputs, evaluate]

/-- With no signing queries the x-reduction returns the inverse of its one lazily sampled
period exponent. Its other uniform sample is the independent second secret key. -/
theorem xReduction_generator :
    xReduction generatorForgery 1 7 1 7 = (do
      let _y ← ($ᵗ (ZMod 101) : ProbComp _)
      let ρ ← $ᵗ (ZMod 101)
      return 1 / ρ) := by
  simp [xReduction, reductionRun, generatorForgery, indexedWeightedExtractionProgram,
    Explained.ofVectors, AGM.initialInput, sourceInputs, coefficients, evaluate,
    terms, weightedQuery, offset, QueryImpl.simulateQ_add_liftM_right]

/-- The explicit run with target-period exponent 71 extracts challenge 37. -/
theorem xReduction_explicit_run :
    (37 : ZMod 101) ∈ support (xReduction generatorForgery 1 37 1 37) := by
  have h : xReduction generatorForgery 1 37 1 37 = (do
      let _y ← ($ᵗ (ZMod 101) : ProbComp _)
      let ρ ← $ᵗ (ZMod 101)
      return 1 / ρ) := by
    simp [xReduction, reductionRun, generatorForgery, indexedWeightedExtractionProgram,
      Explained.ofVectors, AGM.initialInput, sourceInputs, coefficients, evaluate,
      terms, weightedQuery, offset, QueryImpl.simulateQ_add_liftM_right]
  simp only [h, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff]
  refine ⟨0, by simp, 71, by simp, ?_⟩
  symm
  exact (div_eq_iff (by decide : (71 : ZMod 101) ≠ 0)).2 (by decide)

/-- The main certified-key bound instantiates over the test field with an infinite period type. -/
theorem generatorForgery_unforgeable_bound :
    AggregateSignatureAlg.Synchronized.unforgeableAdvantage
        (ProbCompRuntime.rom (ℕ →ₒ ZMod 101)) (publicKeyOf 1)
        generatorForgery.toUnforgeableAdversary ≤
      Pr{let b ← DLog11.experiment 1 1 (xReduction generatorForgery)}[b = true] +
      Pr{let b ← DLog11.experiment 1 1 (yReduction generatorForgery)}[b = true] +
      Pr{let b ← DLog11.experiment 1 1 (hashReduction generatorForgery)}[b = true] +
      (1 / 101 : ℝ≥0∞) := by
  have h := unforgeableAdvantage_le_of_algebraic generatorForgery
    (by
      constructor
      · intro a b hab
        simpa only [smul_eq_mul, mul_one] using hab
      · intro a
        exact ⟨a, by simp⟩)
    (by simp)
  simpa using h

end SynchronizedPSAGMTest
