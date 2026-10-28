/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Security
public import Mathlib.Algebra.Field.ZMod
import VCVio.EvalDist.ProbabilityBounds

/-! # BLS over the field of order 101

Concrete consumers of the Boneh–Lynn–Shacham scheme, with multiplication as the pairing
and both generators equal to one. The adversary hashes `false`, signs `true`, and uses
the scalar visible in this toy public key to forge on `false`.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace BLSTest

/-- Primality certificate for the local test field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- Sample directly as `Fin 101`, without constructing an enumeration at module load. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

local notation "toyScheme" =>
  BLS.scheme (M := Bool) (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1

private def adversary : SignatureAlg.UnforgeableAdversary toyScheme where
  main pk := do
    let h : ZMod 101 ←
      ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inl (.inr false))
    let _ : ZMod 101 ←
      ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inr true)
    return (false, pk.2 * h)

/-- Multiplication with unit generators instantiates the generic ROM completeness theorem. -/
theorem perfectlyComplete :
    (toyScheme).PerfectlyComplete (ProbCompRuntime.rom (Bool →ₒ ZMod 101)) :=
  BLS.perfectlyComplete _ _ _

/-- The fixture uses one direct hash query and one signing query on every public key. -/
private theorem queryBound : BLS.QueryBound adversary 1 1 := by
  intro pk
  constructor <;> simp [adversary, isQueryBoundP_query_bind_iff]

/-- In the concrete pairing, every accepted signature equals the secret times the hash. -/
theorem verification_iff (x h σ : ZMod 101) : σ * 1 = h * (x * 1) ↔ σ = x * h := by
  simpa using BLS.pairing_eq_iff (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1
    (by intro y; exact ⟨y, by simp⟩) (by simp) x h σ

/-- Guessing the fixture's first hash slot solves every co-CDH challenge in this toy group. -/
private theorem reductionAt_zero (x h : ZMod 101) :
    BLS.reductionAt adversary 0 1 1 (x • 1) (x • 1) h =
      (fun _ : ZMod 101 => x • h) <$> ($ᵗ ZMod 101 : ProbComp (ZMod 101)) := by
  simp only [BLS.reductionAt, adversary, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, OptionT.run_bind, Option.elimM, StateT.run'_eq, StateT.run_bind]
  rw [BLS.embeddingOracle_run_hash,
    BLS.embeddingEntry_run_of_target false (∅, 0) (by rfl)]
  simp only [map_pure, pure_bind, Option.elim_none, Option.elim_some, StateT.run_bind]
  rw [BLS.embeddingOracle_run_sign]
  simp only [OptionT.run_monadLift, monadLift_self, bind_pure_comp,
    bind_map_left, map_bind, Functor.map_map, Option.elim_some, OptionT.run_pure]
  rw [BLS.embeddingEntry_run_of_fresh 0 true _ (by simp) (by decide)]
  simp only [bind_map_left, Option.map_some, Option.elim_some]
  simp [BLS.embeddingEntry]

private theorem reduction_success :
    (3 : ℝ≥0∞)⁻¹ ≤
      Pr{let b ← CoCDH.experiment 1 1 (BLS.reduction adversary 1 1)}[b = true] := by
  unfold CoCDH.experiment
  apply le_prEvent_bind_of_forall_le _ (prEvent_true_eq_one _) _ _
  intro x
  apply le_prEvent_bind_of_forall_le _ (prEvent_true_eq_one _) _ _
  intro h
  change (3 : ℝ≥0∞)⁻¹ ≤ Pr{let b ← (do
    let j ← ($ᵗ Fin 3 : ProbComp (Fin 3))
    let w ← BLS.reductionAt adversary j.val 1 1 (x • 1) (x • 1) h
    pure (decide (w = x • h)) : ProbComp Bool)}[b = true]
  calc
    (3 : ℝ≥0∞)⁻¹ = (3 : ℝ≥0∞)⁻¹ * 1 := by simp
    _ ≤ _ := mul_le_prEvent_bind_of_forall _ _ (fun j : Fin 3 => j = 0) _
      (by simpa only [Fintype.card_fin, Nat.cast_ofNat] using
        (SampleableType.prEvent_uniformSample_eq_singleton (0 : Fin 3)).ge) (by
        intro j hj
        subst j
        simp only [Fin.val_zero]
        rw [reductionAt_zero x h]
        simp)

/-- A concrete one-hash, one-sign adversary satisfies the factor-three bound for the named
index-guessing reduction. The proof uses the successful first-slot branch directly. -/
theorem one_hash_one_sign_bound :
    let A : SignatureAlg.UnforgeableAdversary toyScheme := ⟨fun pk => do
      let h : ZMod 101 ←
        ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inl (.inr false))
      let _ : ZMod 101 ←
        ((unifSpec + (Bool →ₒ ZMod 101)) + (Bool →ₒ ZMod 101)).query (.inr true)
      return (false, pk.2 * h)⟩
    BLS.QueryBound A 1 1 ∧
      SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Bool →ₒ ZMod 101)) A ≤
        3 * Pr{let b ← CoCDH.experiment 1 1 (BLS.reduction A 1 1)}[b = true] := by
  change BLS.QueryBound adversary 1 1 ∧ _
  refine ⟨queryBound, ?_⟩
  calc
    _ ≤ 1 := MeasureTheory.measure_le_one _ _
    _ = 3 * (3 : ℝ≥0∞)⁻¹ :=
      (ENNReal.mul_inv_cancel (by norm_num) (by norm_num)).symm
    _ ≤ _ := mul_le_mul_right reduction_success 3

end BLSTest
