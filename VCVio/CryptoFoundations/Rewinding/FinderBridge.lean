/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Finder
public import VCVio.CryptoFoundations.Rewinding.Eager
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Tree finders against frozen reruns

A frozen prover determines one random Boolean acceptance function on complete challenge vectors.
The eager representation preserves the finder's joint output and complete-run counter, so uniform
success and unconditional cost bounds transfer by averaging over this function.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Rewinding

variable {R : Type} {C : R → Type}

/-- Average acceptance rate of a randomly chosen Boolean acceptance function. -/
@[expose] noncomputable def averageAcceptRate [Fintype R] [DecidableEq R]
    [∀ r, Fintype (C r)] [∀ r, DecidableEq (C r)]
    (F : ProbComp (((r : R) → C r) → Bool)) : ℝ≥0∞ :=
  letI : MeasurableSpace (((r : R) → C r) → Bool) := ⊤
  ∫⁻ f, acceptRate f ∂𝒟[F]

/-- Uniform finder success bounds average over a randomly chosen acceptance function. -/
theorem IsTreeFinder.average_success [Fintype R] [LinearOrder R]
    [∀ r, Fintype (C r)] [∀ r, DecidableEq (C r)]
    {k : R → ℕ} {nodeOk : (r : R) → (Fin (k r) → C r) → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option (VecTree C k))} {κ T : ℝ≥0∞}
    (h : IsTreeFinder k nodeOk find κ T) (F : ProbComp (((r : R) → C r) → Bool)) :
    averageAcceptRate F - κ ≤
      Pr{let z ← (do let f ← F; runFinder find f)}[z.1.isSome] := by
  let : MeasurableSpace (((r : R) → C r) → Bool) := ⊤
  rw [averageAcceptRate, prEvent_bind_eq_lintegral_of_discrete]
  calc
    (∫⁻ f, acceptRate f ∂𝒟[F]) - κ ≤
        (∫⁻ f, acceptRate f ∂𝒟[F]) - ∫⁻ _f, κ ∂𝒟[F] := by
      apply tsub_le_tsub_left
      rw [lintegral_const]
      exact (mul_le_mul_of_nonneg_left (evalDist_apply_univ_le_one F)
        (show 0 ≤ κ from zero_le)).trans_eq (mul_one κ)
    _ ≤ ∫⁻ f, acceptRate f - κ ∂𝒟[F] :=
      lintegral_sub_le (fun _ => κ) (fun f => acceptRate f) Measurable.of_discrete
    _ ≤ ∫⁻ f, Pr{let z ← runFinder find f}[z.1.isSome] ∂𝒟[F] :=
      lintegral_mono h.success

/-- Uniform unconditional finder cost bounds average over a random acceptance function. -/
theorem IsTreeFinder.average_cost [Fintype R] [LinearOrder R]
    [∀ r, Fintype (C r)] [∀ r, DecidableEq (C r)]
    {k : R → ℕ} {nodeOk : (r : R) → (Fin (k r) → C r) → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option (VecTree C k))} {κ T : ℝ≥0∞}
    (h : IsTreeFinder k nodeOk find κ T) (F : ProbComp (((r : R) → C r) → Bool)) :
    expectedCalls (do let f ← F; runFinder find f) ≤ T := by
  let : MeasurableSpace (((r : R) → C r) → Bool) := ⊤
  rw [expectedCalls_bind]
  calc
    (∫⁻ f, expectedCalls (runFinder find f) ∂𝒟[F]) ≤ ∫⁻ _f, T ∂𝒟[F] :=
      lintegral_mono h.cost
    _ = T * 𝒟[F] Set.univ := lintegral_const T
    _ ≤ T * 1 := mul_le_mul_of_nonneg_left (evalDist_apply_univ_le_one F) zero_le
    _ = T := mul_one T

namespace ResetPolicy

variable {ι σ : Type} {spec : OracleSpec ι} {init : ProbComp σ}
  {impl : QueryImpl spec (StateT σ ProbComp)} (P : ResetPolicy init impl)

/-- A finder against frozen reruns has the joint output and counter law of that finder against
one random acceptance function, whose marginals are the honest acceptance decisions. -/
theorem finder_eager [Finite ((r : R) → C r)]
    (run : ((r : R) → C r) → OracleComp spec Bool) :
    ∃ F : ProbComp (((r : R) → C r) → Bool),
      (∀ c, ((fun f => f c) <$> F) =ᵈ
        (do (simulateQ impl (run c)).run' (← init))) ∧
      ∀ {β : Type} (find : OracleComp (unifSpec + accSpec C) β),
        P.attempt run find =ᵈ (do let f ← F; runFinder find f) := by
  exact P.rerun_eager run

/-- A black-box tree finder retains its average success guarantee and unconditional expected
complete-run bound when its acceptance oracle is implemented by frozen reruns. -/
theorem finder_bounds [Fintype R] [LinearOrder R]
    [∀ r, Fintype (C r)] [∀ r, DecidableEq (C r)]
    (run : ((r : R) → C r) → OracleComp spec Bool)
    {k : R → ℕ} {nodeOk : (r : R) → (Fin (k r) → C r) → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option (VecTree C k))} {κ T : ℝ≥0∞}
    (h : IsTreeFinder k nodeOk find κ T) :
    ∃ F : ProbComp (((r : R) → C r) → Bool),
      (∀ c, ((fun f => f c) <$> F) =ᵈ
        (do (simulateQ impl (run c)).run' (← init))) ∧
      (P.attempt run find =ᵈ (do let f ← F; runFinder find f)) ∧
      averageAcceptRate F - κ ≤ Pr{let z ← P.attempt run find}[z.1.isSome] ∧
      expectedCalls (P.attempt run find) ≤ T := by
  obtain ⟨F, hmarg, hlaw⟩ := P.finder_eager run
  refine ⟨F, hmarg, hlaw find, ?_, ?_⟩
  · rw [(hlaw find).prEvent_eq]
    exact h.average_success F
  · rw [expectedCalls_eq_of_evalDistEq (hlaw find)]
    exact h.average_cost F

end ResetPolicy
end Rewinding
