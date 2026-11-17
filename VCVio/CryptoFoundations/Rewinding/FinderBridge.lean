/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Finder
public import VCVio.CryptoFoundations.Rewinding.Eager

/-!
# Finders against frozen reruns

A frozen prover determines one random Boolean acceptance function on complete challenge vectors.
The eager representation preserves the finder's joint output and complete-run counter, so uniform
success and unconditional cost bounds transfer by averaging over this function. Each entry of the
function has the honest acceptance distribution, so its average acceptance rate is the honest
acceptance probability averaged over complete challenge vectors.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Rewinding

variable {R : Type} {C : R → Type}

/-- Average acceptance rate of a randomly chosen Boolean acceptance function. -/
@[expose] noncomputable def averageAcceptRate [Fintype R] [DecidableEq R]
    [∀ r, Fintype (C r)]
    (F : ProbComp (((r : R) → C r) → Bool)) : ℝ≥0∞ :=
  letI : MeasurableSpace (((r : R) → C r) → Bool) := ⊤
  ∫⁻ f, acceptRate f ∂𝒟[F]

/-- The average acceptance rate of a random acceptance function is the average, over complete
challenge vectors, of the probability that its entry at that vector accepts. -/
theorem averageAcceptRate_eq_of_marginals [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    {F : ProbComp (((r : R) → C r) → Bool)} {g : ((r : R) → C r) → ProbComp Bool}
    (hg : ∀ c, ((fun f => f c) <$> F) =ᵈ g c) :
    averageAcceptRate F =
      (∑ c, Pr{let b ← g c}[b = true]) / Fintype.card ((r : R) → C r) := by
  let : MeasurableSpace (((r : R) → C r) → Bool) := ⊤
  have hc : ∀ c, Pr{let b ← g c}[b = true] =
      ∫⁻ f, (if f c = true then 1 else 0) ∂𝒟[F] := by
    intro c
    rw [← (hg c).prEvent_eq, prEvent_map]
    simpa only [bind_pure, prEvent_pure] using
      prEvent_bind_eq_lintegral_of_discrete F (pure : _ → ProbComp _) (fun f => f c = true)
  simp only [hc, averageAcceptRate, acceptRate, div_eq_mul_inv]
  rw [← lintegral_finsetSum _ (fun _ _ => Measurable.of_discrete),
    ← lintegral_mul_const _ Measurable.of_discrete]
  simp only [Finset.sum_boole]

/-- Uniform affine finder success bounds average over a randomly chosen acceptance function. -/
theorem IsFinder.average_success [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)] {Out : Type}
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) (F : ProbComp (((r : R) → C r) → Bool)) :
    averageAcceptRate F ≤
      κ + (1 - κ) * Pr{let z ← (do let f ← F; runFinder find f)}[z.1.isSome] := by
  let : MeasurableSpace (((r : R) → C r) → Bool) := ⊤
  rw [averageAcceptRate, prEvent_bind_eq_lintegral_of_discrete]
  calc
    (∫⁻ f, acceptRate f ∂𝒟[F]) ≤
        ∫⁻ f, κ + (1 - κ) * Pr{let z ← runFinder find f}[z.1.isSome] ∂𝒟[F] :=
      lintegral_mono h.success
    _ = κ * 𝒟[F] Set.univ +
        (1 - κ) * ∫⁻ f, Pr{let z ← runFinder find f}[z.1.isSome] ∂𝒟[F] := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        lintegral_const_mul _ Measurable.of_discrete]
    _ ≤ _ := by
      gcongr
      exact mul_le_of_le_one_right zero_le (evalDist_apply_univ_le_one F)

/-- A finder against a random acceptance function succeeds with probability at least the
average acceptance rate minus its error. -/
theorem IsFinder.averageAcceptRate_sub_le [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) (F : ProbComp (((r : R) → C r) → Bool)) :
    averageAcceptRate F - κ ≤
      Pr{let z ← (do let f ← F; runFinder find f)}[z.1.isSome] :=
  tsub_le_iff_left.mpr ((h.average_success F).trans
    (add_le_add le_rfl (mul_le_of_le_one_left zero_le tsub_le_self)))

/-- Uniform unconditional finder cost bounds average over a random acceptance function. -/
theorem IsFinder.average_cost [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)] {Out : Type}
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) (F : ProbComp (((r : R) → C r) → Bool)) :
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
the eager table of acceptance decisions, whose entries have the honest acceptance distribution
(`ResetPolicy.eagerTable_marginal`). -/
theorem attempt_eq_runFinder_eagerTable [Finite ((r : R) → C r)]
    (run : ((r : R) → C r) → OracleComp spec Bool) {β : Type}
    (find : OracleComp (unifSpec + accSpec C) β) :
    P.attempt run find =ᵈ (do let f ← P.eagerTable run; runFinder find f) :=
  P.attempt_eagerTable run find

/-- The average acceptance rate of the eager table is the honest acceptance probability of a
complete run, averaged over complete challenge vectors. -/
theorem averageAcceptRate_eagerTable [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    (run : ((r : R) → C r) → OracleComp spec Bool) :
    averageAcceptRate (P.eagerTable run) =
      (∑ c, Pr{let b ← (do (simulateQ impl (run c)).run' (← init))}[b = true]) /
        Fintype.card ((r : R) → C r) :=
  averageAcceptRate_eq_of_marginals (P.eagerTable_marginal run)

/-- A black-box finder retains its affine success guarantee and unconditional expected
complete-run bound when its acceptance oracle is implemented by frozen reruns. The acceptance
rate is averaged over the eager table of acceptance decisions. -/
theorem finder_bounds [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    (run : ((r : R) → C r) → OracleComp spec Bool) {Out : Type}
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) :
    averageAcceptRate (P.eagerTable run) ≤
        κ + (1 - κ) * Pr{let z ← P.attempt run find}[z.1.isSome] ∧
      expectedCalls (P.attempt run find) ≤ T := by
  have hlaw := P.attempt_eq_runFinder_eagerTable run find
  refine ⟨?_, ?_⟩
  · rw [hlaw.prEvent_eq]
    exact h.average_success _
  · rw [expectedCalls_eq_of_evalDistEq hlaw]
    exact h.average_cost _

/-- `ResetPolicy.finder_bounds` with the subtractive success bound: against frozen reruns, the
finder succeeds with probability at least the average acceptance rate of the eager table minus
its error. -/
theorem finder_bounds_sub [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    (run : ((r : R) → C r) → OracleComp spec Bool) {Out : Type}
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) :
    averageAcceptRate (P.eagerTable run) - κ ≤ Pr{let z ← P.attempt run find}[z.1.isSome] ∧
      expectedCalls (P.attempt run find) ≤ T := by
  refine ⟨?_, (P.finder_bounds run h).2⟩
  rw [(P.attempt_eq_runFinder_eagerTable run find).prEvent_eq]
  exact h.averageAcceptRate_sub_le _

/-- `ResetPolicy.finder_bounds` with the honest acceptance probability: the probability that a
complete run accepts, averaged uniformly over complete challenge vectors, is at most the error
plus its complement times the success probability against frozen reruns. -/
theorem finder_bounds_honest [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    (run : ((r : R) → C r) → OracleComp spec Bool) {Out : Type}
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) :
    (∑ c, Pr{let b ← (do (simulateQ impl (run c)).run' (← init))}[b = true]) /
          Fintype.card ((r : R) → C r) ≤
        κ + (1 - κ) * Pr{let z ← P.attempt run find}[z.1.isSome] ∧
      expectedCalls (P.attempt run find) ≤ T := by
  rw [← P.averageAcceptRate_eagerTable run]
  exact P.finder_bounds run h

end ResetPolicy
end Rewinding
