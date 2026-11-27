/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.FirstMoment
public import VCVio.EvalDist.Kernel
public import PolyFun.PFunctor.Free.Measure.StatefulExpectedCharge

/-!
# Expected charge of a stopped trial counter

A counted oracle charges one unit for a trial and zero for an idle operation.
The incoming charge is the probability that the next operation increments the counter.
The expected charges accumulated up to the caller's stopping decision give the expected
increase in its actual trial count.
-/

public section

namespace OracleComp.BernoulliMoment

open OracleSpec MeasureTheory PFunctor
open scoped ENNReal

variable {ι σ γ : Type} {spec : OracleSpec ι}

/-- Interpret a counted oracle operation through its joint answer-and-state kernel.
Its incoming charge is the chance that this call increments the trial count. -/
@[expose] noncomputable def trialCharge (so : QueryImpl spec (StateT σ ProbComp))
    (n : σ → ℕ) : OpSpec spec.toPFunctor (σ → ℝ≥0∞) :=
  letI : MeasurableSpace σ := ⊤
  letI : (t : ι) → MeasurableSpace (spec.Range t) := fun _ => ⊤
  OpSpec.statefulExpectedCharge
    (fun t => evalDistKernelOfDiscrete (so t).run)
    (fun t s => Pr{let z ← (so t).run s}[n z.2 = n s + 1])

private theorem trialCharge_step (so : QueryImpl spec (StateT σ ProbComp)) (n : σ → ℕ)
    (t : ι) (k : spec.Range t → σ → ℝ≥0∞) (s : σ) :
    trialCharge so n t k s = Pr{let z ← (so t).run s}[n z.2 = n s + 1] +
      ∑' z, Pr{let u ← (so t).run s}[u = z] * k z.1 z.2 := by
  let : MeasurableSpace σ := ⊤
  let : (t : ι) → MeasurableSpace (spec.Range t) := fun _ => ⊤
  -- The joint reply has finite support even when the answer and state types are uncountable.
  let m := (so t).run s
  have hs := support_finite m
  simp only [trialCharge, OpSpec.statefulExpectedCharge_apply, evalDistKernelOfDiscrete_apply]
  congr 1
  rw [lintegral_eq_tsum_mul_of_ae_mem_countable hs.countable
    (evalDist.ae_of_forall_mem_support m _ hs.measurableSet fun _ h => h)]
  apply tsum_congr
  intro z
  rw [← prEvent_eq_evalDist_singleton]

private theorem mean_next_trials {so : QueryImpl spec (StateT σ ProbComp)} {n v : σ → ℕ}
    {p : ℝ} {q : ℕ} (law : CountsTrials so n v p q) (t : ι) (s : σ) :
    (∑' z, Pr{let u ← (so t).run s}[u = z] * (n z.2 : ℝ≥0∞)) =
      n s + Pr{let z ← (so t).run s}[n z.2 = n s + 1] := by
  rcases law t s with idle | ⟨_, _, active⟩
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ (fun z hz => by rw [(idle z hz).1]; omega),
      add_zero]
    exact tsum_prEvent_mul_of_const_on_support _ fun z hz => by rw [(idle z hz).1]
  · rw [prEvent_eq_one_of_forall_mem_support _ _ (fun z hz => (active z hz).1)]
    exact tsum_prEvent_mul_of_const_on_support _ fun z hz => by simp [(active z hz).1]

/-- The expected final trial count is the initial count plus the caller's expected charge. -/
theorem CountsTrials.expected_trials_eq_charge {so : QueryImpl spec (StateT σ ProbComp)}
    {n v : σ → ℕ} {p : ℝ} {q : ℕ} (law : CountsTrials so n v p q)
    (body : OracleComp spec γ) (s : σ) :
    (∑' z, Pr{let u ← (simulateQ so body).run s}[u = z] * (n z.2 : ℝ≥0∞)) =
      n s + FreeM.wpFold (trialCharge so n) body.toFreeM (fun _ _ => 0) s := by
  induction body using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, tsum_prEvent_pure_mul,
      OracleComp.toFreeM, FreeM.wpFold_pure, add_zero]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_prEvent_bind_mul]
    change _ = n s + trialCharge so n t
      (fun y => FreeM.wpFold (trialCharge so n) (k y).toFreeM (fun _ _ => 0)) s
    simp_rw [ih, mul_add]
    rw [tsum_add, mean_next_trials law t s, trialCharge_step, add_assoc]

/-- At zero initial counts the expected successes are the rate times the expected charge. -/
theorem CountsTrials.expected_successes_eq_charge {so : QueryImpl spec (StateT σ ProbComp)}
    {n v : σ → ℕ} {p : ℝ} {q : ℕ} (law : CountsTrials so n v p q)
    (body : OracleComp spec γ) (s : σ) (trials : n s = 0) (successes : v s = 0) :
    (∑' z, Pr{let u ← (simulateQ so body).run s}[u = z] * (v z.2 : ℝ≥0∞)) =
      ENNReal.ofReal p * FreeM.wpFold (trialCharge so n) body.toFreeM (fun _ _ => 0) s := by
  rw [expected_successes law body s trials successes, law.expected_trials_eq_charge, trials]
  simp

end OracleComp.BernoulliMoment
