/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.AdaptiveMoment
public import VCVio.OracleComp.SimSemantics.StateT.Compensated
import all VCVio.OracleComp.QueryTracking.CountingOracle.AdaptiveMoment

/-!
# First moment of an adaptive Bernoulli count

The caller may stop after seeing any reply.
A counted trial has the declared success probability conditional on the current state.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace OracleComp.BernoulliMoment

variable {ι σ γ : Type} {spec : OracleSpec ι}

private noncomputable abbrev avg {α : Type} (m : ProbComp α) (f : α → ℝ≥0∞) :=
  ∑' z, Pr{let u ← m}[u = z] * f z

private theorem avg_scale {α : Type} (m : ProbComp α) (p : ℝ≥0∞) (f : α → ℝ≥0∞) :
    avg m (fun z => p * f z) = p * avg m f := by
  simp only [avg, ← ENNReal.tsum_mul_left, mul_left_comm]

private theorem step_mean {so : QueryImpl spec (StateT σ ProbComp)} {n v : σ → Nat}
    {p : ℝ} {q : Nat} (law : CountsTrials so n v p q) (t : ι) (s : σ) :
    let m := (so t).run s
    avg m (fun z => (v z.2 : ℝ≥0∞)) + ENNReal.ofReal p * n s =
      v s + avg m (fun z => ENNReal.ofReal p * n z.2) := by
  classical
  intro m
  rcases law t s with free | ⟨_, prob, step⟩
  · simp only [avg]
    rw [tsum_prEvent_mul_of_const_on_support m (fun z hz => congrArg (Nat.cast (R := ℝ≥0∞))
        (free z hz).2),
      tsum_prEvent_mul_of_const_on_support m (fun z hz =>
        congrArg (fun u : Nat => ENNReal.ofReal p * u) (free z hz).1)]
  · let hit := fun z : spec.Range t × σ => v z.2 = v s + 1
    have total : Pr{let z ← m}[hit z] + Pr{let z ← m}[¬hit z] = 1 := by
      simpa using prEvent_add_prEvent_not_eq_prEvent_true m hit
    have costs : avg m (fun z => ENNReal.ofReal p * n z.2) =
        ENNReal.ofReal p * (n s + 1 : Nat) :=
      tsum_prEvent_mul_of_const_on_support m fun z hz => by rw [(step z hz).1]
    have hits := mean_two m (fun z => (v z.2 : ℝ≥0∞)) hit (v s + 1) (v s) (by
      intro z hz
      by_cases h : hit z
      · simp only [h, ite_true]
        exact_mod_cast h
      · simp only [h, ite_false]
        exact_mod_cast (step z hz).2.resolve_left h)
    rw [costs, avg, hits]
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    calc
      _ = (Pr{let z ← m}[hit z] + Pr{let z ← m}[¬hit z]) * v s +
          Pr{let z ← m}[hit z] + ENNReal.ofReal p * n s := by rw [add_mul]; ac_rfl
      _ = _ := by
        rw [total, one_mul, show Pr{let z ← m}[hit z] = ENNReal.ofReal p from prob]
        ac_rfl

/-- With zero initial counts the expected successes equal the rate times the expected trials.
Ignored queries and all adaptive stopping decisions are retained. -/
theorem expected_successes {so : QueryImpl spec (StateT σ ProbComp)} {n v : σ → Nat}
    {p : ℝ} {q : Nat} (law : CountsTrials so n v p q) (body : OracleComp spec γ)
    (s : σ) (trials : n s = 0) (successes : v s = 0) :
    let m := (simulateQ so body).run s
    (∑' z, Pr{let u ← m}[u = z] * (v z.2 : ℝ≥0∞)) =
      ENNReal.ofReal p * ∑' z, Pr{let u ← m}[u = z] * (n z.2 : ℝ≥0∞) := by
  intro m
  let weight := fun b : σ => ENNReal.ofReal p * n b
  let value := fun b : σ => (v b : ℝ≥0∞)
  have inv : so.PreservesInv (fun _ => True) := fun _ _ _ _ _ => trivial
  have upper := QueryImpl.run_compensated so _ inv value weight
    (fun _ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _))
    (fun t b _ => (step_mean law t b).le) body s trivial
  have lower := QueryImpl.run_compensated so _ inv weight value
    (fun _ _ => ENNReal.natCast_ne_top _)
    (fun t b _ => by simpa only [add_comm] using (step_mean law t b).ge) body s trivial
  have eq : avg m (fun z => (v z.2 : ℝ≥0∞)) = avg m (fun z => ENNReal.ofReal p * n z.2) := by
    apply le_antisymm
    · simpa only [value, weight, trials, successes, Nat.cast_zero, mul_zero, add_zero, zero_add]
        using upper
    · simpa only [value, weight, trials, successes, Nat.cast_zero, mul_zero, add_zero, zero_add]
        using lower
  exact eq.trans (avg_scale m _ _)

end OracleComp.BernoulliMoment
