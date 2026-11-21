/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.BernoulliMoment
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.EvalDist.ProbabilityBounds

/-!
# Adaptive use of a bounded Bernoulli trial counter

A caller may stop after observing any reply and may interleave operations that leave the counters
alone. An active step spends one trial and increments the success count with a fixed probability.
The expected quadratic reserve plus the credit for unspent trials stays constant.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace OracleComp.BernoulliMoment

/-- The expected increase of the quadratic reserve on one counted trial. -/
@[expose] noncomputable def price (p α β : ℝ) : ℝ := α + β * ((1 - p) / p)

/-- Credit for unspent trials pays for future increases in the reserve. -/
@[expose] noncomputable def balance (p α β : ℝ) (q v n : ℕ) : ℝ :=
  reserve p α β v n + price p α β * (q - n : ℕ)

private theorem price_nonneg {p α β : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (ha : 0 ≤ α) (hb : 0 ≤ β) : 0 ≤ price p α β :=
  add_nonneg ha (mul_nonneg hb (div_nonneg (sub_nonneg.mpr hp1) hp.le))

private theorem balance_nonneg {p α β : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (ha : 0 ≤ α) (hb : 0 ≤ β) (q v n : ℕ) : 0 ≤ balance p α β q v n :=
  add_nonneg (nonneg ha hb n.cast_nonneg) (mul_nonneg (price_nonneg hp hp1 ha hb) (by positivity))

/-- The balance on an active trial is a martingale, including the last allowed trial. -/
theorem step_balance {p α β : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ α) (hb : 0 ≤ β)
    {q n : ℕ} (room : n < q) (v : ℕ) :
    ENNReal.ofReal p * ENNReal.ofReal (balance p α β q (v + 1) (n + 1)) +
      ENNReal.ofReal (1 - p) * ENNReal.ofReal (balance p α β q v (n + 1)) =
      ENNReal.ofReal (balance p α β q v n) := by
  rw [← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_mul (sub_nonneg.mpr hp1),
    ← ENNReal.ofReal_add (mul_nonneg hp.le (balance_nonneg hp hp1 ha hb _ _ _))
      (mul_nonneg (sub_nonneg.mpr hp1) (balance_nonneg hp hp1 ha hb _ _ _))]
  congr 1
  have left : ((q - n : ℕ) : ℝ) = ((q - (n + 1) : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show q - n = q - (n + 1) + 1 by omega)
  simp only [balance, price, Nat.cast_add, Nat.cast_one, left]
  linear_combination step hp.ne' α β v n

private theorem mean_two {γ : Type} (m : ProbComp γ) (f : γ → ℝ≥0∞) (hit : γ → Prop)
    [DecidablePred hit] (yes no : ℝ≥0∞)
    (two : ∀ z ∈ support m, f z = if hit z then yes else no) :
    (∑' z, Pr{let u ← m}[u = z] * f z) =
      Pr{let u ← m}[hit u] * yes + Pr{let u ← m}[¬hit u] * no := by
  rw [prEvent_eq_tsum_ite m hit, prEvent_eq_tsum_ite m (fun u => ¬hit u),
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← tsum_add]
  refine tsum_congr fun z => ?_
  by_cases ok : z ∈ support m
  · rw [two z ok]
    by_cases h : hit z <;> simp [h]
  · rw [prEvent_eq_zero_of_not_mem_support m ok]
    simp

variable {ι σ γ : Type} {spec : OracleSpec ι}

/-- Each operation leaves both counters alone or spends one fresh trial at the stated rate. -/
@[expose] def CountsTrials (so : QueryImpl spec (StateT σ ProbComp)) (trials successes : σ → ℕ)
    (p : ℝ) (q : ℕ) : Prop :=
  ∀ t s,
    (∀ z ∈ support ((so t).run s), trials z.2 = trials s ∧ successes z.2 = successes s) ∨
    (trials s < q ∧
      Pr{let z ← (so t).run s}[successes z.2 = successes s + 1] = ENNReal.ofReal p ∧
      ∀ z ∈ support ((so t).run s), trials z.2 = trials s + 1 ∧
        (successes z.2 = successes s + 1 ∨ successes z.2 = successes s))

/-- Every returned path respects the trial cap, regardless of when the caller stops. -/
theorem CountsTrials.trials_le {so : QueryImpl spec (StateT σ ProbComp)} {trials successes : σ → ℕ}
    {p : ℝ} {q : ℕ} (h : CountsTrials so trials successes p q) (oa : OracleComp spec γ)
    (s : σ) (start : trials s ≤ q) :
    ∀ z ∈ support ((simulateQ so oa).run s), trials z.2 ≤ q := by
  apply simulateQ_run_preservesInv so (fun st => trials st ≤ q) _ oa s start
  intro t st le z hz
  rcases h t st with idle | ⟨room, _, active⟩
  · simpa only [(idle z hz).1] using le
  · rw [(active z hz).1]
    exact Nat.succ_le_of_lt room

/-- An adaptive run preserves the mean balance if each of its operations either leaves the counts
fixed or takes one Bernoulli trial before the budget expires. -/
theorem run_balance (so : QueryImpl spec (StateT σ ProbComp)) (trials successes : σ → ℕ)
    (p α β : ℝ) (q : ℕ) (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ α) (hb : 0 ≤ β)
    (localLaw : CountsTrials so trials successes p q)
    (oa : OracleComp spec γ) (s : σ) :
    (∑' z, Pr{let u ← (simulateQ so oa).run s}[u = z] *
      ENNReal.ofReal (balance p α β q (successes z.2) (trials z.2))) =
      ENNReal.ofReal (balance p α β q (successes s) (trials s)) := by
  classical
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_prEvent_bind_mul]
    simp_rw [ih]
    rcases localLaw t s with idle | ⟨room, rate, counts⟩
    · let b := ENNReal.ofReal (balance p α β q (successes s) (trials s))
      have h := mean_two ((so t).run s)
          (fun z => ENNReal.ofReal (balance p α β q (successes z.2) (trials z.2)))
          (fun _ => True) b b (fun z hz => by
        simp only [ite_self, b, (idle z hz).1, (idle z hz).2])
      simpa using h
    · let hit (z : spec.Range t × σ) := successes z.2 = successes s + 1
      have miss : Pr{let z ← (so t).run s}[¬hit z] = ENNReal.ofReal (1 - p) := by
        rw [prEvent_not_eq_one_sub, show Pr{let z ← (so t).run s}[hit z] = _ from rate,
          ENNReal.ofReal_sub _ hp.le]
        simp
      rw [mean_two ((so t).run s) _ hit
        (ENNReal.ofReal (balance p α β q (successes s + 1) (trials s + 1)))
        (ENNReal.ofReal (balance p α β q (successes s) (trials s + 1))) (fun z hz => by
        obtain ⟨n, cases⟩ := counts z hz
        by_cases h : hit z
        · simpa only [h, ite_true, n] using congrArg
            (fun v => ENNReal.ofReal (balance p α β q v (trials s + 1))) h
        · simp only [h, ite_false, n, cases.resolve_left h]),
        show Pr{let z ← (so t).run s}[hit z] = _ from rate, miss]
      exact step_balance hp hp1 ha hb room (successes s)

/-- The expected reserve equals the price times the expected number of trials actually taken.
This retains savings on paths that stop early or spend their budget on other operations. -/
theorem run_reserve (so : QueryImpl spec (StateT σ ProbComp)) (trials successes : σ → ℕ)
    (p α β : ℝ) (q : ℕ) (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ α) (hb : 0 ≤ β)
    (localLaw : CountsTrials so trials successes p q) (oa : OracleComp spec γ) (s : σ)
    (hn : trials s = 0) (hv : successes s = 0) :
    (∑' z, Pr{let u ← (simulateQ so oa).run s}[u = z] *
      ENNReal.ofReal (reserve p α β (successes z.2) (trials z.2))) =
      ENNReal.ofReal (price p α β) * ∑' z, Pr{let u ← (simulateQ so oa).run s}[u = z] *
        (trials z.2 : ℝ≥0∞) := by
  let m := (simulateQ so oa).run s
  let k := ENNReal.ofReal (price p α β)
  have cap := localLaw.trials_le oa s (by simp [hn])
  have bank := run_balance so trials successes p α β q hp hp1 ha hb localLaw oa s
  change (∑' z, Pr{let u ← m}[u = z] * _) = _ at bank
  rw [hv, hn] at bank
  have start : ENNReal.ofReal (balance p α β q 0 0) = k * q := by
    simp [balance, k, ENNReal.ofReal_mul (price_nonneg hp hp1 ha hb)]
  rw [start] at bank
  have row (z : γ × σ) (hz : z ∈ support m) :
      ENNReal.ofReal (reserve p α β (successes z.2) (trials z.2)) + k * q =
        ENNReal.ofReal (balance p α β q (successes z.2) (trials z.2)) + k * trials z.2 := by
    rw [balance, ENNReal.ofReal_add (nonneg ha hb (trials z.2).cast_nonneg)
      (mul_nonneg (price_nonneg hp hp1 ha hb) (by positivity)),
      ENNReal.ofReal_mul (price_nonneg hp hp1 ha hb), ENNReal.ofReal_natCast]
    rw [add_assoc, ← mul_add, ← Nat.cast_add, Nat.sub_add_cancel (cap z hz)]
  have eqrow (z : γ × σ) :
      Pr{let u ← m}[u = z] * (ENNReal.ofReal (reserve p α β (successes z.2) (trials z.2)) + k * q) =
      Pr{let u ← m}[u = z] * (ENNReal.ofReal (balance p α β q (successes z.2) (trials z.2)) +
        k * trials z.2) := by
    by_cases hz : z ∈ support m
    · rw [row z hz]
    · rw [prEvent_eq_zero_of_not_mem_support m hz, zero_mul, zero_mul]
  have sum := tsum_congr (L := SummationFilter.unconditional _) eqrow
  simp_rw [mul_add] at sum
  rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul] at sum
  change (∑' z, Pr{let u ← m}[u = z] * ENNReal.ofReal (balance p α β q _ _)) = k * q at bank
  rw [bank, add_comm (k * q)] at sum
  apply (ENNReal.add_left_inj (a := k * q) (by finiteness)).1
  convert sum using 2
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  ring

end OracleComp.BernoulliMoment
