/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.ExpectedQueryCount
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The budgeted expected-potential bound on small instances

* **A lottery.**  Each query to a coin oracle draws a uniform `Bool` and sets a sticky flag when
  the coin is `true`.  The potential `if flag then 1 else n / 2` is spent at one budget level per
  query, so a computation making at most `n` queries ends with the flag set with probability at
  most `n / 2`, whatever the computation does with the answers.
* **The additive resource bound.**  A resource on the state that grows by at most one on a
  charged step and not at all on an uncharged one has expected final value at most its initial
  value plus the query budget.  It is derived once from `OracleComp.lintegral_run_le_of_budget`
  with the potential `resource s + n`, and once from the two expected-count lemmas.
* **The step inequality of the hit potential.**  `n ^ u / |Y| ^ u` is spent at one level per draw
  when a draw clears one of `u` pending values with probability at most `u / |Y|`; the arithmetic
  is Mathlib's `pow_add_mul_le_add_pow`, at `ℕ` and at `ℝ≥0∞`.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace BudgetedPotentialTest

/-! ## A lottery -/

/-- A coin oracle: each query draws a uniform `Bool`, returns it, and sets the flag if it is
`true`. -/
def coinImpl : QueryImpl (Unit →ₒ Bool) (StateT Bool ProbComp) := fun _ =>
  StateT.mk fun s => (fun b => (b, s || b)) <$> ($ᵗ Bool)

/-- The lottery potential at remaining budget `n`: `1` once the flag is set, `n / 2` before. -/
noncomputable def coinPotential (n : ℕ) (s : Bool) : ℝ≥0∞ :=
  if s then 1 else n * 2⁻¹

theorem coinPotential_step (t : Unit) (s : Bool) (n : ℕ) :
    ∫⁻ r, r ∂𝒟[(fun z => coinPotential n z.2) <$> (coinImpl t).run s] ≤
      coinPotential (n + if (fun _ : Unit => True) t then 1 else 0) s := by
  simp only [↓reduceIte]
  let _ : MeasurableSpace (Bool × Bool) := ⊤
  let _ : MeasurableSpace Bool := ⊤
  cases s with
  | true =>
    rw [show (coinImpl t).run true = (fun b => (b, true || b)) <$> ($ᵗ Bool) from rfl,
      Functor.map_map]
    exact lintegral_id_evalDist_map_le_of_le _ fun b => by simp [coinPotential]
  | false =>
    rw [show (coinImpl t).run false = (fun b => (b, b)) <$> ($ᵗ Bool) from rfl,
      Functor.map_map, lintegral_id_evalDist_map, lintegral_fintype]
    simp only [Fintype.univ_bool, Finset.mem_singleton,
      Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton,
      SampleableType.evalDist_uniformSample_singleton, Fintype.card_bool, coinPotential,
      ↓reduceIte, Bool.false_eq_true, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, one_mul]
    rw [add_mul, one_mul, add_comm]
    gcongr
    exact mul_le_of_le_one_right' (ENNReal.inv_le_one.mpr one_le_two)

/-- A computation making at most `n` coin queries sets the flag with probability at most
`n / 2`. -/
theorem prEvent_coin_le {α : Type} (oa : OracleComp (Unit →ₒ Bool) α) (n : ℕ)
    (hq : oa.IsQueryBoundP (fun _ => True) n) :
    Pr{let z ← (simulateQ coinImpl oa).run false}[z.2 = true] ≤ n * 2⁻¹ := by
  simpa [coinPotential] using prEvent_run_le_of_budget coinImpl (fun _ => True) coinPotential
    (fun s a b hab => by
      cases s
      · simpa [coinPotential] using mul_le_mul_left (Nat.cast_le.mpr hab) _
      · simp [coinPotential])
    coinPotential_step (fun z => z.2 = true) (fun z hz => by simp [coinPotential, hz]) oa n hq
    false

/-! ## The additive resource bound -/

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- The additive resource bound, from the budgeted potential `resource s + n`. -/
theorem lintegral_resource_le_add_of_budget (so : QueryImpl spec (StateT σ ProbComp))
    (charged : spec.Domain → Prop) [DecidablePred charged] (resource : σ → ℝ≥0∞)
    (hstep : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s),
      resource z.2 ≤ resource s + if charged t then 1 else 0)
    (oa : OracleComp spec α) (n : ℕ) (hq : oa.IsQueryBoundP charged n) (s : σ) :
    ∫⁻ r, r ∂𝒟[(fun z => resource z.2) <$> (simulateQ so oa).run s] ≤ resource s + n := by
  have key := lintegral_run_le_of_budget so charged (fun n s => resource s + n)
    (fun s a b hab => by dsimp only; gcongr)
    (fun t s n => by
      rw [lintegral_id_evalDist_map_add]
      calc (∫⁻ r, r ∂𝒟[(fun z => resource z.2) <$> (so t).run s]) +
            ∫⁻ r, r ∂𝒟[(fun _ => (n : ℝ≥0∞)) <$> (so t).run s]
          ≤ (resource s + if charged t then 1 else 0) + n :=
            add_le_add (lintegral_id_evalDist_map_le_of_le_of_mem_support _ (hstep t s))
              (lintegral_id_evalDist_map_le_of_le _ fun _ => le_rfl)
        _ = resource s + ((n + if charged t then 1 else 0 : ℕ) : ℝ≥0∞) := by
          split_ifs <;> push_cast <;> ring)
    oa n hq s
  simpa using key

/-- The same bound from the landed expected-count lemmas. -/
theorem lintegral_resource_le_add_of_expectedCount (so : QueryImpl spec (StateT σ ProbComp))
    (charged : spec.Domain → Prop) [DecidablePred charged] (resource : σ → ℝ≥0∞)
    (hstep : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s),
      resource z.2 ≤ resource s + if charged t then 1 else 0)
    (oa : OracleComp spec α) (n : ℕ) (hq : oa.IsQueryBoundP charged n) (s : σ) :
    ∫⁻ r, r ∂𝒟[(fun z => resource z.2) <$> (simulateQ so oa).run s] ≤ resource s + n :=
  (lintegral_resource_le_add_expectedSimulatedQueryCount so charged resource hstep oa s).trans
    (add_le_add le_rfl (expectedSimulatedQueryCount_le_of_isQueryBoundP so charged oa s n hq))

/-! ## The step inequality of the hit potential -/

example (n u : ℕ) : n ^ (u + 1) + (u + 1) * n ^ u ≤ (n + 1) ^ (u + 1) := by
  simpa using pow_add_mul_le_add_pow (a := n) (b := 1) (Nat.zero_le _) (Nat.zero_le _) (u + 1)

example (x : ℝ≥0∞) (u : ℕ) : x ^ (u + 1) + (u + 1) * x ^ u ≤ (x + 1) ^ (u + 1) := by
  simpa using pow_add_mul_le_add_pow (a := x) (b := 1) zero_le zero_le (u + 1)

end BudgetedPotentialTest
