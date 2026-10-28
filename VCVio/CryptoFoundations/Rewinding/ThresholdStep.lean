/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.ThresholdEager
public import VCVio.CryptoFoundations.Rewinding.Finder
public import VCVio.OracleComp.EvalDist.List

/-!
# A single threshold step with probabilistic children

Independent child computations contribute an acceptance witness and a complete-run cost.
Sampling their finite table in advance separates the combinatorial threshold bound from the
children's individual success probabilities and expected costs.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Rewinding

/-! ## Deterministic child tables -/

variable {W : Type}

/-- The success event of a threshold attempt on a stored child table has the same probability
as the Boolean threshold finder observing which table entries contain witnesses. -/
theorem prEvent_thresholdChildren_table_eq (r : ℕ) (z : Option W × ℕ)
    (zs : List (Option W × ℕ)) (count : ℕ) :
    Pr{let t ← (thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild
      (r + 1) (z :: zs)).run count}[t.1.isSome] =
    Pr{let t ← (simulateQ (coins (S := ℕ) + counted (fun z : Option W × ℕ => z.1.isSome))
      (thresholdRound (r + 1) (z :: zs))).run 0}[t.1.isSome] := by
  rw [thresholdChildren_table, thresholdRound_counted]
  apply prEvent_bind_congr
  intro i
  cases hy : ((z :: zs)[(i : ℕ)]).1 with
  | none => simp [hy]
  | some w =>
      simp only [hy, Option.isSome_some, ite_true, prEvent_map]
      apply prEvent_congr
      intro d
      have hlen : (d.filterMap Prod.fst).length =
          (d.filter (fun z : Option W × ℕ => z.1.isSome)).length := by
        rw [List.length_filterMap_eq_countP, List.countP_eq_length_filter]
      rw [hlen]
      split <;> simp_all

/-- A fixed child table succeeds with its fraction of successful entries if it contains at
least the requested number of successes, and otherwise succeeds with probability zero. -/
theorem prEvent_thresholdChildren_table (r : ℕ) (z : Option W × ℕ)
    (zs : List (Option W × ℕ)) (count : ℕ) :
    Pr{let t ← (thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild
      (r + 1) (z :: zs)).run count}[t.1.isSome] =
      if r + 1 ≤ (z :: zs).countP (fun z => z.1.isSome) then
        ((z :: zs).countP (fun z => z.1.isSome) : ℝ≥0∞) / (zs.length + 1) else 0 := by
  rw [prEvent_thresholdChildren_table_eq, prEvent_thresholdRound]

/-- The affine threshold success estimate for a deterministic child table. -/
theorem thresholdChildren_table_success_scaled (r : ℕ) (z : Option W × ℕ)
    (zs : List (Option W × ℕ)) (count : ℕ) (hr : r ≤ zs.length) :
    ((z :: zs).countP (fun z => z.1.isSome) : ℝ≥0∞) / (zs.length + 1) ≤
      (r : ℝ≥0∞) / (zs.length + 1) +
        (1 - (r : ℝ≥0∞) / (zs.length + 1)) *
          Pr{let t ← (thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild
            (r + 1) (z :: zs)).run count}[t.1.isSome] := by
  rw [prEvent_thresholdChildren_table_eq]
  have h := thresholdRound_success_scaled (fun z : Option W × ℕ => z.1.isSome) r z zs hr
  simpa only [add_comm] using tsub_le_iff_right.mp h

/-- The affine threshold estimate for an arbitrary nonempty child table and feasible positive
threshold. -/
theorem thresholdChildren_table_success_scaled_all (k : ℕ)
    (pool : List (Option W × ℕ)) (count : ℕ) (hkpos : 1 ≤ k) (hkle : k ≤ pool.length) :
    (pool.countP (fun z => z.1.isSome) : ℝ≥0∞) / pool.length ≤
      ((k - 1 : ℕ) : ℝ≥0∞) / pool.length +
        (1 - ((k - 1 : ℕ) : ℝ≥0∞) / pool.length) *
          Pr{let t ← (thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild
            k pool).run count}[t.1.isSome] := by
  cases k with
  | zero => omega
  | succ r =>
      cases pool with
      | nil => simp at hkle
      | cons z zs =>
          have hr : r ≤ zs.length := by simpa using hkle
          simpa using thresholdChildren_table_success_scaled r z zs count hr

/-- A deterministic child table costs at most the threshold times the average entry cost,
without conditioning on whether a full set of successful children was found. -/
theorem expectedCalls_thresholdChildren_table {W : Type} (k : ℕ)
    (pool : List (Option W × ℕ)) :
    expectedCalls
      ((thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n)) tableChild k pool).run 0) ≤
        (k : ℝ≥0∞) * ((pool.map Prod.snd).sum : ℝ≥0∞) / pool.length := by
  let : MeasurableSpace (Option (List W)) := ⊤
  let : MeasurableSpace (List (Option W × ℕ)) := ⊤
  rw [expectedCalls_eq_lintegral, thresholdChildren_table_draws,
    lintegral_evalDist_map _
      (g := fun z : Option (List W) × ℕ => (z.2 : ℝ≥0∞))
      Measurable.of_discrete (by fun_prop)]
  simp only [Nat.zero_add]
  have hw := ProbComp.lintegral_sum_nat_thresholdDraws_le
    (fun z : Option W × ℕ => z.1.isSome) Prod.snd k pool
  rw [lintegral_evalDist_map_of_discrete] at hw
  exact hw

/-! ## Independent probabilistic children -/

/-- A threshold step with independent probabilistic children costs at most the threshold times
the average unconditional child cost. -/
theorem expectedCalls_thresholdChildren {C W : Type}
    (child : C → ProbComp (Option W × ℕ)) (k : ℕ) (pool : List C) :
    expectedCalls
      ((thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n))
        (chargedChild child) k pool).run 0) ≤
      (k : ℝ≥0∞) * (pool.map fun c => expectedCalls (child c)).sum / pool.length := by
  let : MeasurableSpace (Option W × ℕ) := ⊤
  let : MeasurableSpace (List (Option W × ℕ)) := ⊤
  rw [expectedCalls_eq_of_evalDistEq (thresholdChildren_eager ProbComp.uniformFin child k pool 0),
    expectedCalls_bind]
  calc
    (∫⁻ table, expectedCalls
        ((thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n))
          tableChild k table).run 0) ∂𝒟[pool.mapM child]) ≤
        ∫⁻ table, (k : ℝ≥0∞) * ((table.map Prod.snd).sum : ℝ≥0∞) / pool.length
          ∂𝒟[pool.mapM child] := by
      apply lintegral_mono_ae
      apply evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
      intro table ht
      rw [← List.length_of_mem_support_mapM child pool table ht]
      exact expectedCalls_thresholdChildren_table k table
    _ = (k : ℝ≥0∞) * (pool.map fun c => expectedCalls (child c)).sum / pool.length := by
      simp only [div_eq_mul_inv]
      rw [lintegral_mul_const _ Measurable.of_discrete,
        lintegral_const_mul _ Measurable.of_discrete]
      congr 2
      have hs := lintegral_mapM_sum child (fun z => (z.2 : ℝ≥0∞)) pool
      have hsum : ∀ table : List (Option W × ℕ),
          ((table.map Prod.snd).sum : ℝ≥0∞) =
            (table.map fun z => (z.2 : ℝ≥0∞)).sum := by
        intro table
        induction table with
        | nil => simp
        | cons z zs ih => simp [ih]
      simp_rw [hsum]
      rw [hs]
      congr 1
      apply List.map_congr_left
      intro c hc
      rw [expectedCalls_eq_lintegral_counter,
        lintegral_evalDist_map_of_discrete]

/-- The average child success rate is at most the threshold error plus the complement of that
error times the success probability of the complete threshold step. -/
theorem thresholdChildren_success_scaled {C W : Type}
    (child : C → ProbComp (Option W × ℕ)) (k : ℕ) (pool : List C)
    (hk : 1 ≤ k) (hkl : k ≤ pool.length) :
    (pool.map fun c => Pr{let z ← child c}[z.1.isSome]).sum / pool.length ≤
      ((k - 1 : ℕ) : ℝ≥0∞) / pool.length +
        (1 - ((k - 1 : ℕ) : ℝ≥0∞) / pool.length) *
          Pr{let z ← (thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n))
            (chargedChild child) k pool).run 0}[z.1.isSome] := by
  let : MeasurableSpace (Option W × ℕ) := ⊤
  let : MeasurableSpace (List (Option W × ℕ)) := ⊤
  have hlaw := thresholdChildren_eager ProbComp.uniformFin child k pool 0
  rw [hlaw.prEvent_eq, prEvent_bind_eq_lintegral_of_discrete]
  have hmean := lintegral_mapM_countP child (fun z => z.1.isSome) pool
  rw [← hmean]
  calc
    (∫⁻ table, (table.countP (fun z => z.1.isSome) : ℝ≥0∞) ∂𝒟[pool.mapM child]) /
        pool.length =
      ∫⁻ table, (table.countP (fun z => z.1.isSome) : ℝ≥0∞) / pool.length
        ∂𝒟[pool.mapM child] := by
          simp only [div_eq_mul_inv]
          rw [lintegral_mul_const _ Measurable.of_discrete]
    _ ≤ ∫⁻ table, ((k - 1 : ℕ) : ℝ≥0∞) / pool.length +
        (1 - ((k - 1 : ℕ) : ℝ≥0∞) / pool.length) *
          Pr{let z ← (thresholdChildren (fun n => StateT.lift (ProbComp.uniformFin n))
            tableChild k table).run 0}[z.1.isSome] ∂𝒟[pool.mapM child] := by
      apply lintegral_mono_ae
      apply evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
      intro table ht
      have hlen := List.length_of_mem_support_mapM child pool table ht
      rw [← hlen]
      exact thresholdChildren_table_success_scaled_all k table 0 hk (hlen ▸ hkl)
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul _ Measurable.of_discrete]

end Rewinding
