/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.ProbComp.IndepProductEvents
import VCVio.EvalDist.ProbabilityBounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Predictable finite-target events on an answer tape

Changing a coordinate leaves its target set unchanged.
The comparison probability is the mean uniform mass of that target set.
Strict-prefix target sets with a pathwise bound on their total cardinality give a ticket bound.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace AnswerTape

/-- A target set independent of the current coordinate has its mean uniform mass. -/
theorem evalDist_answerTape_setOf_mem_eq_lintegral_of_update_invariant
    {W : Type} [SampleableType W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
    {n : Nat} (i : Fin n) (S : (Fin n → W) → Set W)
    (currentIndependent : ∀ v value, S (Function.update v i value) = S v) :
    𝒟[answerTape W n] {v | v i ∈ S v} =
      ∫⁻ v, 𝒟[($ᵗ W : ProbComp W)] (S v) ∂𝒟[answerTape W n] := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let μ : Measure W := 𝒟[($ᵗ W : ProbComp W)]
    -- Split the chosen word from the remaining coordinates.
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => W) i
    have split := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
    -- A fixed reference word compares target sets without revealing the chosen word.
    have target (value : W) (rest : Fin n → W) :
        S (e.symm (value, rest)) = S (e.symm (Classical.arbitrary W, rest)) := by
      change S (i.insertNth value rest) = S (i.insertNth (Classical.arbitrary W) rest)
      simpa only [Fin.update_insertNth] using
        currentIndependent (i.insertNth (Classical.arbitrary W) rest) value
    have coordinate (value : W) (rest : Fin n → W) :
        e.symm (value, rest) i = value := by
      simp [e]
    rw [evalDist_answerTape]
    change (Measure.pi fun _ : Fin (n + 1) => μ) {v | v i ∈ S v} =
      ∫⁻ v, μ (S v) ∂Measure.pi (fun _ : Fin (n + 1) => μ)
    rw [← split.symm.map_eq, Measure.map_apply e.symm.measurable
      MeasurableSet.of_discrete, lintegral_map Measurable.of_discrete e.symm.measurable]
    -- Integrate the independent chosen word before the remaining coordinates.
    rw [Measure.prod_apply_symm MeasurableSet.of_discrete,
      lintegral_prod_symm _ Measurable.of_discrete.aemeasurable]
    apply lintegral_congr
    intro rest
    change μ {value | e.symm (value, rest) i ∈ S (e.symm (value, rest))} =
      ∫⁻ value, μ (S (e.symm (value, rest))) ∂μ
    simp_rw [coordinate, target]
    simp [μ]

/-- Prefix-predictable target sets cost at most their pathwise number of comparison tickets.

Each slot may project the same full word differently.
The projections and their comparison events need not be independent.
-/
theorem prEvent_answerTape_exists_project_mem_le_tickets
    {W D H : Type} [SampleableType W] {n B : Nat}
    (slots : Finset H) (projection : H → W → D)
    (targets : Fin n → (Fin n → W) → H → Finset D)
    (epsilon : ℝ≥0∞)
    (predictable : ∀ i v w,
      (∀ j : Fin n, j.val < i.val → v j = w j) → targets i v = targets i w)
    (fiberBound : ∀ h ∈ slots, ∀ d,
      Pr{let word ← ($ᵗ W : ProbComp W)}[projection h word = d] ≤ epsilon)
    (ticketBudget : ∀ v,
      (∑ i : Fin n, ∑ h ∈ slots, (targets i v h).card) ≤ B) :
    Pr{let v ← answerTape W n}[
      ∃ i : Fin n, ∃ h ∈ slots, projection h (v i) ∈ targets i v h] ≤
      (B : ℝ≥0∞) * epsilon := by
  classical
  let : MeasurableSpace W := ⊤
  let μ : Measure W := 𝒟[($ᵗ W : ProbComp W)]
  let tape : Measure (Fin n → W) := 𝒟[answerTape W n]
  let S : Fin n → (Fin n → W) → Set W :=
    fun i v => {word | ∃ h ∈ slots, projection h word ∈ targets i v h}
  have oneTargetSet (i : Fin n) (v : Fin n → W) (h : H) (hh : h ∈ slots) :
      μ {word | projection h word ∈ targets i v h} ≤
        ((targets i v h).card : ℝ≥0∞) * epsilon := by
    have bound := prEvent_exists_finset_le_card_mul (targets i v h)
      ($ᵗ W : ProbComp W) (fun d word => projection h word = d)
      (fun d _ => fiberBound h hh d)
    have event : {word : W | ∃ d ∈ targets i v h, projection h word = d} =
        {word | projection h word ∈ targets i v h} := by
      ext word
      constructor
      · rintro ⟨d, hd, same⟩
        change projection h word ∈ targets i v h
        exact same.symm ▸ hd
      · intro member
        exact ⟨projection h word, member, rfl⟩
    simpa only [prEvent_eq_evalDist_of_discrete, event] using bound
  have massBound (i : Fin n) (v : Fin n → W) :
      μ (S i v) ≤ (∑ h ∈ slots, ((targets i v h).card : ℝ≥0∞)) * epsilon := by
    calc
      μ (S i v) ≤ ∑ h ∈ slots, μ {word | projection h word ∈ targets i v h} := by
        refine (measure_mono ?_).trans (measure_biUnion_finset_le slots
          (fun h => {word | projection h word ∈ targets i v h}))
        rintro word ⟨h, hh, hw⟩
        exact Set.mem_biUnion hh hw
      _ ≤ ∑ h ∈ slots, ((targets i v h).card : ℝ≥0∞) * epsilon :=
        Finset.sum_le_sum fun h hh => oneTargetSet i v h hh
      _ = _ := (Finset.sum_mul _ _ _).symm
  -- Strict-prefix predictability makes each target independent of its own coordinate.
  have average (i : Fin n) :
      tape {v | v i ∈ S i v} = ∫⁻ v, μ (S i v) ∂tape := by
    apply evalDist_answerTape_setOf_mem_eq_lintegral_of_update_invariant
    intro v value
    have sameTargets := predictable i (Function.update v i value) v (by
      intro j hj
      have different : j ≠ i := fun eq => (Nat.lt_irrefl i.val) (eq ▸ hj)
      simp [different])
    simp only [S, sameTargets]
  rw [prEvent_eq_evalDist_of_discrete]
  change tape {v | ∃ i : Fin n, v i ∈ S i v} ≤ (B : ℝ≥0∞) * epsilon
  calc
    tape {v | ∃ i : Fin n, v i ∈ S i v} ≤
        ∑ i : Fin n, tape {v | v i ∈ S i v} := by
      rw [show {v | ∃ i : Fin n, v i ∈ S i v} = ⋃ i : Fin n, {v | v i ∈ S i v} by
        ext v
        simp]
      exact measure_iUnion_fintype_le tape _
    -- Average the total comparison mass before applying the pathwise ticket budget.
    _ = ∫⁻ v, ∑ i : Fin n, μ (S i v) ∂tape := by
      simp_rw [average]
      exact (lintegral_finsetSum Finset.univ (fun _ _ => Measurable.of_discrete)).symm
    _ ≤ ∫⁻ v, (∑ i : Fin n, ∑ h ∈ slots,
        ((targets i v h).card : ℝ≥0∞)) * epsilon ∂tape := by
      apply lintegral_mono
      intro v
      exact (Finset.sum_le_sum (fun i _ => massBound i v)).trans_eq
        (Finset.sum_mul _ _ _).symm
    _ ≤ ∫⁻ _v, (B : ℝ≥0∞) * epsilon ∂tape := by
      apply lintegral_mono
      intro v
      change (∑ i : Fin n, ∑ h ∈ slots,
        ((targets i v h).card : ℝ≥0∞)) * epsilon ≤ (B : ℝ≥0∞) * epsilon
      gcongr
      exact_mod_cast ticketBudget v
    _ = _ := by simp [tape]

end AnswerTape
