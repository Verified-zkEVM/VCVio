/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ClassGrowth
import VCVio.OracleComp.EvalDist.Sum

/-!
# The per-class charge, paid per fresh entry

The charge counts the class's **fresh** entries rather than every in-class query. That is the
right count when the signer's queries are not in the budget: the honest signer asks millions of
canonical inputs per request, all of them cache hits, and none of them can produce a bad answer,
because a hit produces no answer at all.

What a bad answer actually needs is a fresh entry: an input the run installed. So the charge is
against the inputs of the class that the final cache holds and the initial one did not
(`freshMass`). A hit leaves the count alone, exactly as a coin does, and a miss contributes its
own rate plus the tail, by an induction on the run with the count taken as the cache's own
growth (`prob_bad_le_expected_fresh`).

The growth is read as a sum over all inputs in `ℝ≥0∞`, so no finiteness is needed anywhere: an
expectation of an infinite count is simply `⊤`, and the bound is then trivial.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.FreshExpectation

variable {α β γ : Type}

open Security GrowthCharge

/-! ## The fresh entries of a class -/

open scoped Classical in
/-- **The class's fresh entries**: one unit per input of the class the final cache holds and the
initial one does not. -/
@[expose]
noncomputable def freshMass (inClass : Bytes → Prop) (initial final : QueryCache HashSpec) :
    ℝ≥0∞ :=
  ∑' input : Bytes, if inClass input ∧ initial input = none ∧ final input ≠ none then 1 else 0

open scoped Classical in
/-- **Installing an input moves one unit out of the fresh mass**, if the input is of the class. -/
theorem freshMass_cacheQuery (inClass : Bytes → Prop) (initial final : QueryCache HashSpec)
    (input : Bytes) (answer : HashOutput) (hfresh : initial input = none)
    (hfinal : final input ≠ none) :
    freshMass inClass initial final =
      (if inClass input then 1 else 0) +
        freshMass inClass (initial.cacheQuery input answer) final := by
  unfold freshMass
  rw [ENNReal.tsum_eq_add_tsum_ite input]
  congr 1
  · by_cases hclass : inClass input <;> simp [hclass, hfresh, hfinal]
  · refine tsum_congr fun other => ?_
    by_cases hother : other = input
    · subst hother
      simp
    · rw [ite_eq_right hother, QueryCache.cacheQuery_of_ne _ _ hother]

open scoped Classical in
/-- **The fresh mass is at most the size of any set holding the fresh inputs.** -/
theorem freshMass_le_card (inClass : Bytes → Prop) (initial final : QueryCache HashSpec)
    (holder : Finset Bytes)
    (hheld : ∀ input, inClass input → initial input = none → final input ≠ none →
      input ∈ holder) :
    freshMass inClass initial final ≤ (holder.card : ℝ≥0∞) := by
  unfold freshMass
  calc (∑' input : Bytes,
        if inClass input ∧ initial input = none ∧ final input ≠ none then (1 : ℝ≥0∞) else 0)
      ≤ ∑' input : Bytes, if input ∈ holder then (1 : ℝ≥0∞) else 0 := by
        refine ENNReal.tsum_le_tsum fun input => ?_
        split_ifs with hfresh hmem
        · exact le_rfl
        · exact absurd (hheld input hfresh.1 hfresh.2.1 hfresh.2.2) hmem
        · exact zero_le
        · exact le_rfl
    _ = ∑ input ∈ holder, (1 : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := holder) (fun input hinput => ite_eq_right hinput)]
        exact Finset.sum_congr rfl fun input hinput => ite_eq_left hinput
    _ = (holder.card : ℝ≥0∞) := by simp

open scoped Classical in
/-- **Two disjoint classes' fresh masses add.** -/
theorem freshMass_add (left right : Bytes → Prop) (initial final : QueryCache HashSpec)
    (hdisjoint : ∀ input, left input → ¬ right input) :
    freshMass left initial final + freshMass right initial final =
      freshMass (fun input => left input ∨ right input) initial final := by
  unfold freshMass
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun input => ?_
  by_cases hleft : left input
  · have hright := hdisjoint input hleft
    by_cases hfresh : initial input = none ∧ final input ≠ none <;> simp [hleft, hright, hfresh]
  · by_cases hright : right input <;>
      by_cases hfresh : initial input = none ∧ final input ≠ none <;>
        simp [hleft, hright, hfresh]

open scoped Classical in
/-- **A list of distinct fresh inputs of the class is no longer than the class's fresh mass.** -/
theorem length_le_freshMass (inClass : Bytes → Prop) (initial final : QueryCache HashSpec)
    (inputs : List Bytes) (hnodup : inputs.Nodup)
    (hfresh : ∀ input ∈ inputs,
      inClass input ∧ initial input = none ∧ final input ≠ none) :
    (inputs.length : ℝ≥0∞) ≤ freshMass inClass initial final := by
  unfold freshMass
  calc (inputs.length : ℝ≥0∞) = ∑ input ∈ inputs.toFinset, (1 : ℝ≥0∞) := by
        rw [Finset.sum_const, List.toFinset_card_of_nodup hnodup, nsmul_eq_mul, mul_one]
    _ = ∑ input ∈ inputs.toFinset,
          (if inClass input ∧ initial input = none ∧ final input ≠ none then (1 : ℝ≥0∞)
            else 0) :=
        Finset.sum_congr rfl fun input hinput =>
          (ite_eq_left (hfresh input (List.mem_toFinset.mp hinput))).symm
    _ ≤ _ := ENNReal.sum_le_tsum _

/-! ## Expectations of a value -/

/-- **An expectation splits along a bind.** -/
theorem tsum_bind_mul {β γ : Type} (run : ProbComp β) (next : β → ProbComp γ)
    (value : γ → ℝ≥0∞) :
    ∑' output, Pr{let x ← run >>= next}[x = output] * value output =
      ∑' middle, Pr{let x ← run}[x = middle] *
        ∑' output, Pr{let x ← next middle}[x = output] * value output :=
  OracleComp.tsum_prEvent_bind_mul run next value

/-- **An expectation splits along a map.** -/
theorem tsum_map_mul {β γ : Type} (run : ProbComp β) (reshape : β → γ) (value : γ → ℝ≥0∞) :
    ∑' output, Pr{let x ← reshape <$> run}[x = output] * value output =
      ∑' middle, Pr{let x ← run}[x = middle] * value (reshape middle) :=
  OracleComp.tsum_prEvent_map_mul run reshape value

/-- **A pointwise bound on the support bounds the expectation.** -/
theorem tsum_mul_le {β : Type} (run : ProbComp β) (left right : β → ℝ≥0∞)
    (hle : ∀ value ∈ support run, left value ≤ right value) :
    ∑' value, Pr{let x ← run}[x = value] * left value ≤
      ∑' value, Pr{let x ← run}[x = value] * right value := by
  refine ENNReal.tsum_le_tsum fun value => ?_
  by_cases hmem : value ∈ support run
  · exact mul_le_mul' le_rfl (hle value hmem)
  · rw [(prEvent_eq_zero_of_not_mem_support _) hmem, zero_mul, zero_mul]

/-- **A constant bound on the support bounds the expectation**, the run's mass being at most
one. -/
theorem tsum_mul_le_const {β : Type} (run : ProbComp β) (value : β → ℝ≥0∞) (bound : ℝ≥0∞)
    (hle : ∀ output ∈ support run, value output ≤ bound) :
    ∑' output, Pr{let x ← run}[x = output] * value output ≤ bound := by
  calc ∑' output, Pr{let x ← run}[x = output] * value output
      ≤ ∑' output, Pr{let x ← run}[x = output] * bound := tsum_mul_le run _ _ hle
    _ = (∑' output, Pr{let x ← run}[x = output]) * bound := ENNReal.tsum_mul_right
    _ ≤ 1 * bound := mul_le_mul' (OracleComp.tsum_prEvent_le_one run) le_rfl
    _ = bound := one_mul bound

/-! ## The charge -/

open scoped Classical in
/-- **The bad event is charged at the class's expected fresh entries.** If an answer can be bad
only at an input of the class, and is bad there with probability at most `rate`, then a run
started clean ends with a bad cached answer with probability at most `rate` times the expected
number of inputs of the class it installed. -/
theorem prob_bad_le_expected_fresh (inClass : Bytes → Prop) (bad : Bytes → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ input,
      Pr{let answer ← ($ᵗ HashOutput : ProbComp HashOutput)}[bad input answer] ≤ rate)
    (hclass : ∀ input answer, bad input answer → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (initial : QueryCache HashSpec), CleanBad bad initial →
      Pr{let x ← (simulateQ KeygenUniform.rom computation).run initial}[(Bad bad) x] ≤
        (∑' result, Pr{let x ← (simulateQ KeygenUniform.rom computation).run initial}[x = result] *
          freshMass inClass initial result.2) * rate := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro initial hclean
    refine le_of_eq_of_le (b := 0) ?_ zero_le
    rw [simulateQ_pure, StateT.run_pure]
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun result hresult hbad => ?_
    rw [support_pure, Set.mem_singleton_iff] at hresult
    subst hresult
    obtain ⟨input, output, hanswer, hbadness⟩ := hbad
    exact hclean input output hanswer hbadness
  | query_bind queried next ih =>
    intro initial hclean
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · -- A coin leaves the cache alone.
      rw [OracleComp.prEvent_bind_eq_tsum, tsum_bind_mul, ← ENNReal.tsum_mul_right]
      have hstep : ∀ step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initial),
          step.2 = initial := by
        intro step hstep
        have hform : step ∈
            Set.range (fun value : OracleWorld.Range (Sum.inl coin) => (value, initial)) := by
          simpa [KeygenUniform.rom, RandomOracleModel.impl, unifFwdImpl] using hstep
        obtain ⟨value, hvalue⟩ := hform
        rw [← hvalue]
      refine ENNReal.tsum_le_tsum fun step => ?_
      by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initial)
      · rw [mul_assoc, hstep step hmem]
        exact mul_le_mul' le_rfl (ih step.1 initial hclean)
      · rw [prEvent_eq_zero_of_not_mem_support _ hmem]
        simp
    · cases hcached : initial input with
      | some cached =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initial =
            (pure (cached, initial) : ProbComp (HashOutput × QueryCache HashSpec)) := by
          change (randomOracle input).run initial = _
          rw [QueryImpl.withCaching_run_some _ hcached]
        rw [hrun]
        erw [pure_bind]
        exact ih cached initial hclean
      | none =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initial =
            (fun answer => (answer, initial.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          change (randomOracle input).run initial = _
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrun]
        erw [bind_map_left]
        rw [OracleComp.prEvent_bind_eq_tsum, tsum_bind_mul]
        -- After a miss, the tail's fresh mass is the step's own unit plus the tail's.
        have htail : ∀ answer : HashOutput,
            ∑' result, Pr{let x ← ((simulateQ KeygenUniform.rom (next answer)).run
                (initial.cacheQuery input answer))}[x = result] *
                freshMass inClass initial result.2 =
              (if inClass input then 1 else 0) +
                ∑' result, Pr{let x ← ((simulateQ KeygenUniform.rom (next answer)).run
                    (initial.cacheQuery input answer))}[x = result] *
                  freshMass inClass (initial.cacheQuery input answer) result.2 := by
          intro answer
          calc ∑' result, Pr{let x ← ((simulateQ KeygenUniform.rom (next answer)).run
              (initial.cacheQuery input answer))}[x = result] *
                freshMass inClass initial result.2
              = ∑' result, Pr{let x ← ((simulateQ KeygenUniform.rom (next answer)).run
                  (initial.cacheQuery input answer))}[x = result] *
                  ((if inClass input then 1 else 0) +
                    freshMass inClass (initial.cacheQuery input answer) result.2) := by
                refine tsum_congr fun result => ?_
                by_cases hmem : result ∈ support ((simulateQ KeygenUniform.rom
                    (next answer)).run (initial.cacheQuery input answer))
                · have hpersist := cache_value_persists (next answer)
                    (initial.cacheQuery input answer) result.2 result.1 hmem input answer
                    (QueryCache.cacheQuery_self _ _ _)
                  rw [freshMass_cacheQuery inClass initial result.2 input answer hcached
                    (by rw [hpersist]; simp)]
                · rw [prEvent_eq_zero_of_not_mem_support _ hmem, zero_mul, zero_mul]
            _ = (∑' result, Pr{let x ← ((simulateQ KeygenUniform.rom (next answer)).run
                (initial.cacheQuery input answer))}[x = result] *
                  (if inClass input then 1 else 0)) +
                ∑' result, Pr{let x ← ((simulateQ KeygenUniform.rom (next answer)).run
                    (initial.cacheQuery input answer))}[x = result] *
                  freshMass inClass (initial.cacheQuery input answer) result.2 := by
                rw [← ENNReal.tsum_add]
                exact tsum_congr fun result => mul_add _ _ _
            _ = _ := by
                rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]
        simp_rw [htail]
        have hpointwise : ∀ answer : HashOutput,
            Pr{let x ← ((simulateQ KeygenUniform.rom (next answer)).run
                (initial.cacheQuery input answer))}[Bad bad x] ≤
              (if bad input answer then 1 else 0) +
                (∑' result, Pr{let x ← ((simulateQ KeygenUniform.rom (next answer)).run
                    (initial.cacheQuery input answer))}[x = result] *
                  freshMass inClass (initial.cacheQuery input answer) result.2) * rate := by
          intro answer
          by_cases hbadness : bad input answer
          · rw [ite_eq_left hbadness]
            exact le_add_right (prEvent_le_one _)
          · rw [ite_eq_right hbadness, zero_add]
            exact ih answer (initial.cacheQuery input answer) (hclean.cacheQuery hbadness)
        refine le_trans (ENNReal.tsum_le_tsum fun answer =>
          mul_le_mul' le_rfl (hpointwise answer)) ?_
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_add, add_mul]
        refine add_le_add ?_ ?_
        · have hbadMass : (∑' answer : HashOutput,
                Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = answer] *
                  (if bad input answer then (1 : ℝ≥0∞) else 0)) =
              Pr{let answer ← ($ᵗ HashOutput : ProbComp HashOutput)}[bad input answer] := by
            rw [OracleComp.prEvent_eq_tsum_ite]
            refine tsum_congr fun answer => ?_
            split_ifs <;> simp only [mul_one, mul_zero]
          erw [hbadMass]
          calc Pr{let answer ← ($ᵗ HashOutput : ProbComp HashOutput)}[bad input answer]
              ≤ (if inClass input then 1 else 0) * rate := by
                by_cases hmember : inClass input
                · rw [ite_eq_left hmember, one_mul]
                  exact hrate input
                · rw [ite_eq_right hmember, zero_mul]
                  exact le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _
                    fun answer _ hbadness => hmember (hclass input answer hbadness))
            _ = (∑' answer : HashOutput,
                  Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = answer] *
                  (if inClass input then 1 else 0)) * rate := by
                rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]
        · rw [← ENNReal.tsum_mul_right]
          refine le_of_eq (tsum_congr fun answer => ?_)
          ring

end SlhDsaSecurity.FreshExpectation
