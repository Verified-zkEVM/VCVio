/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.Rewinding.Cost
public import VCVioTest.Rewinding

/-!
# Charged-rerun regressions

## Expected per-challenge costs do not compose

`Rewinding.IsFinder.expectedCalls_bind_runCharged_le_lintegral_sup_mul` bounds the expected
accumulated charge by `T` times the expectation, over the world, of the largest rerun cost in that
world. It cannot be weakened to an expected cost per challenge vector. The weakened
statement says: every finder meeting the `Rewinding.IsFinder` contract with cost `T`, against a
randomly drawn world whose rerun on each challenge vector has expected cost at most `c` (or whose
rerun cost, averaged over the world and a uniform challenge vector, is at most `c`), has expected
accumulated charge at most `c * T`.

One round with binary challenges refutes it. The world is a uniform bit `w`; every rerun accepts
iff `w = 1`, and a rerun costs `3` on the challenge equal to `w` and `1` otherwise. The finder
queries challenge `0`, reads `w` off the verdict, and then queries challenge `w`. It meets the
contract at error `0` and cost `2`. For each fixed challenge vector, the expected rerun cost over
the world is `2`, and so is the average over the world and a uniform challenge vector; yet the
expected accumulated charge is `5 > 2 * 2`, because the second rerun always lands on the
expensive challenge. In each world the largest rerun cost is `3`, so its expectation over the
world is `3`, and the bound `3 * 2` holds.

This refutes a lemma about the `Rewinding.IsFinder` contract, which lets a finder choose its
inputs after observing the world. It does not refute expected-cost bounds for specific finders:
here the second challenge depends on the first verdict, and the example says nothing about
finders whose challenge vectors are drawn independently and uniformly.

## Every rerun is charged

Two reruns of a one-query coin flip from a frozen tape report the same coin. Under the unit cost
model the charged attempt records a query cost of `2` beside two complete runs, and its expected
accumulated query cost is `2`. Under a cost model that prices each query at `3` it records `6`
beside two complete runs, so the query cost differs from the run count. A finder against a fixed
table whose every entry reports cost `3` accumulates `6` over its two reruns. A charge that
ignored the reported or instrumented cost would fail these equalities. The worst-case bounds
`Rewinding.ResetPolicy.cost_le_mul_runs_of_mem_support_chargedAttempt` and
`Rewinding.ResetPolicy.finder_bounds_charged_of_worstCaseCostBound` apply to these instances.
-/

public section

open OracleComp OracleSpec Rewinding MeasureTheory
open scoped ENNReal

namespace VCVioTest.RewindingCost

private theorem div_two_eq {a b : ℝ≥0∞} (h : 2 * b = a) : a / 2 = b :=
  ((ENNReal.eq_div_iff (by norm_num) (by norm_num)).2 h).symm

/-- One round with binary challenges. -/
abbrev Ch : Unit → Type := fun _ => Fin 2

/-- Complete challenge vectors. -/
abbrev Q : Type := (r : Unit) → Ch r

/-- The challenge vector with challenge `i`. -/
@[expose] def vec (i : Fin 2) : Q := fun _ => i

/-- In world `w`, every rerun accepts iff `w = 1`. -/
@[expose] def acc (w : Fin 2) : Q → Bool := fun _ => decide (w = 1)

/-- In world `w`, a rerun costs `3` on the challenge equal to `w` and `1` otherwise. -/
@[expose] def cost (w : Fin 2) : Q → ℕ := fun q => if q () = w then 3 else 1

/-- Query challenge `0`, read the world off its verdict, then query the challenge equal to the
world. -/
@[expose] def find : OracleComp (unifSpec + accSpec Ch) (Option Unit) := do
  let b : Bool ← query (spec := unifSpec + accSpec Ch) (Sum.inr (vec 0))
  let _ ← query (spec := unifSpec + accSpec Ch) (Sum.inr (vec (if b then 1 else 0)))
  pure (some ())

/-- The world is a uniform bit. -/
@[expose] def world : ProbComp (Fin 2) := (unifSpec.query 1 : OracleComp unifSpec (Fin 2))

/-- Against any table, `find` makes two reruns and is charged their two costs. -/
theorem runCharged_find (f : Q → Bool) (k : Q → ℕ) :
    runCharged find f k 0 =
      pure (some (), k (vec 0) + k (vec (if f (vec 0) then 1 else 0))) := by
  simp [runCharged, find, charged]

/-- Every acceptance function sees exactly two complete runs. -/
theorem runFinder_find (f : Q → Bool) : runFinder find f = pure (some (), 2) := by
  simp [runFinder, find, counted]

/-- `find` meets the finder contract with the trivial output predicate, error `0` and cost `2`. -/
theorem isFinder_find : IsFinder (fun _ _ => True) find 0 2 where
  sound := fun _ _ _ _ _ => trivial
  success := fun f => by
    rw [runFinder_find]
    simp only [acceptRate, tsub_zero, map_pure, Option.isSome_some, prEvent_pure_prop,
      ↓reduceIte, mul_one, zero_add]
    exact ENNReal.div_le_of_le_mul (by
      rw [one_mul]; exact_mod_cast Finset.card_filter_le _ _)
  cost := fun f => by rw [runFinder_find, expectedCalls_pure]; norm_num

/-- Integration against the uniform world bit is the average of the two values. -/
theorem lintegral_world (g : Fin 2 → ℝ≥0∞) : ∫⁻ w, g w ∂𝒟[world] = (g 0 + g 1) / 2 := by
  let : MeasurableSpace (Fin 2) := ⊤
  have h : 𝒟[world] = ProbabilityTheory.uniformOn Set.univ := OracleComp.evalDist_query_uniform 1
  rw [h, lintegral_fintype]
  simp [Fin.sum_univ_two, ProbabilityTheory.uniformOn_univ, div_eq_mul_inv, add_mul]

/-- The expected accumulated charge against the world is `(6 + 4) / 2 = 5`. -/
theorem expectedCalls_world_runCharged_find :
    expectedCalls (do let w ← world; runCharged find (acc w) (cost w) 0) = 5 := by
  let : MeasurableSpace (Fin 2) := ⊤
  rw [expectedCalls_bind, lintegral_world]
  simp only [runCharged_find, expectedCalls_pure, acc, cost, vec]
  norm_num
  exact div_two_eq (by norm_num)

/-- For each challenge vector, the expected rerun cost over the world is `(3 + 1) / 2 = 2`. -/
theorem lintegral_world_cost (q : Q) : ∫⁻ w, (cost w q : ℝ≥0∞) ∂𝒟[world] = 2 := by
  rw [lintegral_world]
  apply div_two_eq
  unfold cost
  generalize q () = i
  fin_cases i <;> norm_num

/-- The rerun cost averaged over the world and a uniform challenge vector is `2`. -/
theorem lintegral_world_average_cost :
    ∫⁻ w, (∑ q : Q, (cost w q : ℝ≥0∞)) / Fintype.card Q ∂𝒟[world] = 2 := by
  have hQ : Fintype.card Q = 2 := by simp
  have hsum (w : Fin 2) : ∑ q : Q, (cost w q : ℝ≥0∞) = 4 := by
    rw [Fintype.sum_equiv (Equiv.funUnique Unit (Fin 2)) (fun q => (cost w q : ℝ≥0∞))
      (fun i => (cost w (vec i) : ℝ≥0∞)) (fun q => rfl)]
    fin_cases w <;> simp [Fin.sum_univ_two, cost, vec] <;> norm_num
  simp only [hsum, hQ, lintegral_world, Nat.cast_ofNat]
  rw [div_two_eq (a := 4) (b := 2) (by norm_num)]
  exact div_two_eq (by norm_num)

/-- The bound with an expected cost per challenge vector fails for a finder meeting the
contract. -/
theorem not_forall_expectedCalls_bind_runCharged_le_of_lintegral :
    ¬ ∀ (find' : OracleComp (unifSpec + accSpec Ch) (Option Unit)) (T : ℝ≥0∞),
      IsFinder (fun _ _ => True) find' 0 T →
      ∀ (F : ProbComp (Fin 2)) (acc' : Fin 2 → Q → Bool) (cost' : Fin 2 → Q → ℕ) (c : ℕ),
        (∀ q, ∫⁻ w, (cost' w q : ℝ≥0∞) ∂𝒟[F] ≤ c) →
        expectedCalls (do let w ← F; runCharged find' (acc' w) (cost' w) 0) ≤ (c : ℝ≥0∞) * T := by
  intro h
  have := h find 2 isFinder_find world acc cost 2 fun q => (lintegral_world_cost q).le
  rw [expectedCalls_world_runCharged_find] at this
  norm_num at this

/-- The bound with the rerun cost averaged over the world and a uniform challenge vector fails for
a finder meeting the contract. -/
theorem not_forall_expectedCalls_bind_runCharged_le_of_average :
    ¬ ∀ (find' : OracleComp (unifSpec + accSpec Ch) (Option Unit)) (T : ℝ≥0∞),
      IsFinder (fun _ _ => True) find' 0 T →
      ∀ (F : ProbComp (Fin 2)) (acc' : Fin 2 → Q → Bool) (cost' : Fin 2 → Q → ℕ) (c : ℕ),
        ∫⁻ w, (∑ q : Q, (cost' w q : ℝ≥0∞)) / Fintype.card Q ∂𝒟[F] ≤ c →
        expectedCalls (do let w ← F; runCharged find' (acc' w) (cost' w) 0) ≤ (c : ℝ≥0∞) * T := by
  intro h
  have := h find 2 isFinder_find world acc cost 2 lintegral_world_average_cost.le
  rw [expectedCalls_world_runCharged_find] at this
  norm_num at this

/-- The worst-case bound holds on the same instance: `5 ≤ 3 * 2`. -/
theorem expectedCalls_world_runCharged_find_le :
    expectedCalls (do let w ← world; runCharged find (acc w) (cost w) 0) ≤ 3 * 2 := by
  have := isFinder_find.expectedCalls_bind_runCharged_le world acc cost 3 fun w _ q => by
    unfold cost
    split_ifs <;> norm_num
  exact_mod_cast this

/-- In each world the largest rerun cost is `3`, so its expectation over the world is `3`. -/
theorem lintegral_world_sup_cost :
    ∫⁻ w, ((Finset.univ.sup (cost w) : ℕ) : ℝ≥0∞) ∂𝒟[world] = 3 := by
  have hsup (w : Fin 2) : Finset.univ.sup (cost w) = 3 :=
    le_antisymm (Finset.sup_le fun q _ => by unfold cost; split_ifs <;> norm_num)
      (by simpa [cost, vec] using Finset.le_sup (f := cost w) (Finset.mem_univ (vec w)))
  simp only [hsup, lintegral_world]
  exact div_two_eq (by norm_num)

/-- The bound with the expected largest rerun cost holds on the same instance: `5 ≤ 3 * 2`. -/
theorem expectedCalls_world_runCharged_find_le_lintegral_sup :
    expectedCalls (do let w ← world; runCharged find (acc w) (cost w) 0) ≤ 3 * 2 := by
  simpa only [lintegral_world_sup_cost] using
    isFinder_find.expectedCalls_bind_runCharged_le_lintegral_sup_mul world acc cost

/-! ## Every rerun is charged -/

/-- A uniform bit drawn by one query has worst-case unit query cost `1`. -/
theorem worstCaseCostBound_coin :
    WorstCaseCostBound ($[0..1] : ProbComp (Fin 2)) CostModel.unit 1 :=
  worstCaseCostBound_query (spec := unifSpec) 1 CostModel.unit

/-- Both reruns of a frozen coin flip read the same tape entry; the charged attempt records one
unit query per rerun beside the two complete runs. -/
theorem chargedAttempt_twoReruns :
    fixedTape.chargedAttempt (fun _ : Unit => ($[0..1] : ProbComp (Fin 2))) CostModel.unit
        VCVioTest.Rewinding.twoReruns =
      (fun b => (((b, b), 2), 2)) <$> ($[0..1] : ProbComp (Fin 2)) := by
  unfold ResetPolicy.chargedAttempt ResetPolicy.attempt fixedTape ResetPolicy.rerun
    VCVioTest.Rewinding.twoReruns costAdapter
  simp [QueryImpl.add_apply_inr, StateT.run_bind, costAdapterImpl, AddWriterT.runAdd,
    CostModel.unit, FixedTape.answer, FixedTape.advance,
    uniformSample, ProbComp.uniformFin_def,
    map_eq_bind_pure_comp, bind_assoc, QueryImpl.withAddCost, QueryImpl.withCost]
  rfl

/-- Each query costs `3`. -/
@[expose] def costThree : CostModel unifSpec ℕ where
  queryCost _ := 3

/-- Under a cost of `3` per query, the charged attempt records `6` beside the two complete
runs. -/
theorem chargedAttempt_twoReruns_costThree :
    fixedTape.chargedAttempt (fun _ : Unit => ($[0..1] : ProbComp (Fin 2))) costThree
        VCVioTest.Rewinding.twoReruns =
      (fun b => (((b, b), 6), 2)) <$> ($[0..1] : ProbComp (Fin 2)) := by
  unfold ResetPolicy.chargedAttempt ResetPolicy.attempt fixedTape ResetPolicy.rerun
    VCVioTest.Rewinding.twoReruns costAdapter
  simp [QueryImpl.add_apply_inr, StateT.run_bind, costAdapterImpl, AddWriterT.runAdd,
    costThree, FixedTape.answer, FixedTape.advance,
    uniformSample, ProbComp.uniformFin_def,
    map_eq_bind_pure_comp, bind_assoc, QueryImpl.withAddCost, QueryImpl.withCost]
  rfl

/-- The expected accumulated query cost of the two reruns is exactly two. -/
theorem expectedCalls_fst_chargedAttempt_twoReruns :
    expectedCalls (Prod.fst <$> fixedTape.chargedAttempt
      (fun _ : Unit => ($[0..1] : ProbComp (Fin 2))) CostModel.unit
        VCVioTest.Rewinding.twoReruns) = 2 := by
  rw [chargedAttempt_twoReruns, Functor.map_map]
  simp [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
    AddWriterT.costs_def]

/-- On every outcome of the two reruns, the query cost is at most one per complete run. -/
theorem cost_le_mul_runs_of_mem_support_chargedAttempt_twoReruns :
    ∀ z ∈ support (fixedTape.chargedAttempt (fun _ : Unit => ($[0..1] : ProbComp (Fin 2)))
      CostModel.unit VCVioTest.Rewinding.twoReruns), z.1.2 ≤ 1 * z.2 :=
  fixedTape.cost_le_mul_runs_of_mem_support_chargedAttempt _ _ 1
    (fun _ => worstCaseCostBound_coin) _

/-- Against a fixed table that accepts and reports cost `3` on every input, the adapted finder
accumulates `6` over its two reruns. -/
theorem fst_map_simulateQ_counted_costAdapter_find :
    Prod.fst <$> (simulateQ (coins (S := ℕ) + counted fun _ : Q => (true, 3))
      (costAdapter find)).run 0 = pure (some (), 6) := by
  simp [costAdapter, costAdapterImpl, find, counted, coins]

/-- Each rerun accepts iff a frozen coin flip is `1`. -/
@[expose] def verdict : Q → ProbComp Bool :=
  fun _ => (fun b : Fin 2 => decide (b = 1)) <$> ($[0..1] : ProbComp (Fin 2))

/-- Charged by unit query cost against frozen coin-flip reruns, `find` succeeds with probability
at least the average acceptance rate, makes at most two complete runs in expectation, and has
expected query cost at most two. -/
theorem finder_bounds_charged_verdict_find :
    averageAcceptRate (fixedTape.eagerTable verdict) ≤
        Pr{let z ← fixedTape.chargedAttempt verdict CostModel.unit find}[z.1.1.isSome] ∧
      expectedCalls ((fun z => (z.1.1, z.2)) <$>
        fixedTape.chargedAttempt verdict CostModel.unit find) ≤ 2 ∧
      expectedCalls (Prod.fst <$> fixedTape.chargedAttempt verdict CostModel.unit find) ≤ 2 := by
  simpa using fixedTape.finder_bounds_charged_of_worstCaseCostBound verdict CostModel.unit
    isFinder_find 1 fun _ => (worstCaseCostBound_map_iff _ _ _ _).2 worstCaseCostBound_coin

end VCVioTest.RewindingCost
