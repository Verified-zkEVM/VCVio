/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.BlockOperational
public import VCVio.CryptoFoundations.Rewinding.BlockEager

/-!
# The block step with probabilistic children

`OracleComp.blockFinder` asks a Boolean acceptance oracle about challenges. In a multi-round finder
the child of a challenge is itself a randomized search over the later rounds, which succeeds with
some probability and has a cost. `OracleComp.blockChildStep child k` draws a uniform centre and runs
the block step `Rewinding.blockChildren` on it with such children: it runs the child at the centre
and collects `k j - 1` successful children among the coordinate-`j` neighbours of the centre, for
every `j`.

`OracleComp.prEvent_child_le_blockChildStep` is its success clause: if a uniformly drawn child
succeeds with probability `ε`, the step succeeds with a probability `p` such that
`ε ≤ κ + (1 - κ) p`, with `κ = ∑ j, (k j - 1) / |S j|`, as for the acceptance oracle.

The proof draws all children in advance (`Rewinding.blockChildren_eager_table`). With a table of
results as the child, the step succeeds exactly at the good centres of the table's successful
entries (`OracleComp.prEvent_isSome_blockChildren_table`), so the counting bound
`CoordinateWise.div_card_filter_le_affine_pi` holds for every table, and the success clause is its
expectation over the table.

`OracleComp.expectedCalls_blockChildStep_le` is its cost clause: the step costs at most
`1 + ∑ j, (k j - 1)` times the average expected cost of the children. On a table, the draws of the
accepted centres at coordinate `j` inspect at most `k j - 1` times the total weight in expectation
(`OracleComp.sum_drawWeight_neighbourPool_le`), by the column count
`CoordinateWise.sum_accept_column_weight_le`.

## References

* [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
    Asymptotic and Concrete Efficiency*](https://eprint.iacr.org/2023/846)
-/

public section

open Finset CoordinateWise OracleComp OracleSpec ProbComp Rewinding MeasureTheory

open scoped ENNReal NNReal

namespace OracleComp

variable {ι : Type} [DecidableEq ι] [Fintype ι] {S : ι → Type} [∀ j, DecidableEq (S j)]
  [∀ j, Fintype (S j)] {W : Type}

/-- **Success on a table.** With a deterministic table of results as the child, the block step at
`c₀` succeeds with certainty or not at all, according to whether `c₀` is good for the table's
successful entries. -/
theorem prEvent_isSome_blockChildren_table (T : ((i : ι) → S i) → Option W × ℕ) (k : ι → ℕ)
    (c₀ : (i : ι) → S i) (count : ℕ) :
    Pr{let z ← (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (tableChild ∘ T) k
        c₀ (neighbourPool c₀)).run count}[z.1.isSome] =
      if c₀ ∈ blockGoodSet k (fun c => (T c).1.isSome) then 1 else 0 := by
  classical
  set ρ : ((i : ι) → S i) → Bool := fun c => (T c).1.isSome with hρ
  rw [← blockChildren_map, ← blockTableRun, blockTableRun_eq]
  cases hw : (T c₀).1 with
  | none =>
      have hgood : c₀ ∉ blockGoodSet k ρ := by simp [mem_blockGoodSet, hρ, hw]
      rw [ite_eq_right hgood]
      simp
  | some w₀ =>
      have hacc : ρ c₀ = true := by simp [hρ, hw]
      have hdraws : (Fintype.mPi fun j => ProbComp.drawUntil (fun z : Option W × ℕ => z.1.isSome)
          (k j - 1) ((neighbourPool c₀ j).map T)) =
          (fun d j => (d j).map T) <$> Fintype.mPi (blockDraws k ρ c₀) := by
        rw [Fintype.mPi_map]
        congr 1
        funext j
        exact ProbComp.drawUntil_map T _ _ _ _ rfl
      have hlen : ∀ l : List ((i : ι) → S i),
          ((l.map T).filterMap Prod.fst).length = (l.filter ρ).length := fun l => by
        rw [List.filterMap_map, List.length_filterMap_eq_countP, List.countP_eq_length_filter]
        rfl
      simp only
      rw [hdraws, Functor.map_map, prEvent_map]
      simp only [hlen]
      by_cases hgood : c₀ ∈ blockGoodSet k ρ
      · rw [ite_eq_left hgood]
        refine prEvent_eq_one_of_forall_mem_support _ _ fun d hd => ?_
        simp [(forall_length_filter_blockDraws_iff hacc hd).mpr hgood]
      · rw [ite_eq_right hgood]
        refine prEvent_eq_zero_of_forall_mem_support _ _ fun d hd => ?_
        have h : ¬ ∀ j, ((d j).filter ρ).length = k j - 1 := fun h =>
          hgood ((forall_length_filter_blockDraws_iff hacc hd).mp h)
        simp [h]

/-- **The block step with probabilistic children.** Draw a uniform centre and run the block step
on it from the counter `0`, with `child c` giving the result of the child at `c` and its cost. The
result is the centre's result with the collected results of every coordinate, or `none`, together
with the total cost of the children run. -/
@[expose] noncomputable def blockChildStep [SampleableType ((i : ι) → S i)]
    (child : ((i : ι) → S i) → ProbComp (Option W × ℕ)) (k : ι → ℕ) :
    ProbComp (Option (W × (ι → List W)) × ℕ) := do
  let c₀ ← $ᵗ ((i : ι) → S i)
  (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (chargedChild child) k c₀
    (neighbourPool c₀)).run 0

/-- The block step with probabilistic children has the law of drawing a table of all children
first and then running the step at a uniform centre with the table as the child. -/
theorem blockChildStep_eager [SampleableType ((i : ι) → S i)]
    (child : ((i : ι) → S i) → ProbComp (Option W × ℕ)) (k : ι → ℕ) :
    blockChildStep child k =ᵈ
      (do
        let T ← Fintype.mPi child
        let c₀ ← $ᵗ ((i : ι) → S i)
        (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (tableChild ∘ T) k c₀
          (neighbourPool c₀)).run 0) := by
  refine (EvalDistEq.bind_right (m := ProbComp) _ fun c₀ =>
    blockChildren_eager_table child k c₀ (neighbourPool c₀) (fun j => nodup_neighbourPool c₀ j)
      (fun _ _ _ h h' => eq_of_mem_neighbourPool h h') (centre_notMem_neighbourPool c₀) 0).trans ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- With a table of results as the child, the block step at a uniform centre succeeds with the
probability that a uniform challenge is good for the table's successful entries. -/
theorem prEvent_isSome_blockChildren_table_uniform [SampleableType ((i : ι) → S i)]
    (T : ((i : ι) → S i) → Option W × ℕ) (k : ι → ℕ) :
    Pr{let z ← (do
        let c₀ ← $ᵗ ((i : ι) → S i)
        (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (tableChild ∘ T) k c₀
          (neighbourPool c₀)).run 0)}[z.1.isSome] =
      ((blockGoodSet k (fun c => (T c).1.isSome)).card : ℝ≥0∞) /
        Fintype.card ((i : ι) → S i) := by
  classical
  let _ : MeasurableSpace ((i : ι) → S i) := ⊤
  let _ : MeasurableSingletonClass ((i : ι) → S i) := ⟨fun _ => trivial⟩
  rw [prEvent_bind_eq_lintegral_of_discrete, SampleableType.evalDist_uniformSample,
    ProbabilityTheory.lintegral_uniformOn_univ]
  simp only [prEvent_isSome_blockChildren_table]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The success clause.** If a uniformly drawn child succeeds with probability `ε`, the block step
with these children succeeds with a probability `p` such that `ε ≤ κ + (1 - κ) p`, where
`κ = ∑ j, (k j - 1) / |S j|`. -/
theorem prEvent_child_le_blockChildStep [SampleableType ((i : ι) → S i)]
    (child : ((i : ι) → S i) → ProbComp (Option W × ℕ)) (k : ι → ℕ) :
    Pr{let z ← (do let c ← $ᵗ ((i : ι) → S i); child c)}[z.1.isSome] ≤
      (∑ j, ((k j - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (S j) : ℝ≥0∞)) +
        (1 - ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (S j) : ℝ≥0∞)) *
          Pr{let z ← blockChildStep child k}[z.1.isSome] := by
  classical
  have : ∀ j, Nonempty (S j) := fun j => ⟨(Classical.arbitrary ((i : ι) → S i)) j⟩
  let _ : MeasurableSpace (((i : ι) → S i) → Option W × ℕ) := ⊤
  let _ : DiscreteMeasurableSpace (((i : ι) → S i) → Option W × ℕ) := ⟨fun _ => trivial⟩
  set κ : ℝ≥0∞ := ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (S j) : ℝ≥0∞) with hκ
  rw [(Fintype.uniformSample_bind_evalDistEq_mPi child).prEvent_eq,
    (blockChildStep_eager child k).prEvent_eq, prEvent_bind_eq_lintegral_of_discrete,
    prEvent_bind_eq_lintegral_of_discrete]
  simp only [prEvent_isSome_blockChildren_table_uniform]
  simp only [bind_pure_comp, Functor.map_map, SampleableType.prEvent_uniformSample]
  calc ∫⁻ T, ((Finset.univ.filter fun c => (T c).1.isSome = true).card : ℝ≥0∞) /
          Fintype.card ((i : ι) → S i) ∂𝒟[Fintype.mPi child]
      ≤ ∫⁻ T, κ + (1 - κ) * (((blockGoodSet k (fun c => (T c).1.isSome)).card : ℝ≥0∞) /
          Fintype.card ((i : ι) → S i)) ∂𝒟[Fintype.mPi child] := by
        refine lintegral_mono fun T => ?_
        have h := CoordinateWise.div_card_filter_le_affine_pi
          (accept := fun c => (T c).1.isSome = true) k
        rw [hκ]
        simpa [blockGoodSet] using h
    _ = κ + (1 - κ) * ∫⁻ T, ((blockGoodSet k (fun c => (T c).1.isSome)).card : ℝ≥0∞) /
          Fintype.card ((i : ι) → S i) ∂𝒟[Fintype.mPi child] := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ Measurable.of_discrete]

omit [Fintype ι] in
/-- The weight of a neighbour pool is the weight of the other values of the coordinate. -/
theorem listWeight_neighbourPool (f : ((i : ι) → S i) → ℝ≥0) (c : (i : ι) → S i) (j : ι) :
    listWeight f (neighbourPool c j) =
      ∑ y ∈ Finset.univ.erase (c j), f (Function.update c j y) := by
  rw [listWeight, neighbourPool, altPool, List.map_map, Finset.sum_map_toList]
  rfl

/-- **The expected weight of the draws of all accepted centres at one coordinate.** On a table
with acceptance `ρ` and entry weights `w`, the expected weight that the draws at coordinate `j` of
the block step inspect, summed over the accepted centres, is at most `k j - 1` times the total
weight. -/
theorem sum_drawWeight_neighbourPool_le (ρ : ((i : ι) → S i) → Bool)
    (w : ((i : ι) → S i) → ℝ≥0) (k : ι → ℕ) (j : ι) :
    ∑ c, (if ρ c then drawWeight ρ w (k j - 1) (neighbourPool c j) else 0) ≤
      ((k j - 1 : ℕ) : ℝ≥0) * ∑ c, w c := by
  classical
  refine le_trans (Finset.sum_le_sum fun c _ => ?_)
    (sum_accept_column_weight_le (accept := fun c => ρ c = true) j w ((k j - 1 : ℕ) : ℝ≥0))
  by_cases hacc : ρ c = true
  · simp only [hacc, ↓reduceIte]
    refine (drawWeight_le_split ρ w (k j - 1) (neighbourPool c j)).trans (le_of_eq ?_)
    have hcount : (neighbourPool c j).countP ρ + 1 = columnCount (fun c => ρ c = true) j c := by
      rw [countP_neighbourPool]; exact card_hitSet_succ hacc j
    have hc : (columnCount (fun c => ρ c = true) j c - 1 : ℕ) = (neighbourPool c j).countP ρ := by
      omega
    rw [hc, ← hcount, Nat.cast_add, Nat.cast_one, listWeight_neighbourPool,
      listWeight_neighbourPool]
    congr 2
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
        Bool.not_eq_true']
      constructor
      · exact fun h => by simpa using h.2
      · intro h
        refine ⟨fun hy => ?_, by simpa using h⟩
        subst hy
        simp [Function.update_eq_self, hacc] at h
  · simp only [hacc, Bool.false_eq_true, ↓reduceIte, le_refl]

/-- **The cost clause.** If the children cost `expectedCalls (child c)` in expectation, the block
step with these children costs at most `1 + ∑ j, (k j - 1)` times their average cost: the centre's
child, and at every coordinate `j` at most `k j - 1` children in expectation. -/
theorem expectedCalls_blockChildStep_le [SampleableType ((i : ι) → S i)]
    (child : ((i : ι) → S i) → ProbComp (Option W × ℕ)) (k : ι → ℕ) :
    expectedCalls (blockChildStep child k) ≤
      (1 + ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞)) *
        ((∑ c, expectedCalls (child c)) / Fintype.card ((i : ι) → S i)) := by
  classical
  let _ : MeasurableSpace (((i : ι) → S i) → Option W × ℕ) := ⊤
  let _ : DiscreteMeasurableSpace (((i : ι) → S i) → Option W × ℕ) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (Option W) := ⊤
  set N : ℝ≥0∞ := (Fintype.card ((i : ι) → S i) : ℝ≥0∞) with hN
  -- the cost of the step on one table
  have hT : ∀ T : ((i : ι) → S i) → Option W × ℕ,
      expectedCalls (do
          let c₀ ← $ᵗ ((i : ι) → S i)
          (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (tableChild ∘ T) k c₀
            (neighbourPool c₀)).run 0) ≤
        (1 + ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞)) * ((∑ c, ((T c).2 : ℝ≥0∞)) / N) := by
    intro T
    let _ : MeasurableSpace ((i : ι) → S i) := ⊤
    let _ : MeasurableSingletonClass ((i : ι) → S i) := ⟨fun _ => trivial⟩
    rw [expectedCalls_bind, SampleableType.evalDist_uniformSample,
      ProbabilityTheory.lintegral_uniformOn_univ]
    simp only [expectedCalls_blockChildren_table]
    rw [mul_div_assoc']
    refine ENNReal.div_le_div_right ?_ _
    have hsplit : ∀ c : (i : ι) → S i, ((T c).2 : ℝ≥0∞) + (if (T c).1.isSome then
        ∑ j, (drawWeight (fun c => (T c).1.isSome) (fun c => ((T c).2 : ℝ≥0)) (k j - 1)
          (neighbourPool c j) : ℝ≥0∞) else 0) =
        ((T c).2 : ℝ≥0∞) + ∑ j, ((if (T c).1.isSome then
          drawWeight (fun c => (T c).1.isSome) (fun c => ((T c).2 : ℝ≥0)) (k j - 1)
            (neighbourPool c j) else 0 : ℝ≥0) : ℝ≥0∞) := by
      intro c
      split <;> simp
    simp only [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_comm, add_mul, one_mul, Finset.sum_mul]
    refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
    have hB := sum_drawWeight_neighbourPool_le (fun c => (T c).1.isSome)
      (fun c => ((T c).2 : ℝ≥0)) k j
    have hB' := ENNReal.coe_le_coe.mpr hB
    push_cast at hB'
    simpa [Finset.mul_sum] using hB'
  rw [expectedCalls_eq_of_evalDistEq (blockChildStep_eager child k), expectedCalls_bind]
  calc ∫⁻ T, expectedCalls (do
          let c₀ ← $ᵗ ((i : ι) → S i)
          (blockChildren (fun n => StateT.lift (ProbComp.uniformFin n)) (tableChild ∘ T) k c₀
            (neighbourPool c₀)).run 0) ∂𝒟[Fintype.mPi child]
      ≤ ∫⁻ T, (1 + ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞)) * ((∑ c, ((T c).2 : ℝ≥0∞)) / N)
          ∂𝒟[Fintype.mPi child] := lintegral_mono hT
    _ = (1 + ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞)) * ((∑ c, expectedCalls (child c)) / N) := by
        simp only [div_eq_mul_inv]
        rw [lintegral_const_mul _ Measurable.of_discrete,
          lintegral_mul_const _ Measurable.of_discrete,
          lintegral_finsetSum _ fun _ _ => Measurable.of_discrete]
        congr 3
        funext c
        rw [← expectedCalls_eq_of_evalDistEq (Fintype.mPi_map_eval child c),
          expectedCalls_eq_lintegral]
        exact (lintegral_evalDist_map (Fintype.mPi child) (f := fun T => T c)
          Measurable.of_discrete (g := fun z : Option W × ℕ => (z.2 : ℝ≥0∞))
          ((Measurable.of_discrete (f := fun n : ℕ => (n : ℝ≥0∞))).comp measurable_snd)).symm

end OracleComp
