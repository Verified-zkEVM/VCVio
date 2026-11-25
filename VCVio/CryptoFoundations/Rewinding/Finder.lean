/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Basic
public import Mathlib.Data.Fintype.Pi
public import ToMathlib.Control.Monad.Fold

/-!
# Black-box finders for accepting challenge trees

Rounds are indexed by any finite linearly ordered type. A challenge tree assigns a vector to
each branch path, with the challenge at a round depending only on the path through that round.
The finder sees only a Boolean acceptance oracle and its own independent random coins.

The file also collects the facts about the complete-run counter that finder analyses share.
`Rewinding.expectedCalls_bind` and `Rewinding.expectedCalls_bind_le_add` bound the expected counter
after a random choice. `Rewinding.counted_run_add`, `Rewinding.counted_mOfFn` and
`Rewinding.counted_mPi` add up the counters of runs in sequence.

## References

* Attema, Cramer and Kohl, *A compressed Σ-protocol theory for lattices*, CRYPTO 2021.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Rewinding

variable {R : Type} {C : R → Type}

/-- The Boolean oracle deciding acceptance of a complete challenge vector. -/
abbrev accSpec (C : R → Type) : OracleSpec ((r : R) → C r) :=
  rerunSpec ((r : R) → C r) Bool

/-- A challenge tree with `k r` branches at round `r`. The challenge at a round depends only
on branch choices up to and including that round. -/
structure VecTree [LinearOrder R] (C : R → Type) (k : R → ℕ) where
  /-- The challenge vector at a branch path. -/
  leaf : ((r : R) → Fin (k r)) → (r : R) → C r
  /-- Challenge selection respects the order of rounds. -/
  causal : ∀ (p p' : (r : R) → Fin (k r)) (r : R),
    (∀ s, s ≤ r → p s = p' s) → leaf p r = leaf p' r

/-- Sibling challenges at the node reached by the path before round `r`. -/
@[expose] def VecTree.siblings [LinearOrder R] {k : R → ℕ}
    (t : VecTree C k) (p : (r : R) → Fin (k r)) (r : R) : Fin (k r) → C r :=
  fun j => t.leaf (Function.update p r j) r

/-- Every node of the challenge tree satisfies the prescribed sibling predicate. -/
@[expose] def VecTree.IsStructured [LinearOrder R] {k : R → ℕ}
    (nodeOk : (r : R) → (Fin (k r) → C r) → Prop) (t : VecTree C k) : Prop :=
  ∀ p r, nodeOk r (t.siblings p r)

/-- Run a finder against a fixed acceptance function, returning its output and the number of
acceptance-oracle calls. Coin queries and local work are not charged. -/
@[expose] def runFinder {β : Type} (find : OracleComp (unifSpec + accSpec C) β)
    (f : ((r : R) → C r) → Bool) : ProbComp (β × ℕ) :=
  (simulateQ (coins (S := ℕ) + counted f) find).run 0

/-- The complete-run expectation depends only on the natural-valued counter marginal. -/
theorem expectedCalls_eq_lintegral_counter {β : Type} (mx : ProbComp (β × ℕ)) :
    expectedCalls mx = ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> mx] := by
  rw [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
    AddWriterT.costs_def]
  simp only [WriterT.run_mk, Functor.map_map]
  rfl

/-- A pure outcome has its counter as its expected counter. -/
@[simp]
theorem expectedCalls_pure {β : Type} (b : β) (n : ℕ) :
    expectedCalls (pure (b, n) : ProbComp (β × ℕ)) = n := by
  rw [expectedCalls_eq_lintegral_counter]
  simp

/-- The complete-run expectation integrates the counter projection of the joint law. -/
theorem expectedCalls_eq_lintegral {β : Type} [MeasurableSpace β]
    (mx : ProbComp (β × ℕ)) : expectedCalls mx = ∫⁻ z, (z.2 : ℝ≥0∞) ∂𝒟[mx] := by
  rw [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
    AddWriterT.costs_def]
  simp only [WriterT.run_mk, Functor.map_map]
  exact lintegral_evalDist_map mx measurable_snd Measurable.of_discrete

/-- Equal joint output and counter laws have equal expected complete-run counts. -/
theorem expectedCalls_eq_of_evalDistEq {β : Type} {mx my : ProbComp (β × ℕ)}
    (h : mx =ᵈ my) : expectedCalls mx = expectedCalls my := by
  let : MeasurableSpace β := ⊤
  rw [expectedCalls_eq_lintegral, expectedCalls_eq_lintegral, h.evalDist_eq]

/-- The expected counter after a random choice is the average of its conditional expectations. -/
theorem expectedCalls_bind {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : ProbComp α) (f : α → ProbComp (β × ℕ)) :
    expectedCalls (mx >>= f) = ∫⁻ x, expectedCalls (f x) ∂𝒟[mx] := by
  let : MeasurableSpace β := ⊤
  simp only [expectedCalls_eq_lintegral]
  exact lintegral_evalDist_bind_of_discrete mx f (Measurable.of_discrete.comp measurable_snd)

open MeasureTheory in
/-- A continuation that adds at most `B` to the counter adds at most `B` to the expected
counter. -/
theorem expectedCalls_bind_le_add {β γ : Type} (mx : ProbComp (β × ℕ))
    (f : β × ℕ → ProbComp (γ × ℕ)) (B : ℕ)
    (hf : ∀ z ∈ support mx, ∀ y ∈ support (f z), y.2 ≤ z.2 + B) :
    expectedCalls (mx >>= f) ≤ expectedCalls mx + B := by
  let : MeasurableSpace (β × ℕ) := ⊤
  rw [expectedCalls_bind]
  calc
    (∫⁻ z, expectedCalls (f z) ∂𝒟[mx]) ≤ ∫⁻ z, ((z.2 : ℝ≥0∞) + B) ∂𝒟[mx] := by
      apply lintegral_mono_ae
      apply evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
      intro z hz
      rw [expectedCalls_eq_lintegral_counter]
      calc
        (∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> f z]) ≤
            ∫⁻ _n, ((z.2 : ℝ≥0∞) + B) ∂𝒟[Prod.snd <$> f z] := by
          apply lintegral_mono_ae
          apply evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
          intro n hn
          rw [support_map] at hn
          obtain ⟨y, hy, rfl⟩ := hn
          exact_mod_cast hf z hz y hy
        _ = ((z.2 : ℝ≥0∞) + B) * 𝒟[Prod.snd <$> f z] Set.univ := lintegral_const _
        _ ≤ (z.2 : ℝ≥0∞) + B := mul_le_of_le_one_right zero_le (evalDist_apply_univ_le_one _)
    _ = (∫⁻ z, (z.2 : ℝ≥0∞) ∂𝒟[mx]) + B * 𝒟[mx] Set.univ := by
      rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ expectedCalls mx + B := by
      rw [expectedCalls_eq_lintegral_counter, lintegral_evalDist_map_of_discrete]
      gcongr
      exact mul_le_of_le_one_right zero_le (evalDist_apply_univ_le_one mx)

/-- Changing only the output preserves the expected complete-run counter. -/
theorem expectedCalls_map_output {α β : Type} (g : α → β) (mx : ProbComp (α × ℕ)) :
    expectedCalls ((fun z => (g z.1, z.2)) <$> mx) = expectedCalls mx := by
  simp only [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
    AddWriterT.costs_def, WriterT.run_mk, Functor.map_map]

/-- An initial counter offset is added to the final counter without changing any answers. -/
theorem counted_run_add {Q α β : Type} (f : Q → α)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (count offset : ℕ) :
    (simulateQ (coins (S := ℕ) + counted f) alg).run (count + offset) =
      (fun z => (z.1, z.2 + offset)) <$>
        (simulateQ (coins (S := ℕ) + counted f) alg).run count := by
  induction alg using OracleComp.inductionOn generalizing count with
  | pure a => simp
  | query_bind q next ih =>
    cases q with
    | inl q =>
      simp only [coins] at ih
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
        StateT.run_bind, coins, QueryImpl.liftTarget_apply_run, QueryImpl.ofLift_apply,
        bind_map_left, map_bind, ih]
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
        StateT.run_bind, counted_apply, StateT.run_modify, StateT.run_pure, pure_bind]
      simpa only [Nat.add_right_comm count offset 1] using ih (f q) (count + 1)

/-- Running a finite sequence of programs against a fixed acceptance function adds up their
counters: each member runs from the counter its predecessors leave, and its law does not depend on
that starting value except through the offset (`Rewinding.counted_run_add`). -/
theorem counted_mOfFn {Q α β : Type} (f : Q → α) :
    ∀ {n : ℕ} (g : Fin n → OracleComp (unifSpec + rerunSpec Q α) β) (count : ℕ),
      (simulateQ (coins (S := ℕ) + counted f) (Fin.mOfFn n g)).run count =
        (fun v : Fin n → β × ℕ => (fun i => (v i).1, count + ∑ i, (v i).2)) <$>
          Fin.mOfFn n fun i => (simulateQ (coins (S := ℕ) + counted f) (g i)).run 0
  | 0, g, count => by
      simp only [Fin.mOfFn, simulateQ_pure, StateT.run_pure, map_pure, Finset.univ_eq_empty,
        Finset.sum_empty, add_zero]
      congr 2
      funext i
      exact i.elim0
  | n + 1, g, count => by
      have hrest := fun c => counted_mOfFn f (fun i : Fin n => g i.succ) c
      simp only [Fin.mOfFn, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        map_bind]
      rw [show count = 0 + count from (zero_add count).symm, counted_run_add, zero_add,
        bind_map_left]
      refine bind_congr fun p => ?_
      simp only [hrest, bind_map_left, map_pure]
      refine bind_congr fun v => ?_
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      congr 2
      · funext i
        refine Fin.cases rfl (fun _ => rfl) i
      · ring

/-- `Rewinding.counted_mOfFn` over a finite index type. -/
theorem counted_mPi {Q α β : Type} (f : Q → α) {ι : Type} [Fintype ι]
    (g : ι → OracleComp (unifSpec + rerunSpec Q α) β) (count : ℕ) :
    (simulateQ (coins (S := ℕ) + counted f) (Fintype.mPi g)).run count =
      (fun v : ι → β × ℕ => (fun i => (v i).1, count + ∑ i, (v i).2)) <$>
        Fintype.mPi fun i => (simulateQ (coins (S := ℕ) + counted f) (g i)).run 0 := by
  simp only [Fintype.mPi, simulateQ_map, StateT.run_map, counted_mOfFn, Functor.map_map]
  congr 1
  funext v
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  congr 1
  rw [Equiv.symm_symm]
  exact (Equiv.sum_comp (Fintype.equivFin ι) fun k => (v k).2).symm

/-- Fraction of complete challenge vectors accepted by `f`. -/
@[expose] noncomputable def acceptRate [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    (f : ((r : R) → C r) → Bool) : ℝ≥0∞ :=
  ((Finset.univ.filter fun c => f c = true).card : ℝ≥0∞) /
    (Fintype.card ((r : R) → C r) : ℝ≥0∞)

/-- A black-box finder with output type `Out`, output predicate `good`, error `κ` and cost `T`.
Against every acceptance function `f`, every returned output satisfies `good f`, the acceptance
rate `ε` of `f` and the success probability `p` satisfy `ε ≤ κ + (1 - κ) * p`, and the expected
number of acceptance-oracle calls is at most `T`, counted over complete runs whether or not they
succeed. Coin queries and local work are not charged.

The contract does not fix the shape of the output: a tree finder returns a `VecTree`
(`Rewinding.IsTreeFinder`), and other extractors return other configurations of accepting
challenge vectors. The transfer to frozen reruns (`Rewinding.ResetPolicy.finder_bounds`) uses only
the success and cost fields. -/
structure IsFinder [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)] {Out : Type}
    (good : (((r : R) → C r) → Bool) → Out → Prop)
    (find : OracleComp (unifSpec + accSpec C) (Option Out)) (κ T : ℝ≥0∞) : Prop where
  /-- Every returned output satisfies the output predicate for the acceptance function. -/
  sound : ∀ f, ∀ z ∈ support (runFinder find f), ∀ o, z.1 = some o → good f o
  /-- The acceptance rate is at most the error plus its complement times the success
  probability, uniformly over all acceptance functions. -/
  success : ∀ f, acceptRate f ≤ κ + (1 - κ) * Pr{let z ← runFinder find f}[z.1.isSome]
  /-- Complete-run cost is bounded without conditioning on success. -/
  cost : ∀ f, expectedCalls (runFinder find f) ≤ T

/-- A finder succeeds with probability at least the acceptance rate minus its error. -/
theorem IsFinder.acceptRate_sub_le [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)] {Out : Type}
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) (f : ((r : R) → C r) → Bool) :
    acceptRate f - κ ≤ Pr{let z ← runFinder find f}[z.1.isSome] :=
  tsub_le_iff_left.mpr ((h.success f).trans
    (add_le_add le_rfl (mul_le_of_le_one_left zero_le tsub_le_self)))

/-- A black-box tree finder with branching factors `k`, node predicate `nodeOk`, error `κ` and
cost `T`: a finder (`Rewinding.IsFinder`) whose every returned tree is structured and accepting.

Every branching factor is at least one. At `k r = 0` there are no branch paths, so every tree is
vacuously structured and accepting, and a finder that returns a tree without calling the oracle
would meet the contract at error `0` and cost `0`. -/
structure IsTreeFinder [Fintype R] [LinearOrder R] [∀ r, Fintype (C r)] (k : R → ℕ)
    (nodeOk : (r : R) → (Fin (k r) → C r) → Prop)
    (find : OracleComp (unifSpec + accSpec C) (Option (VecTree C k))) (κ T : ℝ≥0∞) : Prop
    extends IsFinder (fun f (t : VecTree C k) => t.IsStructured nodeOk ∧ ∀ p, f (t.leaf p) = true)
      find κ T where
  /-- Every round has at least one branch, so the leaves of a returned tree are not vacuous. -/
  one_le : ∀ r, 1 ≤ k r

/-- Threshold knowledge error `1 − ∏ᵣ (1 − (kᵣ − 1)/|Cᵣ|)`: the knowledge error of a protocol
that is special sound with threshold `k r` and challenge set `C r` in each round (Attema, Cramer
and Kohl, Remark 1, eq. (3)). -/
@[expose] noncomputable def thresholdError [Fintype R]
    (C : R → Type) [∀ r, Fintype (C r)] (k : R → ℕ) : ℝ≥0∞ :=
  1 - ∏ r, (1 - ((k r - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (C r) : ℝ≥0∞))

end Rewinding
