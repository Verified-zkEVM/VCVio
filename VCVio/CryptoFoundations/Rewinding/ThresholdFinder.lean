/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.ThresholdAnalysis
public import VCVio.CryptoFoundations.Rewinding.FinderBridge

/-!
# The ACK threshold tree finder

For rounds indexed by `Fin n`, the explicit computable `thresholdFinder` returns only accepting
trees with pairwise distinct siblings, for every choice of thresholds `kᵢ`. Its unconditional
expected number of acceptance-oracle calls is at most `∏ᵢ kᵢ`, including failed attempts.

For thresholds `1 ≤ kᵢ ≤ |Cᵢ|`, write `κ = 1 − ∏ᵢ (1 − (kᵢ − 1)/|Cᵢ|)`. Against every Boolean
acceptance function with acceptance rate `ε`, its success probability `p` satisfies
`ε ≤ κ + (1 − κ) p`, so in particular `p ≥ ε − κ`.

These are complete-run call bounds; coin queries, constructing challenge pools and processing
trees are not charged. `ResetPolicy.finder_bounds` transfers the guarantees to frozen reruns, and
`ResetPolicy.finder_bounds_honest` states them with the honest acceptance probability.

## References

* Attema, Cramer and Kohl, *A compressed Σ-protocol theory for lattices*, CRYPTO 2021,
  Lemma 5 and Sections 3.2 and 3.3.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Rewinding

/-! ## Unconditional cost induction -/

/-- A threshold finder on explicit challenge pools makes at most the product of its branching
factors many acceptance-oracle calls in expectation, without conditioning on success. -/
theorem expectedCalls_thresholdFinderWithPools (n : ℕ) (C : Fin n → Type)
    (k : Fin n → ℕ) (pools : (i : Fin n) → List (C i))
    (f : ((i : Fin n) → C i) → Bool) :
    expectedCalls (runFinder (thresholdFinderWithPools n C k pools) f) ≤
      ∏ i, (k i : ℝ≥0∞) := by
  induction n with
  | zero =>
      simp [runFinder, simulateQ_counted_thresholdFinderWithPools, thresholdProgram,
        counted, StateT.run_modify, expectedCalls, AddWriterT.expectedCostNat,
        AddWriterT.expectedCost, AddWriterT.costs_def]
  | succ n ih =>
      rw [runFinder_thresholdFinderWithPools_succ]
      rw [expectedCalls_map_output
        (fun children : Option (List _) => children.bind assembleChildren)]
      let child := fun c : C 0 =>
        (fun z => (z.1.map (fun t => (c, t)), z.2)) <$>
          runFinder (thresholdFinderWithPools n (fun i => C i.succ)
            (fun i => k i.succ) (fun i => pools i.succ)) (fun q => f (Fin.cons c q))
      let T : ℝ≥0∞ := ∏ i : Fin n, (k i.succ : ℝ≥0∞)
      have hchild : ∀ c, expectedCalls (child c) ≤ T := by
        intro c
        dsimp only [child]
        rw [expectedCalls_map_output (Option.map (fun t => (c, t)))]
        exact ih _ _ _ _
      apply (expectedCalls_thresholdChildren child (k 0) (pools 0)).trans
      have hsum : ((pools 0).map fun c => expectedCalls (child c)).sum ≤
          ((pools 0).length : ℝ≥0∞) * T := by
        have h := List.sum_le_length_nsmul ((pools 0).map fun c => expectedCalls (child c)) T
          (by
            intro x hx
            obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
            exact hchild c)
        simpa only [List.length_map, nsmul_eq_mul] using h
      rw [Fin.prod_univ_succ]
      change (k 0 : ℝ≥0∞) * ((pools 0).map fun c => expectedCalls (child c)).sum /
        (pools 0).length ≤ (k 0 : ℝ≥0∞) * T
      by_cases hp : (pools 0).length = 0
      · have hnil := List.length_eq_zero_iff.mp hp
        simp [hnil]
      · have hp0 : ((pools 0).length : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp
        have hpt : ((pools 0).length : ℝ≥0∞) ≠ ⊤ := by finiteness
        calc
          _ ≤ (k 0 : ℝ≥0∞) * (((pools 0).length : ℝ≥0∞) * T) / (pools 0).length := by
            gcongr
          _ = (k 0 : ℝ≥0∞) * T := by
            rw [div_eq_mul_inv]
            calc
              _ = (k 0 : ℝ≥0∞) * T *
                  (((pools 0).length : ℝ≥0∞) * ((pools 0).length : ℝ≥0∞)⁻¹) := by ring
              _ = _ := by rw [ENNReal.mul_inv_cancel hp0 hpt, mul_one]

/-- The computable threshold finder has unconditional expected complete-run count at most
the product of the requested per-round thresholds. -/
theorem expectedCalls_thresholdFinder {n : ℕ} (C : Fin n → Type)
    [∀ i, SampleableType (C i)] [∀ i, DecidableEq (C i)] (k : Fin n → ℕ)
    (f : ((i : Fin n) → C i) → Bool) :
    expectedCalls (runFinder (thresholdFinder C k) f) ≤ ∏ i, (k i : ℝ≥0∞) :=
  expectedCalls_thresholdFinderWithPools n C k (fun i => challengePool (C i)) f


/-! ## Success probability induction -/

private theorem average_affine {C : Type} [Fintype C] [Nonempty C]
    (b d : ℝ≥0∞) (p : C → ℝ≥0∞) :
    (∑ c, (b + d * p c)) / Fintype.card C =
      b + d * ((∑ c, p c) / Fintype.card C) := by
  have hN : (Fintype.card C : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv, add_mul]
  rw [mul_comm (Fintype.card C : ℝ≥0∞) b, mul_assoc b,
    ENNReal.mul_inv_cancel hN (by finiteness), mul_one]
  rw [mul_assoc]

/-- The affine success estimate for the explicit recursive threshold finder: the acceptance rate
is at most `κ + (1 − κ) p` for the threshold error `κ` and success probability `p`, the sharper
form of Lemma 5 given in Attema, Cramer and Kohl, Section 3.3. -/
theorem thresholdFinder_success_scaled {n : ℕ} (C : Fin n → Type)
    [∀ i, Fintype (C i)] [∀ i, SampleableType (C i)] [∀ i, DecidableEq (C i)]
    (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i ∧ k i ≤ Fintype.card (C i))
    (f : ((i : Fin n) → C i) → Bool) :
    acceptRate f ≤ thresholdError C k + (1 - thresholdError C k) *
      Pr{let z ← runFinder (thresholdFinder C k) f}[z.1.isSome] := by
  induction n with
  | zero =>
    have hrun : runFinder (thresholdFinder C k) f =
        pure (if f (fun i => Fin.elim0 i) then some (VecTree.empty C k) else none, 1) := by
      rw [thresholdFinder, runFinder, simulateQ_counted_thresholdFinderWithPools,
        thresholdProgram]
      simp [counted]
    rw [hrun]
    have he : (default : (i : Fin 0) → C i) = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
    cases hf : f (fun i => Fin.elim0 i) with
    | false => simp [thresholdError, acceptRate, he, hf]
    | true =>
      have hcard : ({c ∈ ({fun i => Fin.elim0 i} : Finset ((i : Fin 0) → C i)) |
          f c = true}).card ≤ 1 := (Finset.card_filter_le _ _).trans (by simp)
      simpa [thresholdError, acceptRate, he, hf] using hcard
  | succ n ih =>
    let tail := fun c : C 0 =>
      runFinder (thresholdFinder (fun i : Fin n => C i.succ) (fun i => k i.succ))
        (fun q => f (Fin.cons c q))
    let p := fun c : C 0 => Pr{let z ← tail c}[z.1.isSome]
    let child := fun c : C 0 =>
      (fun z => (z.1.map (fun t => (c, t)), z.2)) <$>
        runFinder (thresholdFinder (fun i : Fin n => C i.succ) (fun i => k i.succ))
          (fun q => f (Fin.cons c q))
    let node := (thresholdChildren (fun j => StateT.lift (ProbComp.uniformFin j))
      (chargedChild child) (k 0) (challengePool (C 0))).run 0
    have hlaw : runFinder (thresholdFinder C k) f =
        (fun z => (z.1.bind assembleChildren, z.2)) <$> node :=
      runFinder_thresholdFinderWithPools_succ n C k _ f
    have hprob : Pr{let z ← runFinder (thresholdFinder C k) f}[z.1.isSome] =
        Pr{let z ← node}[z.1.isSome] := by
      rw [hlaw]
      apply prEvent_assembleChildren
      exact length_thresholdChildren_run ProbComp.uniformFin (chargedChild child)
        (k 0) (challengePool (C 0)) 0
    have hstep := thresholdChildren_success_scaled child (k 0) (challengePool (C 0)) (hk 0).1
    simp only [sum_challengePool, length_challengePool, child, prEvent_map,
      Option.isSome_map] at hstep
    let a : ℝ≥0∞ := ((k 0 - 1 : ℕ) : ℝ≥0∞) / Fintype.card (C 0)
    let b := thresholdError (fun i : Fin n => C i.succ) (fun i => k i.succ)
    have htail : ∀ c : C 0, acceptRate (fun q => f (Fin.cons c q)) ≤
        b + (1 - b) * p c := by
      intro c
      exact ih _ _ (fun i => hk i.succ) _
    rw [hprob, thresholdError_cons C k (hk 0).1 (hk 0).2]
    apply affine_error_compose (thresholdError_ratio_le_one (hk 0).1 (hk 0).2)
      (thresholdError_le_one _ _)
    calc
      acceptRate f = (∑ c : C 0, acceptRate (fun q => f (Fin.cons c q))) /
          Fintype.card (C 0) := acceptRate_cons f
      _ ≤ (∑ c : C 0, (b + (1 - b) * p c)) / Fintype.card (C 0) :=
        by
          apply ENNReal.div_le_div_right
          exact Finset.sum_le_sum (fun c _ => htail c)
      _ = b + (1 - b) * ((∑ c : C 0, p c) / Fintype.card (C 0)) :=
        average_affine _ _ _
      _ ≤ b + (1 - b) * (a + (1 - a) * Pr{let z ← node}[z.1.isSome]) :=
        by
          apply add_le_add le_rfl
          exact mul_le_mul' le_rfl hstep


/-! ## Tree-finder contract -/

/-- The explicit ACK threshold finder satisfies the black-box tree-finder contract with
multiplicative threshold error and unconditional product cost. -/
theorem isTreeFinder_thresholdFinder {n : ℕ} (C : Fin n → Type)
    [∀ i, Fintype (C i)] [∀ i, SampleableType (C i)] [∀ i, DecidableEq (C i)]
    (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i ∧ k i ≤ Fintype.card (C i)) :
    IsTreeFinder k (fun _ ch => Function.Injective ch) (thresholdFinder C k)
      (thresholdError C k) (∏ i, (k i : ℝ≥0∞)) where
  one_le i := (hk i).1
  sound := thresholdFinder_sound C k
  success := thresholdFinder_success_scaled C k hk
  cost := expectedCalls_thresholdFinder C k

end Rewinding
