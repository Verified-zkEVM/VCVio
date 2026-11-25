/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.BlockOperational
public import VCVio.CryptoFoundations.Rewinding.FinderBridge
public import VCVio.CryptoFoundations.Rewinding.BlockRound

/-!
# The coordinate-wise finder with an alphabet and a threshold per coordinate

`blockFinder k` asks a Boolean acceptance oracle about complete challenges `(j : ι) → S j`. It draws
a challenge, asks whether it is accepted, and on acceptance collects `k j - 1` further accepted
neighbours at every coordinate `j`, drawing each coordinate's neighbours without replacement. It is
the block step `Rewinding.blockChildren` with the acceptance oracle as the child. Every oracle call
is charged, including the rejected ones. It returns the block star the neighbours form with the
challenge if every coordinate supplied them.

`isFinder_blockFinder` states that this meets the finder contract of the rewinding framework, with
error `κ = ∑ j, (k j - 1) / |S j|` and at most `1 + ∑ j, (k j - 1)` acceptance-oracle calls in
expectation. Every returned set is a block star of accepted challenges. The framework carries the
success and cost guarantees to frozen reruns of a prover. With one alphabet and one threshold it
is `coordFinder` (`CoordinateFork/Finder.lean`).

## References

* [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
    Asymptotic and Concrete Efficiency*](https://eprint.iacr.org/2023/846)
-/

public section

open Finset CoordinateWise OracleComp OracleSpec ProbComp
open scoped ENNReal

namespace OracleComp

variable {ι : Type} [DecidableEq ι] [Fintype ι] {S : ι → Type} [∀ j, DecidableEq (S j)]
  [∀ j, Fintype (S j)]

/-- **The block extractor as a black-box finder.** Draw a challenge `c₀` and run the block step
(`Rewinding.blockChildren`) with the acceptance oracle as the child: ask about `c₀` and, on
acceptance, collect `k j - 1` accepted coordinate-`j` neighbours of `c₀` for every `j`. Return the
block star they form with `c₀` if every coordinate supplied them. -/
@[expose] noncomputable def blockFinder [SampleableType ((i : ι) → S i)] (k : ι → ℕ) :
    OracleComp (unifSpec + Rewinding.accSpec S) (Option (Finset ((i : ι) → S i))) := do
  let c₀ ← OracleComp.liftComp ($ᵗ ((i : ι) → S i)) (unifSpec + Rewinding.accSpec S)
  let z ← Rewinding.blockChildren (fun n => (unifSpec.query n)) Rewinding.acceptanceChild k c₀
    (neighbourPool c₀)
  pure (z.map fun p => neighbourFamily c₀ fun j => (p.2 j).toFinset)

/-- Against a fixed acceptance function, the finder's output and its count of acceptance-oracle
calls have exactly the law of `blockForkOp`: the table loop's lookups are the finder's oracle
calls. -/
theorem runFinder_blockFinder [SampleableType ((i : ι) → S i)] (k : ι → ℕ)
    (ρ : ((i : ι) → S i) → Bool) :
    Rewinding.runFinder (blockFinder k) ρ = blockForkOp k ρ := by
  have hcol : ∀ j c₀, (simulateQ (Rewinding.coins (S := ℕ) + Rewinding.counted ρ)
      (Rewinding.collectChildren (fun n => (unifSpec.query n)) Rewinding.acceptanceChild
        (k j - 1) (neighbourPool c₀ j))).run 0 =
        (fun d : List ((i : ι) → S i) => (d.filter ρ, d.length)) <$> blockDraws k ρ c₀ j := by
    intro j c₀
    rw [Rewinding.collectChildren_counted ρ _ (k j - 1) _ rfl 0]
    simp [blockDraws]
  have hcoins : ∀ {α : Type} (oa : ProbComp α) (s : ℕ),
      (simulateQ (Rewinding.coins (S := ℕ)) oa).run s = (·, s) <$> oa := by
    intro α oa s
    simp [Rewinding.coins, simulateQ_liftTarget]
  simp only [Rewinding.runFinder, blockFinder, blockForkOp, simulateQ_bind, StateT.run_bind,
    QueryImpl.simulateQ_add_liftComp_left, hcoins, bind_map_left]
  refine bind_congr fun c₀ => ?_
  simp only [Rewinding.blockChildren, Rewinding.acceptanceChild, simulateQ_bind, simulateQ_pure,
    QueryImpl.simulateQ_add_liftM_query_right, Rewinding.counted_apply, StateT.run_bind,
    StateT.run_modify, StateT.run_pure, pure_bind, zero_add, bind_assoc]
  cases hacc : ρ c₀ with
  | false => simp [blockForkOpAt, hacc]
  | true =>
      simp only [ite_true, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        Rewinding.counted_mPi, hcol, ← Fintype.mPi_map, bind_map_left, Functor.map_map,
        blockForkOpAt, hacc, ite_true]
      rw [bind_assoc]
      refine bind_congr fun d => ?_
      rw [pure_bind]
      by_cases h : ∀ j, ((d j).filter ρ).length = k j - 1
      · simp only [h, implies_true, ↓reduceIte, Option.map_some]
        rfl
      · simp only [h, ↓reduceIte, Option.map_none]

/-- **The block extractor meets the black-box finder contract**, at error
`κ = ∑ j, (k j - 1) / |S j|` and at most `1 + ∑ j, (k j - 1)` acceptance-oracle calls in
expectation. Every returned set is a block star of accepted challenges.

The success field is the affine form `ε ≤ κ + (1 - κ) p`
(`CoordinateWise.div_card_filter_le_affine_pi`), so `Rewinding.ResetPolicy.finder_bounds`
carries the success and cost guarantees to frozen reruns of a prover. -/
theorem isFinder_blockFinder [SampleableType ((i : ι) → S i)] (k : ι → ℕ) :
    Rewinding.IsFinder (fun ρ X => IsBlockSpecialSound k X ∧ ∀ c ∈ X, ρ c = true)
      (blockFinder (S := S) k)
      (∑ j, ((k j - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (S j) : ℝ≥0∞))
      (1 + ∑ j, ((k j - 1 : ℕ) : ℝ≥0∞)) where
  sound ρ z hz X hX := by
    rw [runFinder_blockFinder] at hz
    obtain ⟨o, n⟩ := z
    obtain rfl : o = some X := hX
    exact blockForkOp_success hz
  success ρ := by
    have : ∀ j, Nonempty (S j) := fun j => ⟨(Classical.arbitrary ((i : ι) → S i)) j⟩
    rw [runFinder_blockFinder, prEvent_isSome_blockForkOp]
    have h := CoordinateWise.div_card_filter_le_affine_pi (accept := fun c => ρ c = true) k
    simpa [Rewinding.acceptRate, blockGoodSet] using h
  cost ρ := by
    rw [Rewinding.expectedCalls_eq_lintegral_counter, runFinder_blockFinder]
    exact lintegral_cost_blockForkOp_le k ρ

end OracleComp
