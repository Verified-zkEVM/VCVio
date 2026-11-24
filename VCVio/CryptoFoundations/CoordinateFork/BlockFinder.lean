/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.BlockOperational
public import VCVio.CryptoFoundations.CoordinateFork.Finder

/-!
# The coordinate-wise finder with an alphabet and a threshold per coordinate

`blockFinder k` asks a Boolean acceptance oracle about complete challenges `(j : ι) → S j`. It draws
a challenge, asks whether it is accepted, and on acceptance collects `k j - 1` further accepted
neighbours at every coordinate `j` with `coordNeighbours`, drawing each coordinate's neighbours
without replacement. Every oracle call is charged, including the rejected ones. It returns the block
star the neighbours form with the challenge if every coordinate supplied them.

`isFinder_blockFinder` states that this meets the finder contract of the rewinding framework, with
error `κ = ∑ j, (k j - 1) / |S j|` and at most `1 + ∑ j, (k j - 1)` acceptance-oracle calls in
expectation. Every returned set is a block star of accepted challenges. The framework carries the
success and cost guarantees to frozen reruns of a prover. With one alphabet and one threshold, its
law against a fixed acceptance function is the law of `coordFinder` (`runFinder_blockFinder_const`).

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

/-- **The block extractor as a black-box finder.** Draw a challenge `c₀` and ask the acceptance
oracle about it. On acceptance, collect `k j - 1` accepted coordinate-`j` neighbours of `c₀` for
every `j`, and return the block star they form with `c₀` if every coordinate supplied them. -/
@[expose] noncomputable def blockFinder [SampleableType ((i : ι) → S i)] (k : ι → ℕ) :
    OracleComp (unifSpec + Rewinding.accSpec S) (Option (Finset ((i : ι) → S i))) := do
  let c₀ ← OracleComp.liftComp ($ᵗ ((i : ι) → S i)) (unifSpec + Rewinding.accSpec S)
  let b ← (Rewinding.accSpec S).query c₀
  if b then do
    let d ← Fintype.mPi fun j => coordNeighbours (k j) c₀ j
    let N : ι → Finset ((i : ι) → S i) := fun j => (d j).toFinset
    pure (if ∀ j, (N j).card = k j - 1 then some (neighbourFamily c₀ N) else none)
  else pure none

/-- Against a fixed acceptance function, the finder's output and its count of acceptance-oracle
calls have exactly the law of `blockForkOp`: the table loop's lookups are the finder's oracle
calls. -/
theorem runFinder_blockFinder [SampleableType ((i : ι) → S i)] (k : ι → ℕ)
    (ρ : ((i : ι) → S i) → Bool) :
    Rewinding.runFinder (blockFinder k) ρ = blockForkOp k ρ := by
  have hcol : ∀ j c₀, (simulateQ (Rewinding.coins (S := ℕ) + Rewinding.counted ρ)
      (coordNeighbours (k j) c₀ j)).run 0 =
        (fun d : List ((i : ι) → S i) => (d.filter ρ, d.length)) <$> blockDraws k ρ c₀ j := by
    intro j c₀
    rw [coordNeighbours, Rewinding.collectChildren_counted ρ _ (k j - 1) _ rfl 0]
    simp [blockDraws]
  have hcoins : ∀ {α : Type} (oa : ProbComp α) (s : ℕ),
      (simulateQ (Rewinding.coins (S := ℕ)) oa).run s = (·, s) <$> oa := by
    intro α oa s
    simp [Rewinding.coins, simulateQ_liftTarget]
  simp only [Rewinding.runFinder, blockFinder, blockForkOp, simulateQ_bind, StateT.run_bind,
    QueryImpl.simulateQ_add_liftComp_left, hcoins, bind_map_left]
  refine bind_congr fun c₀ => ?_
  simp only [QueryImpl.simulateQ_add_liftM_query_right, Rewinding.counted, StateT.run_bind,
    StateT.run_modify, StateT.run_pure, pure_bind, zero_add]
  cases hacc : ρ c₀ with
  | false => simp [blockForkOpAt, hacc]
  | true =>
      simp only [ite_true, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        Rewinding.counted_mPi, hcol, ← Fintype.mPi_map, bind_map_left, Functor.map_map,
        blockForkOpAt, hacc, ite_true]
      refine bind_congr fun d => ?_
      simp only [blockCollected]
      by_cases h : ∀ j, ((d j).filter ρ).toFinset.card = k j - 1
      · simp only [h, implies_true, ↓reduceIte]
        rfl
      · simp only [h, ↓reduceIte]

/-- **The block extractor meets the black-box finder contract**, at error
`κ = ∑ j, (k j - 1) / |S j|` and at most `1 + ∑ j, (k j - 1)` acceptance-oracle calls in
expectation. Every returned set is a block star of accepted challenges.

The success field is the affine form `ε ≤ κ + (1 - κ) p`
(`CoordinateWise.div_card_filter_le_affine_pi`), so `Rewinding.ResetPolicy.finder_bounds`
carries the success and cost guarantees to frozen reruns of a prover. -/
theorem isFinder_blockFinder [SampleableType ((i : ι) → S i)] [∀ j, Nonempty (S j)]
    (k : ι → ℕ) :
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
    rw [runFinder_blockFinder, prEvent_isSome_blockForkOp]
    have h := CoordinateWise.div_card_filter_le_affine_pi (accept := fun c => ρ c = true) k
    simpa [Rewinding.acceptRate, blockGoodSet] using h
  cost ρ := by
    rw [Rewinding.expectedCalls_eq_lintegral_counter, runFinder_blockFinder]
    exact lintegral_cost_blockForkOp_le k ρ

/-- With one alphabet and one threshold, the block loop is the coordinate-wise loop. -/
theorem blockForkOp_const {T : Type} [DecidableEq T] [Fintype T] [SampleableType (ι → T)] (k : ℕ)
    (ρ : (ι → T) → Bool) :
    blockForkOp (S := fun _ => T) (fun _ => k) ρ = coordForkOp k ρ := by
  unfold blockForkOp coordForkOp
  exact bind_congr fun c₀ => blockForkOpAt_const k ρ c₀

/-- With one alphabet and one threshold, the block finder has the law of `coordFinder` against
every acceptance function. -/
theorem runFinder_blockFinder_const {T : Type} [DecidableEq T] [Fintype T]
    [SampleableType (ι → T)] (k : ℕ) (ρ : (ι → T) → Bool) :
    Rewinding.runFinder (blockFinder (S := fun _ => T) (fun _ => k)) ρ =
      Rewinding.runFinder (coordFinder k) ρ := by
  rw [runFinder_blockFinder, runFinder_coordFinder, blockForkOp_const]

end OracleComp
