/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.CoordinateFork.BlockFinder
public import VCVio.CryptoFoundations.CoordinateFork.Operational

/-!
# Figure 11 of Fenzi–Moghaddas–Nguyen as a black-box finder

`coordFinder k` asks a Boolean acceptance oracle about complete challenge vectors `ι → S`: it
draws a challenge, asks whether it accepts, and on acceptance collects `k - 1` further accepting
neighbours in every coordinate, drawing each coordinate's replacement values without replacement.
Every oracle call is charged, including the rejected ones. It is the block finder `blockFinder` with
one alphabet and the threshold `k` at every coordinate, so its law and its finder contract are the
block ones at a constant threshold.
-/

public section

open Finset CoordinateWise OracleComp OracleSpec ProbComp
open scoped ENNReal

namespace OracleComp

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]

/-- **Figure 11 of Fenzi–Moghaddas–Nguyen as a black-box finder.** Draw a challenge `c₀` and ask
the acceptance oracle about it. On acceptance, collect `k - 1` accepting coordinate-`j` neighbours
of `c₀` for every `j`, and return the coordinate-wise special sound set they form with `c₀` if
every coordinate supplied them. -/
@[expose] noncomputable def coordFinder [SampleableType (ι → S)] (k : ℕ) :
    OracleComp (unifSpec + Rewinding.accSpec (fun _ : ι => S)) (Option (Finset (ι → S))) :=
  blockFinder (S := fun _ => S) fun _ => k

/-- Against a fixed acceptance function, the finder's output and its count of acceptance-oracle
calls have exactly the law of `coordForkOp`: the table loop's lookups are the finder's oracle
calls. -/
theorem runFinder_coordFinder [SampleableType (ι → S)] (k : ℕ) (ρ : (ι → S) → Bool) :
    Rewinding.runFinder (coordFinder k) ρ = coordForkOp k ρ := by
  rw [coordFinder, runFinder_blockFinder, blockForkOp_const]

/-- **Figure 11 of Fenzi–Moghaddas–Nguyen meets the black-box finder contract**, at error
`κ = ℓ (k - 1) / N` and at most `1 + ℓ (k - 1)` acceptance-oracle calls in expectation, where
`ℓ = Fintype.card ι` and `N = Fintype.card S`. Every returned set is coordinate-wise `k`-special
sound and accepting.

The success field is the affine form `ε ≤ κ + (1 - κ) p`
(`CoordinateWise.div_card_filter_le_affine`), so `Rewinding.ResetPolicy.finder_bounds` carries the
success and cost guarantees to frozen reruns of a prover. The threshold finder
(`Rewinding.isTreeFinder_thresholdFinder`) has the smaller error `1 - (1 - (k - 1) / N) ^ ℓ` on
`ℓ` rounds, at the cost of `k ^ ℓ` runs. -/
theorem isFinder_coordFinder [SampleableType (ι → S)] (k : ℕ) :
    Rewinding.IsFinder (fun ρ X => IsCoordSpecialSound k X ∧ ∀ c ∈ X, ρ c = true)
      (coordFinder (ι := ι) (S := S) k)
      ((Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S)
      (1 + Fintype.card ι * (k - 1 : ℕ)) := by
  have h := isFinder_blockFinder (S := fun _ : ι => S) (fun _ => k)
  have hκ : (∑ _j : ι, ((k - 1 : ℕ) : ℝ≥0∞) / (Fintype.card S : ℝ≥0∞))
      = (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc]
  have hT : (1 + ∑ _j : ι, ((k - 1 : ℕ) : ℝ≥0∞)) = 1 + Fintype.card ι * (k - 1 : ℕ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hκ, hT] at h
  exact ⟨fun ρ z hz X hX => by
      obtain ⟨hX, hacc⟩ := h.sound ρ z hz X hX
      exact ⟨isCoordSpecialSound_iff_isBlockSpecialSound.2 hX, hacc⟩,
    h.success, h.cost⟩

end OracleComp
