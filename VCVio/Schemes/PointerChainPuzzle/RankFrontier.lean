/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.Bad

/-!
# Rank frontiers of the pointer-chain puzzle

`PathValue.rankPrefix n m r` contains the path values received by the honest oracle
execution by round `r`. A path input of rank at most `r + 1` depends only on labels
in that prefix. Conversely,
every path value of rank greater than `r + 1` has a predecessor outside the prefix.
Resampling the other labels therefore bounds the probability that a fixed oracle point
is the input of one of those future values by `hitBound n m S L`.

The resampling operation `mixLabels` always preserves the public commitment label in
addition to the rank prefix. This is compatible with the incidence bound because no path
value has the commitment as a predecessor. Preserving its public output label does not
make its oracle input available: the commitment input contains the secret key.

These are classical rank and incidence facts for a rank-indexed quantum hybrid. Applying
them to query weights also requires the reference pre-query state to depend only on the
preserved labels. A coherent oracle schedule must respect the rank restriction even for
the commitment's programmed cell.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace PointerChainPuzzle

namespace PathValue

/-- The path values received by the honest oracle execution by round `r`. -/
@[expose]
def rankPrefix (n m r : ℕ) : Finset (PathValue n m) :=
  Finset.univ.filter fun v ↦ v.rho ≤ r

/-- Membership in a rank prefix is its round inequality. -/
@[simp]
theorem mem_rankPrefix {n m r : ℕ} {v : PathValue n m} :
    v ∈ rankPrefix n m r ↔ v.rho ≤ r := by
  simp [rankPrefix]

/-- Increasing the available round only enlarges the prefix. -/
theorem rankPrefix_mono {n m r s : ℕ} (h : r ≤ s) :
    rankPrefix n m r ⊆ rankPrefix n m s :=
  fun _ hv ↦ mem_rankPrefix.mpr ((mem_rankPrefix.mp hv).trans h)

/-- Every predecessor of a value available by round `r + 1` is available by round `r`. -/
theorem preds_subset_rankPrefix {n m r : ℕ} [NeZero n] {v : PathValue n m}
    (hv : v.rho ≤ r + 1) : v.preds ⊆ rankPrefix n m r := by
  intro w hw
  have hlt := rho_lt_of_mem_preds hw
  exact mem_rankPrefix.mpr (by omega)

/-- Rank prefixes are closed under predecessors. -/
theorem preds_subset_rankPrefix_of_mem {n m r : ℕ} [NeZero n] {v : PathValue n m}
    (hv : v ∈ rankPrefix n m r) : v.preds ⊆ rankPrefix n m r :=
  preds_subset_rankPrefix ((mem_rankPrefix.mp hv).trans (Nat.le_succ _))

/-- A value beyond the next round has a predecessor beyond the current round. -/
theorem exists_pred_of_lt_rho {n m r : ℕ} [NeZero n] {v : PathValue n m}
    (hv : r + 1 < v.rho) : ∃ w ∈ v.preds, r < w.rho := by
  by_contra hn
  push Not at hn
  have hh := rho_le_succ_of_preds hn
  omega

end PathValue

variable {n m : ℕ} {S L Salt Ctx : Type} [NeZero n] [AddCommGroup L]
  {mkCtx : Salt → Ctx} {initAcc : Ctx → S}

/-- An input available in the next round depends only on labels in the current rank prefix. -/
theorem pathInput_eq_of_eq_on_rankPrefix (P : Puzzle n S L Salt)
    {ℓ ℓ' : Labels n m S L} {r : ℕ} {v : PathValue n m} (hv : v.rho ≤ r + 1)
    (h : ∀ w ∈ PathValue.rankPrefix n m r, ℓ w = ℓ' w) :
    pathInput m mkCtx initAcc P ℓ v = pathInput m mkCtx initAcc P ℓ' v :=
  pathInput_congr m mkCtx initAcc P v fun w hw ↦
    h w (PathValue.preds_subset_rankPrefix hv hw)

/-- Resampling beyond a rank prefix leaves every next-round path input unchanged. -/
theorem pathInput_mixLabels_rankPrefix (P : Puzzle n S L Salt)
    (ℓ₀ ℓ' : Labels n m S L) {r : ℕ} {v : PathValue n m} (hv : v.rho ≤ r + 1) :
    pathInput m mkCtx initAcc P (mixLabels (PathValue.rankPrefix n m r) ℓ₀ ℓ') v =
      pathInput m mkCtx initAcc P ℓ₀ v :=
  pathInput_eq_of_eq_on_rankPrefix P hv fun _ hw ↦ mixLabels_of_mem hw

/-- Oracle inputs of path values whose honest receipt round exceeds `r`. -/
@[expose]
def futurePathInputs (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)
    (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (r : ℕ) : Set (Point n S L Salt Ctx) :=
  {t | ∃ v : PathValue n m, r < v.rho ∧ t = pathInput m mkCtx initAcc P ℓ v}

/-- An input beyond the next round depends on a label outside the current rank prefix. -/
theorem futurePathInputs_subset_hitAt (P : Puzzle n S L Salt)
    (ℓ : Labels n m S L) (r : ℕ) :
    futurePathInputs m mkCtx initAcc P ℓ (r + 1) ⊆
      {t | HitAt m mkCtx initAcc P ℓ (PathValue.rankPrefix n m r) t} := by
  rintro t ⟨v, hv, he⟩
  refine ⟨v, he, ?_⟩
  obtain ⟨w, hw, hwr⟩ := PathValue.exists_pred_of_lt_rho hv
  intro hs
  have hp := PathValue.mem_rankPrefix.mp (hs hw)
  omega

/-- Under resampling outside a rank prefix, a fixed point hits an input beyond the next
round with probability at most `[n ≥ 2] / |L| + solvePoints n m / |S|`. The public commitment
label stays fixed throughout the resampling. -/
theorem prEvent_mem_futurePathInputs_mixLabels_le
    [SampleableType S] [SampleableType L] [Fintype S] [Fintype L]
    (P : Puzzle n S L Salt) (ℓ₀ : Labels n m S L) (r : ℕ)
    (t : Point n S L Salt Ctx) :
    Pr{let ℓ' ← $ᵗ Labels n m S L}[
      t ∈ futurePathInputs m mkCtx initAcc P
        (mixLabels (PathValue.rankPrefix n m r) ℓ₀ ℓ') (r + 1)] ≤
      hitBound n m S L := by
  classical
  exact (prEvent_mono _ _ _ fun ℓ' h ↦ futurePathInputs_subset_hitAt P _ r h).trans
    (prEvent_hitAt_le P (PathValue.rankPrefix n m r) ℓ₀ t)

end PointerChainPuzzle
