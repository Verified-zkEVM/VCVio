/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Combinatorics.CoordinateWise
public import ToMathlib.Probability.BernoulliTable
public import VCVio.EvalDist.Defs.Instances
public import VCVio.EvalDist.Monad.Basic

/-!
# Averaging a coordinate-wise rewinding bound over a distribution of acceptance tables

An *acceptance table* `ρ : (ι → S) → Bool` records, for every challenge vector, whether the
table entry is accepted. The table computation succeeds exactly when the sampled challenge accepts
and every one of its columns holds at least `k` accepting values. This is a predicate on the
challenge alone, so its success bound is the finite counting inequality
`CoordinateWise.sub_div_le_div_card_filter`.

A *randomized* adversary is a distribution over tables. Because the counting bound holds pointwise
in `ρ`, it survives averaging over an *arbitrary* distribution `D`, and
`le_tsum_probOutput_mul_goodSet` records that: only the marginals `Pr[ρ c]` appear on the left, and
no independence hypothesis is needed. The analytic multi-round recurrence later instantiates this
at a particular independent Bernoulli coupling; connecting that coupling to executions of a
multi-round prover is separate and unproved.

Note what this does *not* say. `forkSuccOf k D` depends on all of `D`, not just its marginals, so
picking a particular coupling — as the multi-round layer does, by instantiating at an independent
Bernoulli table — is a modelling decision about the extractor's randomness, not a theorem.
-/

@[expose] public section

open Finset CoordinateWise

open scoped ENNReal

universe v

namespace OracleComp.EvalDist

variable {m : Type → Type v} [Monad m] [MonadLiftT m SPMF]
variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]

/-- The challenges a table accepts. -/
def acceptSet (ρ : (ι → S) → Bool) : Finset (ι → S) :=
  Finset.univ.filter fun c => ρ c

/-- The challenges on which the table core succeeds: accepting, with at least `k` accepting values
in every column. -/
def goodSet (k : ℕ) (ρ : (ι → S) → Bool) : Finset (ι → S) :=
  Finset.univ.filter fun c => ρ c ∧ ∀ j, k ≤ columnCount (fun c' => ρ c' = true) j c

/-- The average accepting probability of the table distribution against a uniform challenge. -/
noncomputable def acceptRatio (D : m ((ι → S) → Bool)) : ℝ≥0∞ :=
  (∑ c : ι → S, Pr[fun ρ => ρ c | D]) / Fintype.card (ι → S)

/-- The chance that a uniform challenge lands in `goodSet`, averaged over a distribution of
acceptance tables.

This is the single functional that both sides of the development compute. The extractor's success
probability is it at a `ProbComp` table distribution (`probEvent_isSome_coordFork`); the
multi-round recursion's `forkSucc` is it at a Bernoulli table. Naming it keeps the two from
drifting apart. -/
noncomputable def forkSuccOf (k : ℕ) (D : m ((ι → S) → Bool)) : ℝ≥0∞ :=
  ∑' ρ, Pr[= ρ | D] * (((goodSet k ρ).card : ℝ≥0∞) / Fintype.card (ι → S))

omit [DecidableEq S] in
/-- The all-accepting table accepts every challenge, so `ε = 1`. Together with a positive
`ℓ * (k - 1) / N` this is what keeps the truncated subtraction in the headline bounds from
collapsing to `0 ≤ _`. -/
@[simp] theorem acceptRatio_pure_const_true [Nonempty S] [LawfulMonadLiftT m SPMF] :
    acceptRatio (pure (fun _ => true) : m ((ι → S) → Bool)) = 1 := by
  have hone : ∀ c : ι → S,
      Pr[fun ρ => ρ c | (pure (fun _ => true) : m ((ι → S) → Bool))] = 1 := fun c => by simp
  rw [acceptRatio, Finset.sum_congr rfl fun c _ => hone c, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ENNReal.div_self (by simp) (by finiteness)]

omit [Monad m] [DecidableEq S] in
/-- The expected number of accepting challenges is the sum of the per-challenge marginals. -/
theorem tsum_probOutput_mul_card_acceptSet (D : m ((ι → S) → Bool)) :
    ∑' ρ, Pr[= ρ | D] * ((acceptSet ρ).card : ℝ≥0∞) =
      ∑ c : ι → S, Pr[fun ρ => ρ c | D] := by
  classical
  have hcard : ∀ ρ : (ι → S) → Bool,
      ((acceptSet ρ).card : ℝ≥0∞) = ∑ c : ι → S, if ρ c then (1 : ℝ≥0∞) else 0 :=
    fun ρ => Finset.natCast_card_filter _ _
  simp_rw [hcard]
  rw [tsum_probOutput_mul_finsetSum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [probEvent_eq_tsum_ite]
  exact tsum_congr fun ρ => by by_cases h : ρ c = true <;> simp [h]

omit [Monad m] [DecidableEq S] in
/-- **The averaging step for coordinate-wise forking.**

The counting bound holds pointwise in the acceptance table, so averaging it over any distribution
`D` on tables costs nothing beyond the `ℓ * (k - 1) / N` term. Only the marginals of `D` appear on
the left; independence of the table entries is never used. -/
theorem le_tsum_probOutput_mul_goodSet [Nonempty S] (D : m ((ι → S) → Bool)) (k : ℕ)
    (hmass : Pr[⊥ | D] = 0) :
    acceptRatio D
      ≤ forkSuccOf k D + (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S := by
  classical
  rw [acceptRatio, forkSuccOf]
  set T : ℝ≥0∞ := (Fintype.card (ι → S) : ℝ≥0∞) with hT
  set δ : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S with hδ
  -- Pointwise: the ToMathlib counting bound, moved to additive form.
  have hpt : ∀ ρ : (ι → S) → Bool,
      ((acceptSet ρ).card : ℝ≥0∞) / T ≤ ((goodSet k ρ).card : ℝ≥0∞) / T + δ := by
    intro ρ
    exact tsub_le_iff_right.mp
      (sub_div_le_div_card_filter (accept := fun c => ρ c = true) k)
  calc (∑ c : ι → S, Pr[fun ρ => ρ c | D]) / T
      = (∑' ρ, Pr[= ρ | D] * ((acceptSet ρ).card : ℝ≥0∞)) / T := by
        rw [tsum_probOutput_mul_card_acceptSet]
    _ = ∑' ρ, Pr[= ρ | D] * (((acceptSet ρ).card : ℝ≥0∞) / T) := by
        rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun ρ => by rw [mul_assoc, ← div_eq_mul_inv]
    _ ≤ ∑' ρ, Pr[= ρ | D] * ((((goodSet k ρ).card : ℝ≥0∞) / T) + δ) :=
        tsum_probOutput_mul_mono D hpt
    _ = (∑' ρ, Pr[= ρ | D] * (((goodSet k ρ).card : ℝ≥0∞) / T)) + δ := by
        simp_rw [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          tsum_probOutput_eq_one' hmass, one_mul]

omit [Monad m] [DecidableEq S] in
/-- The averaged table-counting bound, in the subtracted form used by Lemma 7.1 of
Fenzi–Moghaddas–Nguyen. -/
theorem sub_div_le_tsum_probOutput_mul_goodSet [Nonempty S] (D : m ((ι → S) → Bool)) (k : ℕ)
    (hmass : Pr[⊥ | D] = 0) :
    acceptRatio D - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ forkSuccOf k D :=
  tsub_le_iff_right.mpr (le_tsum_probOutput_mul_goodSet D k hmass)

/-! ## Bernoulli tables

A concrete family of table distributions: entry `c` accepts with probability `p c`, independently.
This is what the multi-round bound instantiates, with `p c` the sub-extractor's success probability
on the curried adversary. -/

section Bernoulli

variable {C : Type} [Fintype C] [DecidableEq C] {p : C → ℝ≥0∞}

/-- The marginal of a Bernoulli table is its intended bias. -/
@[simp] theorem probEvent_apply_bernoulliTable (hp : ∀ c, p c ≤ 1) (c : C) :
    Pr[fun ρ => ρ c | (PMF.bernoulliTable p hp : PMF (C → Bool))] = p c := by
  classical
  rw [probEvent_eq_sum_filter_univ]
  simp only [PMF.probOutput_eq_apply]
  exact PMF.sum_filter_bernoulliTable hp c

/-- Against a Bernoulli table the accepting ratio is the average bias, as it should be. -/
theorem acceptRatio_bernoulliTable {q : (ι → S) → ℝ≥0∞} (hq : ∀ c, q c ≤ 1) :
    acceptRatio (PMF.bernoulliTable q hq : PMF ((ι → S) → Bool)) =
      (∑ c : ι → S, q c) / Fintype.card (ι → S) := by
  rw [acceptRatio]
  exact congrArg (· / _) (Finset.sum_congr rfl fun c _ => probEvent_apply_bernoulliTable hq c)

end Bernoulli

end OracleComp.EvalDist
