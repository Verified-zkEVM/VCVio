/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork

/-!
# Coordinate-wise rewinding for multi-round protocols

Lemma 7.2 of Fenzi–Moghaddas–Nguyen: against a `(2μ + 1)`-round public-coin protocol whose every
round draws a challenge from `ι → S`, the coordinate-wise extractor succeeds with probability at
least `ε - μ * ℓ * (k - 1) / N`.

The extractor is built by recursion on the number of rounds: the round-1 extractor treats "the
sub-extractor succeeds on the curried adversary" as its acceptance event. That event is
*randomized*, which is exactly why the single-round bound is stated over an arbitrary distribution
of acceptance tables — instantiating it at `PMF.bernoulliTable` with the sub-extractor's success
probabilities as biases is all the multi-round step needs.

`avgTranscript` is defined by the same recursion as `multiSucc`, so the averaging (Fubini) step of
the paper's proof is definitional here rather than a lemma.

Only success probabilities recurse; realizing the multi-round extractor as a `ProbComp` would
additionally require sampling `PMF.bernoulliTable` at the sub-extractor's success probabilities,
which is left to the query-cost development along with the expected query bounds.
-/

@[expose] public section

open Finset CoordinateWise OracleComp OracleComp.EvalDist

open scoped ENNReal

namespace OracleComp

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]

/-! ## Transcripts -/

/-- Challenge sequences for a `μ`-round public-coin protocol. -/
def Transcript (ι S : Type) : ℕ → Type
  | 0 => PUnit
  | μ + 1 => (ι → S) × Transcript ι S μ

/-- The average of `p` over a uniformly random transcript, by recursion on the number of rounds.

Written this way, the "average over the first challenge of the average over the rest" step of the
multi-round proof holds by definition instead of needing Fubini. -/
noncomputable def avgTranscript : ∀ {μ : ℕ}, (Transcript ι S μ → ℝ≥0∞) → ℝ≥0∞
  | 0, p => p PUnit.unit
  | _ + 1, p => (∑ c : ι → S, avgTranscript fun r => p (c, r)) / Fintype.card (ι → S)

omit [DecidableEq S] in
@[simp] theorem avgTranscript_zero (p : Transcript ι S 0 → ℝ≥0∞) :
    avgTranscript p = p PUnit.unit := rfl

omit [DecidableEq S] in
theorem avgTranscript_succ {μ : ℕ} (p : Transcript ι S (μ + 1) → ℝ≥0∞) :
    avgTranscript p =
      (∑ c : ι → S, avgTranscript fun r => p (c, r)) / Fintype.card (ι → S) := rfl

/-! ## Success probabilities -/

/-- The single-round extractor's success probability against an adversary accepting challenge `c`
with probability `q c`.

Biases above `1` are clamped, so that the recursion in `multiSucc` carries no proof obligation;
`le_forkSucc_add` shows the clamp is invisible for genuine probabilities. -/
noncomputable def forkSucc (k : ℕ) (q : (ι → S) → ℝ≥0∞) : ℝ≥0∞ :=
  forkSuccOf k (PMF.bernoulliTable (fun c => min (q c) 1) fun _ => min_le_right _ _ :
    PMF ((ι → S) → Bool))

/-- Clamping is invisible for genuine probabilities. -/
theorem forkSucc_eq_forkSuccOf (k : ℕ) (q : (ι → S) → ℝ≥0∞) (hq : ∀ c, q c ≤ 1) :
    forkSucc k q = forkSuccOf k (PMF.bernoulliTable q hq : PMF ((ι → S) → Bool)) := by
  rw [forkSucc, PMF.bernoulliTable_congr _ hq (funext fun c => min_eq_left (hq c))]

/-- **The extractor bridge.** `forkSucc` is not merely a convenient functional: it *is* the
coordinate fork's success probability, at any `ProbComp` table distribution realizing the
Bernoulli table with biases `q`.

This is what pins the multi-round bound to the extractor. Without it `sub_le_multiSucc` would be a
fixed-point inequality about an abstract functional — `forkSucc k q := 1` would satisfy it. What
remains open is only *realizability*: whether a `ProbComp` with these marginals exists for the
sub-extractor's success probabilities. -/
theorem forkSucc_eq_probEvent_isSome_coordFork [SampleableType (ι → S)] (k : ℕ)
    (q : (ι → S) → ℝ≥0∞) (hq : ∀ c, q c ≤ 1) (D : ProbComp ((ι → S) → Bool))
    (hD : ∀ ρ, Pr[= ρ | D] = Pr[= ρ | (PMF.bernoulliTable q hq : PMF ((ι → S) → Bool))]) :
    forkSucc k q = Pr[fun r => r.isSome | coordFork k D] := by
  rw [probEvent_isSome_coordFork, forkSucc_eq_forkSuccOf k q hq, forkSuccOf, forkSuccOf]
  exact tsum_congr fun ρ => by rw [hD ρ]

/-- The multi-round extractor's success probability. At each round the sub-extractor's success
probability plays the role of the adversary's accepting probability. -/
noncomputable def multiSucc (k : ℕ) : ∀ {μ : ℕ}, (Transcript ι S μ → ℝ≥0∞) → ℝ≥0∞
  | 0, p => p PUnit.unit
  | _ + 1, p => forkSucc k fun c => multiSucc k fun r => p (c, r)

@[simp] theorem multiSucc_zero (k : ℕ) (p : Transcript ι S 0 → ℝ≥0∞) :
    multiSucc k p = p PUnit.unit := rfl

theorem multiSucc_succ (k : ℕ) {μ : ℕ} (p : Transcript ι S (μ + 1) → ℝ≥0∞) :
    multiSucc k p = forkSucc k fun c => multiSucc (μ := μ) k fun r => p (c, r) := rfl

/-- One round of the multi-round recursion is exactly the single-round extractor. -/
theorem multiSucc_one (k : ℕ) (p : Transcript ι S 1 → ℝ≥0∞) :
    multiSucc k p = forkSucc k fun c => p (c, PUnit.unit) := rfl

/-! ## The bound -/

/-- The per-round loss `ℓ * (k - 1) / N`. -/
noncomputable def roundLoss (ι S : Type) [Fintype ι] [Fintype S] (k : ℕ) : ℝ≥0∞ :=
  (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S

theorem forkSucc_le_one [Nonempty S] (k : ℕ) (q : (ι → S) → ℝ≥0∞) : forkSucc k q ≤ 1 := by
  have hT : (Fintype.card (ι → S) : ℝ≥0∞) ≠ 0 := by simp
  have hTtop : (Fintype.card (ι → S) : ℝ≥0∞) ≠ ⊤ := by finiteness
  have hle : ∀ ρ : (ι → S) → Bool,
      ((goodSet k ρ).card : ℝ≥0∞) / Fintype.card (ι → S) ≤ 1 := by
    intro ρ
    rw [ENNReal.div_le_iff_le_mul (Or.inl hT) (Or.inl hTtop), one_mul]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  rw [forkSucc, forkSuccOf]
  calc ∑' ρ, Pr[= ρ | (PMF.bernoulliTable (fun c => min (q c) 1)
          fun _ => min_le_right _ _ : PMF ((ι → S) → Bool))] *
            (((goodSet k ρ).card : ℝ≥0∞) / Fintype.card (ι → S))
      ≤ ∑' ρ, Pr[= ρ | (PMF.bernoulliTable (fun c => min (q c) 1)
          fun _ => min_le_right _ _ : PMF ((ι → S) → Bool))] * 1 :=
        tsum_probOutput_mul_mono _ hle
    _ = 1 := by
        simp only [mul_one]
        exact tsum_probOutput_of_liftM_PMF (m := PMF) _

theorem multiSucc_le_one [Nonempty S] (k : ℕ) : ∀ {μ : ℕ} (p : Transcript ι S μ → ℝ≥0∞),
    (∀ t, p t ≤ 1) → multiSucc k p ≤ 1
  | 0, _, hp => hp _
  | _ + 1, _, _ => forkSucc_le_one k _

/-- The single-round bound, in the additive form the induction consumes. -/
theorem le_forkSucc_add [Nonempty S] (k : ℕ) (q : (ι → S) → ℝ≥0∞) (hq : ∀ c, q c ≤ 1) :
    (∑ c : ι → S, q c) / Fintype.card (ι → S) ≤ forkSucc k q + roundLoss ι S k := by
  have hclamp : ∑ c : ι → S, min (q c) 1 = ∑ c : ι → S, q c :=
    Finset.sum_congr rfl fun c _ => min_eq_left (hq c)
  have hbound := le_tsum_probOutput_mul_goodSet
    (D := (PMF.bernoulliTable (fun c => min (q c) 1) fun _ => min_le_right _ _ :
      PMF ((ι → S) → Bool))) k (by simp)
  rwa [acceptRatio_bernoulliTable, hclamp] at hbound

/-- **Lemma 7.2** of Fenzi–Moghaddas–Nguyen, in additive form.

The `μ`-round coordinate-wise extractor loses at most `μ` times the single-round loss. -/
theorem avgTranscript_le_multiSucc_add [Nonempty S] (k : ℕ) :
    ∀ {μ : ℕ} (p : Transcript ι S μ → ℝ≥0∞), (∀ t, p t ≤ 1) →
      avgTranscript p ≤ multiSucc k p + μ * roundLoss ι S k
  | 0, p, _ => by simp
  | μ + 1, p, hp => by
      have hT : (Fintype.card (ι → S) : ℝ≥0∞) ≠ 0 := by simp
      have hTtop : (Fintype.card (ι → S) : ℝ≥0∞) ≠ ⊤ := by finiteness
      set q : (ι → S) → ℝ≥0∞ := fun c => multiSucc (μ := μ) k fun r => p (c, r) with hq
      have hq1 : ∀ c, q c ≤ 1 := fun c =>
        multiSucc_le_one k (fun r => p (c, r)) fun r => hp _
      -- Each round-`1` challenge inherits the `μ`-round bound from the induction hypothesis.
      have hIH : ∀ c : ι → S,
          avgTranscript (fun r => p (c, r)) ≤ q c + μ * roundLoss ι S k := fun c =>
        avgTranscript_le_multiSucc_add k (fun r => p (c, r)) fun r => hp _
      calc avgTranscript p
          = (∑ c : ι → S, avgTranscript fun r => p (c, r)) / Fintype.card (ι → S) := rfl
        _ ≤ (∑ _c : ι → S, (q _c + μ * roundLoss ι S k)) / Fintype.card (ι → S) := by
            gcongr with c; exact hIH c
        _ = (∑ c : ι → S, q c) / Fintype.card (ι → S) + μ * roundLoss ι S k := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              ENNReal.add_div, mul_comm ((Fintype.card (ι → S) : ℝ≥0∞)),
              mul_div_assoc, ENNReal.div_self hT hTtop, mul_one]
        _ ≤ (forkSucc k q + roundLoss ι S k) + μ * roundLoss ι S k := by
            gcongr; exact le_forkSucc_add k q hq1
        _ = multiSucc k p + (μ + 1 : ℕ) * roundLoss ι S k := by
            rw [multiSucc_succ, ← hq]
            push_cast
            ring

/-- **Lemma 7.2**, in the paper's subtracted form: the `μ`-round coordinate-wise extractor succeeds
with probability at least `ε - μ * ℓ * (k - 1) / N`. -/
theorem sub_le_multiSucc [Nonempty S] (k : ℕ) {μ : ℕ} (p : Transcript ι S μ → ℝ≥0∞)
    (hp : ∀ t, p t ≤ 1) :
    avgTranscript p - μ * roundLoss ι S k ≤ multiSucc k p :=
  tsub_le_iff_right.mpr (avgTranscript_le_multiSucc_add k p hp)

end OracleComp
