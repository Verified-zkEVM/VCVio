/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork

/-!
# An analytic multi-round recurrence for coordinate-wise table forking

This module proves the numeric recurrence behind the success-probability calculation in Lemma 7.2
of Fenzi–Moghaddas–Nguyen. It shows that recursively applying the single-round table bound loses at
most `μ * ℓ * (k - 1) / N`.

The numeric recurrence treats "the subproblem succeeds on the curried input" as its next-round
acceptance probability. It instantiates the single-round table bound at `PMF.bernoulliTable` with
those probabilities as biases.

`avgTranscript` is defined by the same recursion as `multiSucc`, so the averaging (Fubini) step of
the paper's proof is definitional here rather than a lemma.

Only numbers recurse. `multiSucc` is not a `ProbComp`, does not execute a prover or verifier, and
does not return a transcript tree; each step instantiates an independent Bernoulli-table coupling
from the supplied marginal probabilities.

That coupling is not an assumption about the extractor.
`VCVio/CryptoFoundations/CoordinateFork/MultiRoundOp.lean` builds the recursion of §7.2 as a
computation and proves its success probability is exactly `multiSucc`, because running the
sub-extractor independently at each first challenge produces that very table. What remains outside
this file is the extractor's output and its expected cost.
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

instance instDecidableEqTranscript : ∀ μ : ℕ, DecidableEq (Transcript ι S μ)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | μ + 1 => @instDecidableEqProd _ _ _ (instDecidableEqTranscript μ)

instance instFintypeTranscript : ∀ μ : ℕ, Fintype (Transcript ι S μ)
  | 0 => inferInstanceAs (Fintype PUnit)
  | μ + 1 => @instFintypeProd _ _ _ (instFintypeTranscript μ)

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

/-- The success functional of the single-round table computation when entry `c` has marginal
accepting probability `q c` under the selected independent coupling.

Biases above `1` are clamped, so that the recursion in `multiSucc` carries no proof obligation;
`le_forkSucc_add` shows the clamp is invisible for genuine probabilities. -/
noncomputable def forkSucc (k : ℕ) (q : (ι → S) → ℝ≥0∞) : ℝ≥0∞ :=
  forkSuccOf k (PMF.bernoulliTable (fun c => min (q c) 1) fun _ => min_le_right _ _ :
    PMF ((ι → S) → Bool))

/-- Clamping is invisible for genuine probabilities. -/
theorem forkSucc_eq_forkSuccOf (k : ℕ) (q : (ι → S) → ℝ≥0∞) (hq : ∀ c, q c ≤ 1) :
    forkSucc k q = forkSuccOf k (PMF.bernoulliTable q hq : PMF ((ι → S) → Bool)) := by
  rw [forkSucc, PMF.bernoulliTable_congr _ hq (funext fun c => min_eq_left (hq c))]

/-- **Single-step bridge.** `forkSucc` is the coordinate table fork's success probability at any
`ProbComp` table distribution realizing the Bernoulli table with biases `q`.

This prevents `forkSucc` from being an unconstrained abstract functional. The hypothesis equates
the entire table distribution, not merely its marginals; `CoordinateFork/Realizability.lean`
discharges it for the table an adversary induces, and `CoordinateFork/MultiRoundOp.lean` for the
one the recursion produces. -/
theorem forkSucc_eq_probEvent_isSome_coordFork [SampleableType (ι → S)] (k : ℕ)
    (q : (ι → S) → ℝ≥0∞) (hq : ∀ c, q c ≤ 1) (D : ProbComp ((ι → S) → Bool))
    (hD : ∀ ρ, Pr[= ρ | D] = Pr[= ρ | (PMF.bernoulliTable q hq : PMF ((ι → S) → Bool))]) :
    forkSucc k q = Pr[fun r => r.isSome | coordFork k D] := by
  rw [probEvent_isSome_coordFork, forkSucc_eq_forkSuccOf k q hq, forkSuccOf, forkSuccOf]
  exact tsum_congr fun ρ => by rw [hD ρ]

/-- The analytic multi-round success functional. At each round the recursive value plays the role
of the next table's marginal accepting probability. This is not itself a computation. -/
noncomputable def multiSucc (k : ℕ) : ∀ {μ : ℕ}, (Transcript ι S μ → ℝ≥0∞) → ℝ≥0∞
  | 0, p => p PUnit.unit
  | _ + 1, p => forkSucc k fun c => multiSucc k fun r => p (c, r)

@[simp] theorem multiSucc_zero (k : ℕ) (p : Transcript ι S 0 → ℝ≥0∞) :
    multiSucc k p = p PUnit.unit := rfl

theorem multiSucc_succ (k : ℕ) {μ : ℕ} (p : Transcript ι S (μ + 1) → ℝ≥0∞) :
    multiSucc k p = forkSucc k fun c => multiSucc (μ := μ) k fun r => p (c, r) := rfl

/-- One round of the analytic recursion is exactly the single-round table functional. -/
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

/-- The additive numeric recurrence underlying the success bound in **Lemma 7.2** of
Fenzi–Moghaddas–Nguyen. It does not construct the paper's extractor. -/
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

/-- The numeric recurrence in the subtracted form used by **Lemma 7.2**:
`avgTranscript p - μ * ℓ * (k - 1) / N ≤ multiSucc k p`. Here `multiSucc` is the analytic
functional above, not the success probability of a constructed multi-round extractor. -/
theorem sub_le_multiSucc [Nonempty S] (k : ℕ) {μ : ℕ} (p : Transcript ι S μ → ℝ≥0∞)
    (hp : ∀ t, p t ≤ 1) :
    avgTranscript p - μ * roundLoss ι S k ≤ multiSucc k p :=
  tsub_le_iff_right.mpr (avgTranscript_le_multiSucc_add k p hp)

end OracleComp
