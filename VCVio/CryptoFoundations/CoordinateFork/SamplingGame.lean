/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.Operational

/-!
# The abstract sampling game

Figure 12 of Fenzi–Moghaddas–Nguyen, the game §8 analyses on the way to knowledge soundness of a
Fiat–Shamir-transformed coordinate-wise special-sound protocol.

An *array* `M : (Q × ι → S) → Bool × Q` records, for each assignment of a challenge value to every
(query, coordinate) pair, whether the deterministic prover's forgery verifies and which random
oracle query it uses. The game draws an assignment uniformly; if its entry rejects it stops, and
otherwise it resamples each coordinate of the *winning query's block* — without replacement — until
`k - 1` further hits for that same query are found or the coordinate is exhausted.

The difference from §7's fork (`CoordinateFork/Operational.lean`) is that the block being resampled
is chosen by the array entry rather than fixed in advance: `M j` names the query whose challenge is
worth rewinding. Everything else is the same loop, so `ProbComp.drawUntil` and the negative
hypergeometric bound carry over unchanged.

`expectedValue_cost_samplingGame_le` is the first half of Lemma 8.1: the game examines at most
`1 + ℓ(k-1)·P` array entries on average, where `P` sums, over queries, the chance that the query's
block holds a hit at all. That is the half of Lemma 8.1 the paper proves from scratch. Its success
half explicitly reuses a bound of Attema–Fehr–Klooß and is not formalized here.
-/

@[expose] public section

open Finset CoordinateWise OracleComp OracleComp.EvalDist ProbComp

open scoped ENNReal

namespace OracleComp

variable {Q ι S : Type} [DecidableEq Q] [Fintype Q] [DecidableEq ι] [Fintype ι]
  [DecidableEq S] [Fintype S]

/-! ## Arrays and their hit counts -/

/-- The array entry at `j` is a hit for query `i`: the forgery verifies and it is `i` that it
uses. -/
def hitsAt (M : (Q × ι → S) → Bool × Q) (i : Q) (j : Q × ι → S) : Bool :=
  (M j).1 && decide ((M j).2 = i)

omit [Fintype Q] [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] in
theorem hitsAt_iff {M : (Q × ι → S) → Bool × Q} {i : Q} {j : Q × ι → S} :
    hitsAt M i j ↔ (M j).1 ∧ (M j).2 = i := by
  simp [hitsAt]

omit [Fintype Q] [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] in
/-- The winning query of an accepting entry is the only one it is a hit for. -/
@[simp] theorem hitsAt_snd {M : (Q × ι → S) → Bool × Q} {j : Q × ι → S} (h : (M j).1) :
    hitsAt M (M j).2 j := by
  simp [hitsAt, h]

/-- `a_i(j)` of Equation (29): how many assignments agreeing with `j` outside query `i`'s block are
hits for `i`. -/
def blockCount (M : (Q × ι → S) → Bool × Q) (i : Q) (j : Q × ι → S) : ℕ :=
  (Finset.univ.filter fun j' : Q × ι → S =>
    (∀ p : Q × ι, p.1 ≠ i → j' p = j p) ∧ hitsAt M i j').card

/-- `a_{i,l}(j) ≤ a_i(j)`: varying one coordinate of a block is a special case of varying the
whole block. This is the step that turns the per-coordinate count into the per-query one. -/
theorem columnCount_le_blockCount (M : (Q × ι → S) → Bool × Q) (i : Q) (l : ι)
    (j : Q × ι → S) :
    columnCount (fun j' => hitsAt M i j') (i, l) j ≤ blockCount M i j := by
  classical
  rw [columnCount, blockCount,
    ← Finset.card_image_of_injective _ (Function.update_injective j (i, l))]
  refine Finset.card_le_card fun j' hj' => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj'
  rw [Finset.mem_filter] at hx ⊢
  refine ⟨Finset.mem_univ _, fun p hp => ?_, hx.2⟩
  exact Function.update_of_ne (fun h => hp (by rw [h])) _ _

/-! ## The game -/

/-- The loop at one coordinate of the winning query's block. -/
noncomputable def gameDraws (k : ℕ) (M : (Q × ι → S) → Bool × Q) (i : Q) (j : Q × ι → S)
    (l : ι) : ProbComp (List S) :=
  drawUntil (fun x => hitsAt M i (Function.update j (i, l) x)) (k - 1) (altPool j (i, l))

/-- The hits a run collected at coordinate `l` of the block. -/
noncomputable def gameCollected (M : (Q × ι → S) → Bool × Q) (i : Q) (j : Q × ι → S)
    (d : ι → List S) (l : ι) : Finset S :=
  ((d l).filter fun x => hitsAt M i (Function.update j (i, l) x)).toFinset

/-- The game once the assignment has been drawn. -/
noncomputable def samplingGameAt (k : ℕ) (M : (Q × ι → S) → Bool × Q) (j : Q × ι → S) :
    ProbComp (Option (ι → Finset S) × ℕ) :=
  if (M j).1 then do
    let d ← Fintype.mPi (gameDraws k M (M j).2 j)
    let cost : ℕ := 1 + ∑ l, (d l).length
    if ∀ l, (gameCollected M (M j).2 j d l).card = k - 1 then
      return (some (gameCollected M (M j).2 j d), cost)
    else return (none, cost)
  else return (none, 1)

/-- **Figure 12 of Fenzi–Moghaddas–Nguyen**, the abstract sampling game. -/
noncomputable def samplingGame [SampleableType (Q × ι → S)] (k : ℕ)
    (M : (Q × ι → S) → Bool × Q) : ProbComp (Option (ι → Finset S) × ℕ) :=
  ($ᵗ (Q × ι → S)) >>= samplingGameAt k M

/-! ## How many entries the game examines -/

/-- `P` of Lemma 8.1: summed over queries, the chance that the query's block holds a hit.

Despite each summand being a probability the total is not one — it is a sum over the query index,
so it ranges up to `Fintype.card Q` (`blockHitTotal_le_card`), and that is the bound that turns
Lemma 8.1 into the familiar `1 + Q·ℓ(k-1)`. -/
noncomputable def blockHitTotal (M : (Q × ι → S) → Bool × Q) : ℝ≥0∞ :=
  ∑ i : Q, ((Finset.univ.filter fun j : Q × ι → S => 0 < blockCount M i j).card : ℝ≥0∞)
    / Fintype.card (Q × ι → S)

/-- Each query contributes at most one, so the total is at most the number of queries. -/
theorem blockHitTotal_le_card (M : (Q × ι → S) → Bool × Q) :
    blockHitTotal M ≤ Fintype.card Q := by
  classical
  rw [blockHitTotal]
  calc ∑ i : Q, ((Finset.univ.filter fun j : Q × ι → S => 0 < blockCount M i j).card : ℝ≥0∞)
          / Fintype.card (Q × ι → S)
      ≤ ∑ _i : Q, (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun i _ => ENNReal.div_le_of_le_mul ?_
        rw [one_mul, ← Finset.card_univ]
        exact_mod_cast Finset.card_filter_le _ _
    _ = Fintype.card Q := by simp

omit [Fintype Q] in
/-- At a fixed assignment the game costs one entry for the assignment itself and then one negative
hypergeometric experiment per coordinate of the winning block. -/
theorem expectedValue_cost_samplingGameAt (k : ℕ) (M : (Q × ι → S) → Bool × Q)
    (j : Q × ι → S) :
    expectedValue (samplingGameAt k M j) (fun r => (r.2 : ℝ≥0∞))
      = if (M j).1 then
          1 + ∑ l : ι, NegHypergeom.expectedDraws (Fintype.card S - 1)
            ((hitSet (fun j' => hitsAt M (M j).2 j') j ((M j).2, l)).card) (k - 1)
        else 1 := by
  classical
  rw [samplingGameAt]
  by_cases hacc : (M j).1
  · rw [if_pos hacc, if_pos hacc, expectedValue_bind]
    have hinner : ∀ d : ι → List S,
        expectedValue
          (if ∀ l, (gameCollected M (M j).2 j d l).card = k - 1 then
              (pure (some (gameCollected M (M j).2 j d), 1 + ∑ l, (d l).length) :
                ProbComp (Option (ι → Finset S) × ℕ))
            else pure (none, 1 + ∑ l, (d l).length))
          (fun p => (p.2 : ℝ≥0∞))
          = 1 + ∑ l : ι, ((d l).length : ℝ≥0∞) := by
      intro d
      split <;> · rw [expectedValue_pure]; push_cast; rfl
    simp only [hinner]
    rw [expectedValue_add, expectedValue_const (probFailure_of_liftM_PMF _),
      expectedValue_finsetSum]
    refine congrArg (1 + ·) (Finset.sum_congr rfl fun l _ => ?_)
    rw [expectedValue_coord_mPi (gameDraws k M (M j).2 j)
        (fun _ => probFailure_of_liftM_PMF _) l (fun d => (d.length : ℝ≥0∞)),
      gameDraws, expectedValue_length_drawUntil _ (altPool j ((M j).2, l)).length _ _ rfl,
      length_altPool, countP_altPool]
  · rw [if_neg hacc, if_neg hacc, expectedValue_pure]
    push_cast
    ring

/-- One coordinate of one query's block: averaged over the assignment, the loop there costs at
most `k - 1` entries per assignment whose block holds a hit at all.

This is the counting step of Lemma 8.1, and it is the sharpened column count doing the work: a
column contributes `w` exactly when it holds a hit, so the bound is proportional to the number of
assignments with a nonempty column — which `columnCount_le_blockCount` then relaxes to the
per-query count `a_i`. -/
theorem sum_expectedDraws_le_blockCount [Nonempty S] (k : ℕ) (M : (Q × ι → S) → Bool × Q)
    (i : Q) (l : ι) :
    ∑ j : Q × ι → S, (if hitsAt M i j then
        NegHypergeom.expectedDraws (Fintype.card S - 1)
          ((hitSet (fun j' => hitsAt M i j') j (i, l)).card) (k - 1) else 0)
      ≤ ((k - 1 : ℕ) : ℝ≥0∞) *
          ((Finset.univ.filter fun j : Q × ι → S => 0 < blockCount M i j).card : ℝ≥0∞) := by
  classical
  have hNne : (Fintype.card S : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hNtop : (Fintype.card S : ℝ≥0∞) ≠ ⊤ := by finiteness
  refine (ENNReal.mul_le_mul_iff_right hNne hNtop).mp ?_
  calc (Fintype.card S : ℝ≥0∞) * ∑ j : Q × ι → S, (if hitsAt M i j then
          NegHypergeom.expectedDraws (Fintype.card S - 1)
            ((hitSet (fun j' => hitsAt M i j') j (i, l)).card) (k - 1) else 0)
      ≤ (Fintype.card S : ℝ≥0∞) * ∑ j : Q × ι → S, (if hitsAt M i j then
          ((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)
            / ((columnCount (fun j' => hitsAt M i j' = true) (i, l) j : ℕ) : ℝ≥0∞) else 0) := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => ?_)
        by_cases hacc : hitsAt M i j
        · rw [if_pos hacc, if_pos hacc]
          exact expectedDraws_hitSet_le hacc (i, l)
        · rw [if_neg hacc, if_neg hacc]
    _ ≤ ((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞) *
          ((Finset.univ.filter fun j : Q × ι → S =>
            0 < columnCount (fun j' => hitsAt M i j' = true) (i, l) j).card : ℝ≥0∞) :=
        CoordinateWise.card_mul_sum_div_columnCount_le (i, l) _
    _ ≤ ((k - 1 : ℕ) : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞) *
          ((Finset.univ.filter fun j : Q × ι → S => 0 < blockCount M i j).card : ℝ≥0∞) := by
        refine mul_le_mul' le_rfl ?_
        have hsub : (Finset.univ.filter fun j : Q × ι → S =>
              0 < columnCount (fun j' => hitsAt M i j' = true) (i, l) j)
            ⊆ (Finset.univ.filter fun j : Q × ι → S => 0 < blockCount M i j) := by
          intro j hj
          rw [Finset.mem_filter] at hj ⊢
          exact ⟨hj.1, lt_of_lt_of_le hj.2 (columnCount_le_blockCount M i l j)⟩
        exact_mod_cast Finset.card_le_card hsub
    _ = (Fintype.card S : ℝ≥0∞) * (((k - 1 : ℕ) : ℝ≥0∞) *
          ((Finset.univ.filter fun j : Q × ι → S => 0 < blockCount M i j).card : ℝ≥0∞)) := by
        ring

/-- **The expected-samples half of Lemma 8.1.** The game examines one array entry for the
assignment it drew and, averaged over that assignment, at most `ℓ(k-1)` more — weighted by `P`, the
chance that a query's block holds a hit at all.

The paper's other half, the success probability, explicitly reuses a bound of Attema–Fehr–Klooß and
is not formalized here. -/
theorem expectedValue_cost_samplingGame_le [Nonempty S] [SampleableType (Q × ι → S)] (k : ℕ)
    (M : (Q × ι → S) → Bool × Q) :
    expectedValue (samplingGame k M) (fun r => (r.2 : ℝ≥0∞))
      ≤ 1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞) * blockHitTotal M := by
  classical
  have hCne : (Fintype.card (Q × ι → S) : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hCtop : (Fintype.card (Q × ι → S) : ℝ≥0∞) ≠ ⊤ := by finiteness
  -- Only the winning query contributes, so the data-dependent block splits into a sum over
  -- queries with a fixed block each.
  have hone : ∀ j : Q × ι → S,
      (if (M j).1 then (1 : ℝ≥0∞) + ∑ l : ι, NegHypergeom.expectedDraws (Fintype.card S - 1)
          ((hitSet (fun j' => hitsAt M (M j).2 j') j ((M j).2, l)).card) (k - 1) else 1)
        = 1 + ∑ l : ι, ∑ i : Q, (if hitsAt M i j then
            NegHypergeom.expectedDraws (Fintype.card S - 1)
              ((hitSet (fun j' => hitsAt M i j') j (i, l)).card) (k - 1) else 0) := by
    intro j
    by_cases hacc : (M j).1
    · rw [if_pos hacc]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_eq_single (M j).2
          (fun i _ hne => if_neg fun h => hne ((hitsAt_iff.mp h).2).symm)
          (fun h => absurd (Finset.mem_univ _) h),
        if_pos (hitsAt_snd hacc)]
    · rw [if_neg hacc]
      have hz : ∑ l : ι, ∑ i : Q, (if hitsAt M i j then
          NegHypergeom.expectedDraws (Fintype.card S - 1)
            ((hitSet (fun j' => hitsAt M i j') j (i, l)).card) (k - 1) else 0) = 0 :=
        Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun i _ =>
          if_neg fun h => hacc (hitsAt_iff.mp h).1
      rw [hz, add_zero]
  rw [samplingGame, expectedValue_bind, expectedValue_def]
  simp only [expectedValue_cost_samplingGameAt, hone, probOutput_uniformSample]
  rw [ENNReal.tsum_mul_left, tsum_fintype (L := .unconditional _), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_comm]
  calc (Fintype.card (Q × ι → S) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Q × ι → S) : ℝ≥0∞) + ∑ l : ι, ∑ j : Q × ι → S, ∑ i : Q,
          (if hitsAt M i j then NegHypergeom.expectedDraws (Fintype.card S - 1)
            ((hitSet (fun j' => hitsAt M i j') j (i, l)).card) (k - 1) else 0))
      = (Fintype.card (Q × ι → S) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (Q × ι → S) : ℝ≥0∞) + ∑ l : ι, ∑ i : Q, ∑ j : Q × ι → S,
            (if hitsAt M i j then NegHypergeom.expectedDraws (Fintype.card S - 1)
              ((hitSet (fun j' => hitsAt M i j') j (i, l)).card) (k - 1) else 0)) := by
        exact congrArg _ (congrArg _ (Finset.sum_congr rfl fun l _ => Finset.sum_comm))
    _ ≤ (Fintype.card (Q × ι → S) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (Q × ι → S) : ℝ≥0∞) + ∑ _l : ι, ∑ i : Q, ((k - 1 : ℕ) : ℝ≥0∞) *
            ((Finset.univ.filter fun j : Q × ι → S => 0 < blockCount M i j).card : ℝ≥0∞)) :=
        mul_le_mul' le_rfl (add_le_add le_rfl (Finset.sum_le_sum fun l _ =>
          Finset.sum_le_sum fun i _ => sum_expectedDraws_le_blockCount k M i l))
    _ = 1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞) * blockHitTotal M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add,
          ENNReal.inv_mul_cancel hCne hCtop, blockHitTotal, Finset.mul_sum, Finset.mul_sum,
          ← Finset.mul_sum]
        refine congrArg (1 + ·) ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.div_eq_inv_mul]
        ring

/-- The form Lemma 8.1 is used in: the number of random oracle queries replaces `P`, giving the
`1 + Q·ℓ(k-1)` expected cost that §8.2's extractor budgets for. -/
theorem expectedValue_cost_samplingGame_le_card [Nonempty S] [SampleableType (Q × ι → S)]
    (k : ℕ) (M : (Q × ι → S) → Bool × Q) :
    expectedValue (samplingGame k M) (fun r => (r.2 : ℝ≥0∞))
      ≤ 1 + Fintype.card ι * ((k - 1 : ℕ) : ℝ≥0∞) * Fintype.card Q :=
  (expectedValue_cost_samplingGame_le k M).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl (blockHitTotal_le_card M)))

end OracleComp
