/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.Covering

/-! # Interleaved-target coverage canaries

Two properties of `KeyedHash.Covering.TapeCoveredReuse` that its bound depends on and that no
statement in `Covering.lean` pins.

The freshness requirement — that a coverer differ from the target — is what keeps the event from
holding for every tuple: a one-coordinate tuple is uncovered, while the requirement-free
`TapeCoveredNoFresh` is satisfied by that same tuple.

Coverer reuse is a strict weakening: at `q = 2` and `k = 2` a constant tuple is covered with
reuse although no injective coverer assignment exists there at all.

The role-separated event `TapeCoveredSplit` has one hypothesis on its bound, disjointness of the
two families, and it is necessary for the statement: with the families equal the event holds for
every tuple, and the bound is then false outright rather than loose.  The coverer family need not
be injective, although a non-injective one does lower the number of distinct positions the
coverers occupy below the number of distinct coverer indices; that per-witness gap is pinned
separately, since it is what the bound's canonicalisation step exists to absorb.

The fibre count `card_filter_card_image_eq_split` is checked against a brute-force count at tiny
parameters, including every degenerate one — `qh = 0`, `qs = 0`, `n = 0`, `r = 0 < n`, `r = n` —
and the `Nat.descFactorial` variant of its statement is refuted.
-/

public section

open KeyedHash.Covering MeasureTheory AnswerTape
open scoped ENNReal

namespace CoveringTest

/-! ## Freshness -/

/-- A one-coordinate tuple is not covered: its only coordinate is the target, and a coverer must
differ from the target. -/
theorem not_tapeCoveredReuse_of_q_eq_one (v : Fin 1 → Digest 0 1 1) :
    ¬ TapeCoveredReuse 0 1 1 1 v := by
  rintro ⟨j₀, f, hne, -⟩
  exact hne 0 (Subsingleton.elim _ _)

/-- Without the freshness requirement that same tuple *is* covered. -/
theorem tapeCoveredNoFresh_of_q_eq_one (v : Fin 1 → Digest 0 1 1) :
    TapeCoveredNoFresh 0 1 1 1 v :=
  tapeCoveredNoFresh_of_pos 0 1 1 Nat.one_pos v

/-! ## Reuse -/

/-- A constant two-coordinate tuple is covered with reuse: the second coordinate covers both
digits of the first. -/
theorem tapeCoveredReuse_const :
    TapeCoveredReuse 0 1 2 2 (fun _ => (0, fun _ => 0)) :=
  ⟨0, fun _ => 1, fun _ => (by decide : (1 : Fin 2) ≠ (0 : Fin 2)), fun _ => ⟨rfl, rfl⟩⟩

/-- At `q = 2` and `k = 2` no injective coverer assignment exists at all: a target coordinate
together with two distinct coverers needs three distinct coordinates out of two.  With
`tapeCoveredReuse_const` this makes coverage with reuse a strict super-event of its injective
restriction. -/
theorem not_exists_injective_coverers :
    ¬ ∃ (j₀ : Fin 2) (f : Fin 2 → Fin 2), Function.Injective f ∧ ∀ i, f i ≠ j₀ := by
  decide

/-! ## The hypotheses of the role-separated bound -/

/-- **Disjointness of the two families is load-bearing.**  With the target family and the coverer
family equal, every tuple is covered: the target covers itself. -/
theorem tapeCoveredSplit_of_tgt_eq_cov (v : Fin 1 → Digest 0 1 1) :
    TapeCoveredSplit 0 1 1 1 1 1 id id v :=
  ⟨0, fun _ => 0, fun _ => ⟨rfl, rfl⟩⟩

/-- **Disjointness is necessary for the bound, not only for its proof.**  With `tgt = cov = id`
at `qh = qs = q = k = 1` and `h = a = 1` the event is everything, so its mass is `1`, while the
closed form is `1 / 4`.  So the conclusion of
`evalDist_answerTape_tapeCoveredSplit_le_closedForm` is false without the hypothesis. -/
theorem not_le_closedForm_of_tgt_eq_cov :
    ¬ 𝒟[answerTape (Digest 1 1 1) 1] {v | TapeCoveredSplit 1 1 1 1 1 1 id id v} ≤
      ∑ r ∈ Finset.range (1 + 1),
        ((1 * (1 : ℕ).choose r *
            (Finset.univ.filter fun s : Fin 1 → Fin r => Function.Surjective s).card : ℕ) :
          ℝ≥0∞) *
          ((((2 : ℝ≥0∞) ^ 1)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ 1)⁻¹) ^ 1) := by
  have huniv : {v : Fin 1 → Digest 1 1 1 | TapeCoveredSplit 1 1 1 1 1 1 id id v} = Set.univ :=
    Set.eq_univ_of_forall fun v => ⟨0, fun _ => 0, fun _ => ⟨rfl, rfl⟩⟩
  have h0 : (Finset.univ.filter fun s : Fin 1 → Fin 0 => Function.Surjective s).card = 0 := by
    decide
  have h1 : (Finset.univ.filter fun s : Fin 1 → Fin 1 => Function.Surjective s).card = 1 := by
    decide
  rw [huniv, measure_univ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
  norm_num

/-- **A non-injective coverer family lowers the per-witness exponent.**  It can place two
distinct coverer indices at one position, so that the number of positions the coverers occupy —
the exponent of the leaf factor a single witness pays — falls below the number of distinct
coverer indices.  The bound survives this without an injectivity hypothesis, by ranging over
canonical witnesses only; what the guard pins is the per-witness inequality itself. -/
theorem exists_card_image_comp_lt :
    ∃ (cov : Fin 2 → Fin 1) (f : Fin 2 → Fin 2),
      (Finset.univ.image fun i => cov (f i)).card < (Finset.univ.image f).card := by
  decide

/-! ## The fibre count at small parameters -/

/-- `qh = 3`, `qs = 3`, `n = 2`, `r = 2`: eighteen witnesses with two distinct coverers. -/
theorem card_filter_card_image_eq_split_3_3_2_2 :
    (Finset.univ.filter fun c : Fin 3 × (Fin 2 → Fin 3) =>
        (Finset.univ.image c.2).card = 2).card = 18 := by
  decide

theorem card_filter_card_image_eq_split_closedForm_3_3_2_2 :
    3 * (3 : ℕ).choose 2 *
      (Finset.univ.filter fun s : Fin 2 → Fin 2 => Function.Surjective s).card = 18 := by
  decide

/-- **The `Nat.descFactorial` variant is wrong.**  At `qh = qs = 3`, `n = r = 2` it gives `36`,
not `18`: the surjection count already carries the `r !` that `descFactorial` contributes. -/
theorem card_filter_card_image_eq_split_descFactorial_ne :
    3 * (3 : ℕ).descFactorial 2 *
        (Finset.univ.filter fun s : Fin 2 → Fin 2 => Function.Surjective s).card ≠
      (Finset.univ.filter fun c : Fin 3 × (Fin 2 → Fin 3) =>
        (Finset.univ.image c.2).card = 2).card := by
  decide

/-- `r = 1 < n`: one coverer position covers both digits. -/
theorem card_filter_card_image_eq_split_2_2_2_1 :
    (Finset.univ.filter fun c : Fin 2 × (Fin 2 → Fin 2) =>
        (Finset.univ.image c.2).card = 1).card =
      2 * (2 : ℕ).choose 1 *
        (Finset.univ.filter fun s : Fin 2 → Fin 1 => Function.Surjective s).card := by
  decide

/-- `r = 0 < n`: both sides vanish, there being no surjection onto `Fin 0`. -/
theorem card_filter_card_image_eq_split_3_3_2_0 :
    (Finset.univ.filter fun c : Fin 3 × (Fin 2 → Fin 3) =>
        (Finset.univ.image c.2).card = 0).card =
      3 * (3 : ℕ).choose 0 *
        (Finset.univ.filter fun s : Fin 2 → Fin 0 => Function.Surjective s).card := by
  decide

/-- `n = 0`: the empty assignment at each of the `qh` targets. -/
theorem card_filter_card_image_eq_split_3_3_0_0 :
    (Finset.univ.filter fun c : Fin 3 × (Fin 0 → Fin 3) =>
        (Finset.univ.image c.2).card = 0).card =
      3 * (3 : ℕ).choose 0 *
        (Finset.univ.filter fun s : Fin 0 → Fin 0 => Function.Surjective s).card := by
  decide

/-- `qs = 0`: there is no assignment at all, and `C(0, 1) = 0` on the right. -/
theorem card_filter_card_image_eq_split_2_0_1_1 :
    (Finset.univ.filter fun c : Fin 2 × (Fin 1 → Fin 0) =>
        (Finset.univ.image c.2).card = 1).card =
      2 * (0 : ℕ).choose 1 *
        (Finset.univ.filter fun s : Fin 1 → Fin 1 => Function.Surjective s).card := by
  decide

/-- `qh = 0`: there is no target, and both sides vanish. -/
theorem card_filter_card_image_eq_split_0_3_2_2 :
    (Finset.univ.filter fun c : Fin 0 × (Fin 2 → Fin 3) =>
        (Finset.univ.image c.2).card = 2).card =
      0 * (3 : ℕ).choose 2 *
        (Finset.univ.filter fun s : Fin 2 → Fin 2 => Function.Surjective s).card := by
  decide

end CoveringTest
