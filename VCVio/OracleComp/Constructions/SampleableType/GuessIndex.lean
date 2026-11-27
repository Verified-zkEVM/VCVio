/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.EvalDist.EvalDistEq
public import ToMathlib.Data.Nat.Max
import ToMathlib.Data.List.GetD
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds

/-!
# Guessing an index of a list uniformly

The averaging step behind reductions that guess which oracle query is the bad one: if a
computation returns lists of at most `q` entries, the probability that some entry satisfies `S`
is at most `q` times the probability that the entry at an index guessed uniformly from
`Fin (max q 1)`, independently of the list, satisfies `S`
(`prEvent_exists_mem_le_mul_prEvent_getD`). The guess reads `List.getD` with a default, so an
index past the end of the list reads the default.

`prEvent_exists_mem_le_mul_prEvent_getD_of_evalDistEq` states the bound in any monad, for any
index computation distributed as `$ᵗ Fin (max q 1)`, such as a lifted uniform draw in an
`OracleComp` with a uniform oracle. The factor `q` cannot be lowered: a list of `q` entries of
which only one satisfies `S` meets the bound with equality. The pointwise counting fact is
`List.ite_exists_mem_le_sum_getD`.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v

/-- At a list of length at most `q` with an entry satisfying `S`, an index guessed uniformly from
`Fin (max q 1)` reads an entry satisfying `S` with probability at least `1 / q`. -/
private lemma one_le_mul_prEvent_uniformSample_getD {α : Type} {q : ℕ} {l : List α}
    (hl : l.length ≤ q) (S : α → Prop) (d : α) (h : ∃ x ∈ l, S x) :
    1 ≤ q * Pr{let i ← $ᵗ Fin (max q 1)}[S (l.getD i d)] := by
  classical
  have hcount := List.ite_exists_mem_le_sum_getD (R := ℝ≥0∞) hl S d
  simp only [h, ↓reduceIte, Finset.sum_boole] at hcount
  obtain ⟨x, hx, -⟩ := h
  have hq : 0 < q := List.length_pos_of_mem hx |>.trans_le hl
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fin,
    show ((max q 1 : ℕ) : ℝ≥0∞) = q by rw [max_eq_left hq],
    ENNReal.mul_div_cancel (by exact_mod_cast hq.ne') (ENNReal.natCast_ne_top q)]
  exact hcount

/-- **Guessing an index.** In any monad, if `mx` returns lists of at most `q` entries and `mi`
is distributed as a uniform index of `Fin (max q 1)`, the probability that some entry satisfies
`S` is at most `q` times the probability that the entry at the index drawn by `mi`, after `mx`,
satisfies `S`. -/
theorem prEvent_exists_mem_le_mul_prEvent_getD_of_evalDistEq
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [WeaklyLawfulMonadAttach m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} {q : ℕ}
    (mx : m (List α)) (hmx : ∀ l ∈ support mx, l.length ≤ q)
    (mi : m (Fin (max q 1))) (hmi : mi =ᵈ ($ᵗ Fin (max q 1) : ProbComp (Fin (max q 1))))
    (S : α → Prop) (d : α) :
    Pr{let l ← mx}[∃ x ∈ l, S x] ≤ q * Pr{let l ← mx; let i ← mi}[S (l.getD i d)] := by
  classical
  let : MeasurableSpace (List α) := ⊤
  calc Pr{let l ← mx}[∃ x ∈ l, S x]
      = Pr{let l ← mx}[(∃ x ∈ l, S x) ∧ l.length ≤ q] :=
        prEvent_congr_of_support _ _ _ fun l hl ↦ (and_iff_left (hmx l hl)).symm
    _ = ∫⁻ l, {l : List α | (∃ x ∈ l, S x) ∧ l.length ≤ q}.indicator 1 l ∂𝒟[mx] := by
        rw [prEvent_eq_evalDist_of_discrete, lintegral_indicator_one MeasurableSet.of_discrete]
    _ ≤ ∫⁻ l, q * Pr{let i ← mi}[S (l.getD i d)] ∂𝒟[mx] := lintegral_mono fun l ↦ by
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
        split_ifs with h
        · rw [hmi.prEvent_eq]
          exact one_le_mul_prEvent_uniformSample_getD h.2 S d h.1
        · exact zero_le
    _ = q * Pr{let l ← mx; let i ← mi}[S (l.getD i d)] := by
        rw [lintegral_const_mul _ Measurable.of_discrete, prEvent_bind_of_discrete]

/-- **Guessing an index.** If `mx` returns lists of at most `q` entries, the probability that
some entry satisfies `S` is at most `q` times the probability that the entry at an index drawn
uniformly from `Fin (max q 1)` after `mx` satisfies `S`. -/
theorem prEvent_exists_mem_le_mul_prEvent_getD {α : Type} {q : ℕ}
    (mx : ProbComp (List α)) (hmx : ∀ l ∈ support mx, l.length ≤ q) (S : α → Prop) (d : α) :
    Pr{let l ← mx}[∃ x ∈ l, S x] ≤
      q * Pr{let l ← mx; let i ← $ᵗ Fin (max q 1)}[S (l.getD i d)] :=
  prEvent_exists_mem_le_mul_prEvent_getD_of_evalDistEq mx hmx _ EvalDistEq.rfl S d
