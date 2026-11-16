/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, Aristotle, Quang Dao
-/

module
public import ToMathlib.Algebra.MvPolynomial.SchwartzZippel
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! ## Schwartz–Zippel probability bounds

Uniformly sampling a product of finite subsets of an integral domain makes a nonzero polynomial
vanish with probability at most its total degree divided by the smallest factor cardinality.
Sampling over a whole finite integral domain gives the total degree divided by its cardinality.
-/

public section

open scoped ENNReal

/-- Probability of a nonzero polynomial evaluating to zero over a uniform product distribution
is at most `d / m`, where `d` bounds the total degree and `m` bounds below the cardinality
of each factor. This bridges `schwartz_zippel_counting` with the probability formulation. -/
lemma prEvent_eval_eq_zero_le_div
    {F : Type} [CommRing F] [IsDomain F] {ι : Type} [Finite ι]
    {S : ι → Set F} [∀ i, Fintype ↥(S i)]
    [SampleableType (∀ i, ↥(S i))]
    (f : MvPolynomial ι F) (hf : f ≠ 0)
    (d m : ℕ) (hd : f.totalDegree ≤ d)
    (hm : ∀ i, m ≤ (S i).toFinset.card) :
    Pr{let x ← $ᵗ (∀ i, ↥(S i))}[MvPolynomial.eval (fun i => (↑(x i) : F)) f = 0] ≤
      (d : ℝ≥0∞) / m := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have key : ∀ m', 0 < m' → (∀ i, m' ≤ (S i).toFinset.card) →
      Pr{let x ← $ᵗ (∀ i, ↥(S i))}[MvPolynomial.eval (fun i => (↑(x i) : F)) f = 0] ≤
        (d : ℝ≥0∞) / m' := by
    intro m' hm' hmS
    rw [@SampleableType.prEvent_uniformSample _ _ _
      (fun x : ∀ i, ↥(S i) => MvPolynomial.eval (fun i => (↑(x i) : F)) f = 0)
      (fun _ => Classical.propDecidable _)]
    refine ENNReal.div_le_div_of_mul_le hm' ?_
    convert @schwartz_zippel_counting F _ _ (Classical.decEq F) ι _ _ f hf
        (fun i => (S i).toFinset) d m' hd hmS using 1
    · convert congr_arg₂ (· * ·)
        (card_filter_pi_subtype_eq_piFinset S (fun x => MvPolynomial.eval x f = 0)) rfl
    · rw [Fintype.card_pi]
      aesop
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · obtain ⟨x₀, -⟩ := support_uniformSample_nonempty (α := ∀ i, ↥(S i))
      have hS : ∀ i, 1 ≤ (S i).toFinset.card := fun i =>
        Finset.card_pos.mpr ⟨x₀ i, by simp⟩
      simpa using key 1 one_pos hS
    · rw [Nat.cast_zero, ENNReal.div_zero (by exact_mod_cast hd_pos.ne')]
      exact le_top
  · exact key m hm_pos hm

/-- A nonzero polynomial of total degree at most `d` vanishes on a uniform assignment over a
finite integral domain `F` with probability at most `d / Fintype.card F`. -/
lemma prEvent_eval_eq_zero_univ_le_div
    {F : Type} [CommRing F] [IsDomain F] [Fintype F]
    {ι : Type} [Finite ι] [SampleableType (ι → F)] {d : ℕ}
    (f : MvPolynomial ι F) (hf : f ≠ 0) (hd : f.totalDegree ≤ d) :
    Pr{let x ← $ᵗ (ι → F)}[MvPolynomial.eval x f = 0] ≤
      (d : ℝ≥0∞) / Fintype.card F := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [@SampleableType.prEvent_uniformSample _ _ _
    (fun x : ι → F => MvPolynomial.eval x f = 0)
    (fun _ => Classical.propDecidable _)]
  refine ENNReal.div_le_div_of_mul_le Fintype.card_pos ?_
  simpa only [Fintype.piFinset_univ, Finset.card_univ, Finset.prod_const,
    Fintype.card_fun] using
      @schwartz_zippel_counting F _ _ (Classical.decEq F) ι _ _ f hf
        (fun _ => Finset.univ) d (Fintype.card F) hd (fun _ => le_rfl)
