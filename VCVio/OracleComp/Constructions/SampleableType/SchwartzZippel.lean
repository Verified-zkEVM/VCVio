/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, Aristotle, Quang Dao
-/

module
public import ToMathlib.Algebra.MvPolynomial.SchwartzZippel
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! ## Schwartz–Zippel probability bounds

Uniformly sampling a product of finite subsets of a field makes a nonzero polynomial vanish with
probability at most its total degree divided by the smallest factor cardinality. Sampling over a
full finite field gives the total degree divided by the field cardinality.
-/

public section

open scoped ENNReal

/-- Probability of a nonzero polynomial evaluating to zero over a uniform product distribution
is at most `d / m`, where `d` bounds the total degree and `m` bounds below the cardinality
of each factor. This bridges `schwartz_zippel_counting` with the probability formulation.

`prob_eval_zero_univ_le_div` below specializes it to full finite carriers. -/
lemma prob_eval_zero_le_div
    {F : Type} [Field F] {ι : Type} [Finite ι]
    {S : ι → Set F} [∀ i, Fintype ↥(S i)] [∀ i, Nonempty ↥(S i)]
    [SampleableType (∀ i, ↥(S i))]
    (f : MvPolynomial ι F) (hf : f ≠ 0)
    (d m : ℕ) (hd : f.totalDegree ≤ d) (hm_pos : 0 < m)
    (hm : ∀ i, m ≤ (S i).toFinset.card) :
    Pr{let x ← $ᵗ (∀ i, ↥(S i))}[MvPolynomial.eval (fun i => (↑(x i) : F)) f = 0] ≤
      (d : ℝ≥0∞) / m := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [@SampleableType.prEvent_uniformSample _ _ _
    (fun x : ∀ i, ↥(S i) => MvPolynomial.eval (fun i => (↑(x i) : F)) f = 0)
    (fun _ => Classical.propDecidable _)]
  refine ENNReal.div_le_div_of_mul_le hm_pos
    (Fintype.card_pos_iff.mpr ⟨fun _ => Classical.arbitrary _⟩) ?_
  convert @schwartz_zippel_counting F _ (Classical.decEq F) ι _ _ f hf
      (fun i => (S i).toFinset) d m hd hm_pos hm using 1
  · convert congr_arg₂ (· * ·)
      (@card_filter_eval_subtype_eq_piFinset F _ (Classical.decEq F) ι _ _ S _ f) rfl
  · rw [Fintype.card_pi]
    aesop

/-- Full-carrier specialization of `prob_eval_zero_le_div`. -/
lemma prob_eval_zero_univ_le_div
    {F : Type} [Field F] [Fintype F] [SampleableType F]
    {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (f : MvPolynomial ι F) (hf : f ≠ 0) (hd : f.totalDegree ≤ d) :
    Pr{let x ← $ᵗ (ι → F)}[MvPolynomial.eval x f = 0] ≤
      (d : ℝ≥0∞) / Fintype.card F := by
  classical
  rw [@SampleableType.prEvent_uniformSample _ _ _
    (fun x : ι → F => MvPolynomial.eval x f = 0)
    (fun _ => Classical.propDecidable _)]
  refine ENNReal.div_le_div_of_mul_le Fintype.card_pos Fintype.card_pos ?_
  simpa only [Fintype.piFinset_univ, Finset.card_univ, Finset.prod_const,
    Fintype.card_fun] using
      @schwartz_zippel_counting F _ (Classical.decEq F) ι _ _ f hf
        (fun _ => Finset.univ) d (Fintype.card F) hd Fintype.card_pos (fun _ => le_rfl)

