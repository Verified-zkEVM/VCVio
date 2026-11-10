/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, Aristotle, Quang Dao
-/

module
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Real

/-! ## Counting zeros of multivariate polynomials

A nonzero polynomial of bounded total degree has few zeros on products of finite subsets of an
integral domain. The variables range over any finite type. A finite integral domain gives a bound
in terms of its cardinality and the number of variables.
-/

public section

open scoped ENNReal NNReal BigOperators

/-- A nonzero polynomial of total degree at most `d` has at most `d / m` times the product
cardinality zeros, when each factor has at least `m` elements. -/
theorem schwartz_zippel_counting
    {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : MvPolynomial ι F) (hf : f ≠ 0) (S : ι → Finset F)
    (d m : ℕ) (hd : f.totalDegree ≤ d) (hm : ∀ i, m ≤ (S i).card) :
    (Finset.filter (fun x => MvPolynomial.eval x f = 0) (Fintype.piFinset S)).card * m
      ≤ d * ∏ i, (S i).card := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp
  let e := Fintype.equivFin ι
  let g := MvPolynomial.rename (e : ι → Fin (Fintype.card ι)) f
  let T := fun i => S (e.symm i)
  have hg : g ≠ 0 := fun h =>
    hf (MvPolynomial.rename_injective _ e.injective (by simpa [g] using h))
  have hgd : g.totalDegree ≤ d := (MvPolynomial.totalDegree_rename_le _ _).trans hd
  have hmT (i) : m ≤ (T i).card := hm (e.symm i)
  have hbound :
      ((Finset.filter (fun x => MvPolynomial.eval x g = 0) (Fintype.piFinset T)).card : ℚ≥0) /
          ∏ i, ((T i).card : ℚ≥0) ≤ d / (m : ℚ≥0) := by
    refine (MvPolynomial.schwartz_zippel_sup_sum hg T).trans ?_
    simp only [div_eq_mul_inv, mul_comm, Finset.sup_le_iff, MvPolynomial.mem_support_iff,
      ne_eq]
    intro b hb
    have h_deg : ∑ i, b i ≤ d := by
      simpa [Finsupp.sum_fintype] using
        (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hb)).trans hgd
    refine (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (Nat.cast_le.mpr (hmT i)))
        (Nat.cast_nonneg _)).trans ?_
    rw [← Finset.mul_sum, mul_comm]
    gcongr
    exact_mod_cast h_deg
  have hprod : 0 < ∏ i, ((T i).card : ℚ≥0) :=
    Finset.prod_pos fun i _ => by exact_mod_cast (hm_pos.trans_le (hmT i))
  have key :
      (Finset.filter (fun x => MvPolynomial.eval x g = 0) (Fintype.piFinset T)).card * m
        ≤ d * ∏ i, (T i).card := by
    have := (div_le_div_iff₀ hprod (by exact_mod_cast hm_pos)).mp hbound
    exact_mod_cast this
  have hcard :
      (Finset.filter (fun x => MvPolynomial.eval x f = 0) (Fintype.piFinset S)).card =
      (Finset.filter (fun x => MvPolynomial.eval x g = 0) (Fintype.piFinset T)).card := by
    refine Finset.card_nbij' (fun x => x ∘ e.symm) (fun y => y ∘ e) ?_ ?_ ?_ ?_ <;>
      intro x hx
    · simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx ⊢
      refine ⟨fun i => hx.1 (e.symm i), ?_⟩
      simpa [g, MvPolynomial.eval_rename, Function.comp_assoc] using hx.2
    · simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx ⊢
      exact ⟨fun i => by simpa [T] using hx.1 (e i), by
        simpa [g, MvPolynomial.eval_rename] using hx.2⟩
    · funext i
      simp
    · funext i
      simp
  have hprod_eq : ∏ i, (T i).card = ∏ i, (S i).card :=
    e.symm.prod_comp (fun i => (S i).card)
  rw [hcard, ← hprod_eq]
  exact key

/-- The number of elements of `∀ i, ↥(S i)` whose underlying function satisfies `P` equals the
number of elements of `Fintype.piFinset (fun i => (S i).toFinset)` satisfying `P`. -/
lemma card_filter_pi_subtype_eq_piFinset
    {F : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Set F) [∀ i, Fintype ↥(S i)]
    (P : (ι → F) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun (x : ∀ i, ↥(S i)) => P fun i => (↑(x i) : F))).card =
    (Finset.filter P (Fintype.piFinset (fun i => (S i).toFinset))).card := by
  classical
  refine Finset.card_bij ?_ ?_ ?_ ?_
  · use fun a ha => fun i => a i
  · grind
  · exact fun a₁ ha₁ a₂ ha₂ h => funext fun i => Subtype.ext <| congr_fun h i
  · simp only [Finset.mem_filter, Fintype.mem_piFinset, Set.mem_toFinset, Finset.mem_univ,
    true_and, exists_prop, and_imp]
    exact fun b hb hb' => ⟨fun i => ⟨b i, hb i⟩, hb', rfl⟩

/-- If `k * m ≤ d * n` with `m > 0`, then `k / n ≤ d / m` in `ℝ≥0∞`. -/
lemma ENNReal.div_le_div_of_mul_le {k n d m : ℕ}
    (hm_pos : 0 < m) (h : k * m ≤ d * n) :
    (k : ℝ≥0∞) / n ≤ d / m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · have hk : k = 0 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact hk
      · simp at h; omega
    simp [hk]
  rw [ENNReal.div_le_iff_le_mul] <;> norm_cast
  · rw [← ENNReal.toReal_le_toReal] <;> norm_num
    · rw [div_mul_eq_mul_div, le_div_iff₀] <;> norm_cast
    · exact ENNReal.mul_ne_top (ENNReal.div_ne_top (by aesop) (by aesop)) (by aesop)
  · grind
  · exact Or.inl <| ENNReal.natCast_ne_top _

/-- A nonzero polynomial of total degree at most `D` over a finite integral domain has at most
`D * |F| ^ (|ι| - 1)` zeros, for any finite type `ι` of variables. With no variables the bound
reads `D`, which holds because a nonzero constant has no zeros. -/
theorem MvPolynomial.card_zeros_le_of_totalDegree_le
    {F : Type*} [CommRing F] [IsDomain F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : MvPolynomial ι F) (hf : f ≠ 0) {D : ℕ} (hd : f.totalDegree ≤ D) :
    (Finset.univ.filter (fun x : ι → F => MvPolynomial.eval x f = 0)).card ≤
      D * Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have key := schwartz_zippel_counting f hf (fun _ => Finset.univ) D (Fintype.card F) hd
    (fun _ => by simp)
  simp only [Fintype.piFinset_univ, Finset.card_univ, Finset.prod_const] at key
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hι | hι
  · simpa [hι] using (Nat.le_mul_of_pos_right _ hq).trans key
  · refine Nat.le_of_mul_le_mul_right ?_ hq
    simpa [mul_assoc, ← pow_succ, Nat.sub_add_cancel hι] using key
