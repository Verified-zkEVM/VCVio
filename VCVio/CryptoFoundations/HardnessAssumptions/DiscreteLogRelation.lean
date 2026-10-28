/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.Constructions.SampleableType.SchwartzZippel

/-!
# The discrete-log relation problem

An adversary receives `n` independently uniform multiples of a generator and seeks a nonzero
vector of coefficients whose linear combination vanishes. Programming each basis element as
`x i • g + y i • Z` gives a reduction to discrete logarithm with additive loss `1 / |F|`.

Reference: Joseph Jaeger and Stefano Tessaro, *Expected-Time Cryptography: Generic Techniques
and Applications to Concrete Soundness*, https://eprint.iacr.org/2020/1213, Lemma 3.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace DiscreteLogRelation

variable {F G : Type} {n : ℕ}

/-- A relation adversary returns coefficients for a supplied vector of group elements. -/
abbrev Adversary (F G : Type) (n : ℕ) := (Fin n → G) → ProbComp (Fin n → F)

/-- Sample a uniform basis and accept a nonzero coefficient vector with vanishing group sum. -/
@[expose] def experiment [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (A : Adversary F G n) : ProbComp Bool := do
  let x ← $ᵗ (Fin n → F)
  let a ← A (fun i => x i • g)
  return decide (a ≠ 0 ∧ ∑ i, a i • (x i • g) = 0)

/-- Program the basis with the discrete-log challenge and extract by dividing its coefficient
into the negated generator coefficient, returning zero when that denominator vanishes. -/
@[expose] def reduction [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G]
    (A : Adversary F G n) : DiffieHellman.DLogAdversary F G := fun g Z => do
  let x ← $ᵗ (Fin n → F)
  let y ← $ᵗ (Fin n → F)
  let a ← A (fun i => x i • g + y i • Z)
  return if ∑ i, a i * y i ≠ 0 then -(∑ i, a i * x i) / (∑ i, a i * y i) else 0

private theorem linear_zero_le [Field F] [Fintype F] [SampleableType F]
    (a : Fin n → F) (ha : a ≠ 0) :
    Pr{let y ← $ᵗ (Fin n → F)}[∑ i, a i * y i = 0] ≤
      (1 : ℝ≥0∞) / Fintype.card F := by
  classical
  let p : MvPolynomial (Fin n) F := ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i
  have hn : p ≠ 0 := by
    intro h
    apply ha
    funext i
    have he := congrArg (MvPolynomial.eval (Pi.single i 1)) h
    simpa [p, Pi.single_apply, mul_ite] using he
  have hd : p.totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  simpa [p] using prob_eval_zero_univ_le_div p hn hd

private theorem programmed_eq [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] (g : G) (A : Adversary F G n) (z : F) :
    (do
      let x ← $ᵗ (Fin n → F)
      let y ← $ᵗ (Fin n → F)
      let a ← A (fun i => x i • g + y i • (z • g))
      pure (x, y, a)) =ᵈ
    (do
      let t ← $ᵗ (Fin n → F)
      let a ← A (fun i => t i • g)
      let y ← $ᵗ (Fin n → F)
      pure ((fun i => t i - y i * z), y, a)) := by
  let f := fun (x y : Fin n → F) => do
    let a ← A (fun i => x i • g + y i • (z • g))
    (pure (x, y, a) : ProbComp _)
  let k := fun (t y : Fin n → F) => do
    let a ← A (fun i => t i • g)
    (pure ((fun i => t i - y i * z), y, a) : ProbComp _)
  have hshift (y : Fin n → F) :
      (($ᵗ (Fin n → F)) >>= fun x => f x y) =ᵈ
        (($ᵗ (Fin n → F)) >>= fun t => k t y) := by
    have hb : Function.Bijective (fun t : Fin n → F => fun i => t i - y i * z) := by
      constructor
      · intro t u h
        funext i
        exact (sub_left_inj).mp (congrFun h i)
      · intro x
        exact ⟨fun i => x i + y i * z, by funext i; simp⟩
    have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective hb).bind_left
      (fun x => f x y)
    simpa only [f, k, bind_map_left, smul_smul, ← add_smul, sub_add_cancel] using h.symm
  exact (OracleComp.EvalDistEq.bind_bind_swap _ _ f).trans
    ((EvalDistEq.bind_right _ hshift).trans
      ((OracleComp.EvalDistEq.bind_bind_swap _ _ (fun y t => k t y)).trans
        (EvalDistEq.bind_right _ (fun t => OracleComp.EvalDistEq.bind_bind_swap
          ($ᵗ (Fin n → F)) (A (fun i => t i • g))
          (fun y a => pure ((fun i => t i - y i * z), y, a))))))

/-- Relation finding reduces to discrete logarithm with additive loss `1 / |F|`, including
an empty input vector. The hidden mask is sampled independently after the adversary's output. -/
theorem experiment_le [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : Function.Bijective (· • g : F → G)) (A : Adversary F G n) :
    Pr{let b ← experiment g A}[b = true] ≤
      Pr{let b ← DiffieHellman.dlogExperiment g (reduction A)}[b = true] +
        1 / Fintype.card F := by
  let R : ProbComp (F × (Fin n → F) × (Fin n → F) × (Fin n → F)) := do
    let z ← $ᵗ F
    let t ← $ᵗ (Fin n → F)
    let a ← A (fun i => t i • g)
    let y ← $ᵗ (Fin n → F)
    pure (z, t, y, a)
  let win := fun w : F × (Fin n → F) × (Fin n → F) × (Fin n → F) =>
    w.2.2.2 ≠ 0 ∧ ∑ i, w.2.2.2 i * w.2.1 i = 0
  let success := fun w : F × (Fin n → F) × (Fin n → F) × (Fin n → F) =>
    (if ∑ i, w.2.2.2 i * w.2.2.1 i ≠ 0 then
      -(∑ i, w.2.2.2 i * (w.2.1 i - w.2.2.1 i * w.1)) /
        (∑ i, w.2.2.2 i * w.2.2.1 i) else 0) = w.1
  have hgroup (t a : Fin n → F) :
      (∑ i, a i • (t i • g) = 0) ↔ ∑ i, a i * t i = 0 := by
    rw [show (∑ i, a i • (t i • g)) = (∑ i, a i * t i) • g by
      simp only [smul_smul, Finset.sum_smul]]
    exact ⟨fun h => hg.injective (h.trans (zero_smul F g).symm), fun h => by rw [h, zero_smul]⟩
  have hw : Pr{let w ← R}[win w] = Pr{let b ← experiment g A}[b = true] := by
    simp only [R, win, experiment, prEvent_norm, decide_eq_true_eq, hgroup]
    simp only [← bind_pure_comp, OracleComp.prEvent_bind_const]
    apply prEvent_bind_congr_of_support
    intro t _
    apply prEvent_bind_congr_of_support
    intro a _
    exact OracleComp.prEvent_bind_const _ _
  have hs : Pr{let w ← R}[success w] =
      Pr{let b ← DiffieHellman.dlogExperiment g (reduction A)}[b = true] := by
    simp only [R, success, DiffieHellman.dlogExperiment, reduction, prEvent_norm,
      decide_eq_true_eq]
    apply prEvent_bind_congr_of_support
    intro z _
    have h := (programmed_eq g A z).prEvent_eq (fun w =>
      (if ∑ i, w.2.2 i * w.2.1 i ≠ 0 then
        -(∑ i, w.2.2 i * w.1 i) / (∑ i, w.2.2 i * w.2.1 i) else 0) = z)
    simpa only [prEvent_norm] using h.symm
  have hextract (z : F) (t y a : Fin n → F) (ht : ∑ i, a i * t i = 0)
      (hy : ∑ i, a i * y i ≠ 0) :
      -(∑ i, a i * (t i - y i * z)) / (∑ i, a i * y i) = z := by
    rw [show (∑ i, a i * (t i - y i * z)) =
      (∑ i, a i * t i) - (∑ i, a i * y i) * z by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]]
    rw [ht, zero_sub, neg_neg, mul_div_cancel_left₀ _ hy]
  have hb : Pr{let w ← R}[win w ∧ ¬ success w] ≤
      (1 : ℝ≥0∞) / Fintype.card F := by
    have bind_le {α : Type} (mx : ProbComp α) (f : α → ProbComp Prop)
        (h : ∀ x, prEvent (f x) ≤ (1 : ℝ≥0∞) / Fintype.card F) :
        prEvent (mx >>= f) ≤ (1 : ℝ≥0∞) / Fintype.card F := by
      simpa only [id_map] using prEvent_bind_le_of_forall_le mx f id
        (fun x => by simpa only [id_map] using h x)
    simp only [R, prEvent_norm]
    apply bind_le
    intro z
    apply bind_le
    intro t
    apply bind_le
    intro a
    by_cases ha : a = 0
    · simp [win, ha]
    · refine (prEvent_mono ($ᵗ (Fin n → F) : ProbComp _)
        (fun y => win (z, t, y, a) ∧ ¬ success (z, t, y, a))
        (fun y => ∑ i, a i * y i = 0) ?_).trans (linear_zero_le a ha)
      intro y h
      by_contra hy
      exact h.2 (by simpa only [success, ite_eq_left hy] using hextract z t y a h.1.2 hy)
  rw [← hw, ← hs]
  exact (prEvent_le_prEvent_add_prEvent_and_not R win success).trans (add_le_add le_rfl hb)

end DiscreteLogRelation
