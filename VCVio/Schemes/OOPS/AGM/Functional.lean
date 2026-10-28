/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.OOPS.Admissibility
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedTraceExtraction
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.TraceExtraction

/-! # The OOPS verification-gap functional

The signing functional uses the explanation coefficients at the actual signing positions.
Freshness and the target-topic degree restriction make its difference from the target
weight nonzero, including transcripts with repeated messages or arbitrary other topics.
-/

public section

open GroupModel.Interaction GroupModel.LinearFunctional

namespace OOPS.AGM

/-- The signing part of a chronological explanation, excluding its initial generator
coefficient and all hash-reply coefficients. -/
@[expose] def signingFunctional {F T : Type} [Semiring F] [DecidableEq T]
    (degree : ℕ) (coeff : List F)
    (tr : List ((T × Fin (degree + 1)) ⊕ (F × T))) : T × Fin (degree + 1) → F :=
  evaluate coeff.tail (tr.map (Sum.elim (fun _ => 0) (fun m i => weight degree i m)))

/-- The signing functional is the weighted sum over exactly the signing occurrences. -/
theorem signingFunctional_eq_sum {F T : Type} [Semiring F] [DecidableEq T]
    (degree : ℕ) (coeff : List F)
    (tr : List ((T × Fin (degree + 1)) ⊕ (F × T))) (i : T × Fin (degree + 1)) :
    signingFunctional degree coeff tr i =
      ∑ q : Fin (weightedSignedMessages tr).length,
        ((signingCoefficients coeff.tail tr)[q.val]?).getD 0 *
          weight degree i ((weightedSignedMessages tr).get q) := by
  unfold signingFunctional
  rw [evaluate_signingCoefficients, evaluate_map_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- An admissible fresh target has a nonzero verification-gap coordinate on its own topic.
The coefficients are arbitrary and may depend on the complete adaptive transcript. -/
theorem exists_signingFunctional_gap_ne_zero {F T : Type}
    [Field F] [DecidableEq F] [DecidableEq T] (degree : ℕ) (coeff : List F)
    (tr : List ((T × Fin (degree + 1)) ⊕ (F × T))) (mt : F × T)
    (hdegree : admissible degree mt (weightedSignedMessages tr))
    (hfresh : mt ∉ weightedSignedMessages tr) :
    ∃ j : Fin (degree + 1),
      weight degree (mt.2, j) mt - signingFunctional degree coeff tr (mt.2, j) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_gapCoeff_ne_zero_of_admissible (weightedSignedMessages tr) mt
    (fun q => ((signingCoefficients coeff.tail tr)[q.val]?).getD 0) hdegree hfresh
  exact ⟨j, by simpa only [gapCoeff, signingFunctional_eq_sum] using hj⟩

/-- Polynomial hashing against a finite table equals its weight-family evaluation.
The table is zero outside the cover, and the topic type may be infinite. -/
theorem sum_terms_extendTable_eq {F T : Type} [CommSemiring F] [DecidableEq T]
    (degree : ℕ) (S : Finset (T × Fin (degree + 1))) (ρ : S → F) (mt : F × T) :
    ((terms degree mt).map fun p => p.2 * extendTable S 0 ρ p.1).sum =
      ∑ i : S, weight degree i.val mt * ρ i := by
  classical
  rw [terms, List.map_ofFn, List.sum_ofFn]
  simp only [← sum_labelWeight_mul, Finset.mul_sum, Function.comp_def, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul]
  congr 1
  by_cases ht : mt.2 = i.val.1
  · simp [labelWeight, weight, Prod.ext_iff, ht, eq_comm]
  · simp [labelWeight, weight, Prod.ext_iff, ht, Ne.symm ht]

/-- Interpreting the signing functional with a finite scalar table gives the corresponding
chronological signing contribution. -/
theorem signingFunctional_table {F T : Type} [CommSemiring F] [DecidableEq T]
    (degree : ℕ) (S : Finset (T × Fin (degree + 1))) (ρ : S → F) (coeff : List F)
    (tr : List ((T × Fin (degree + 1)) ⊕ (F × T))) :
    evaluate coeff.tail (tr.map (Sum.elim (fun _ => 0)
      (fun m => ((terms degree m).map fun p => p.2 * extendTable S 0 ρ p.1).sum))) =
      ∑ i : S, signingFunctional degree coeff tr i.val * ρ i := by
  rw [evaluate_signingCoefficients]
  simp only [sum_terms_extendTable_eq]
  rw [evaluate_weighted_map]
  simp only [evaluate_map_eq_sum, smul_eq_mul, signingFunctional_eq_sum]

/-- The good reduction's affine explanation in chronological order, with the generator first. -/
@[expose] def goodRepresentation {F T : Type} [Semiring F] (degree : ℕ)
    (coeff : List F) (tr : List ((T × Fin (degree + 1)) ⊕ (F × T)))
    (ρ : T × Fin (degree + 1) → F) : F × F :=
  evaluate coeff ((1, 0) :: tr.map (Sum.elim (fun i => (ρ i, 0))
    (fun m => (0, ((terms degree m).map fun p => p.2 * ρ p.1).sum))))

/-- The linear coefficient of the good explanation is precisely the signing functional. -/
theorem goodRepresentation_snd {F T : Type} [CommSemiring F] [DecidableEq T]
    (degree : ℕ) (S : Finset (T × Fin (degree + 1))) (ρ : S → F) (coeff : List F)
    (tr : List ((T × Fin (degree + 1)) ⊕ (F × T))) :
    (goodRepresentation degree coeff tr (extendTable S 0 ρ)).2 =
      ∑ i : S, signingFunctional degree coeff tr i.val * ρ i := by
  let inputs : List (F × F) := (1, 0) :: tr.map (Sum.elim
    (fun i => (extendTable S 0 ρ i, 0))
    (fun m => (0, ((terms degree m).map fun p => p.2 * extendTable S 0 ρ p.1).sum)))
  have h := evaluate_map (LinearMap.snd F F F) coeff inputs
  change evaluate coeff (inputs.map Prod.snd) = (goodRepresentation degree coeff tr _).2 at h
  rw [← h]
  have hi : inputs.map Prod.snd = 0 :: tr.map (Sum.elim (fun _ => 0)
      (fun m => ((terms degree m).map fun p => p.2 * extendTable S 0 ρ p.1).sum)) := by
    simp only [inputs, List.map_cons, List.map_map]
    congr 2
    funext q
    cases q <;> rfl
  rw [hi, evaluate_cons, smul_zero, zero_add]
  exact signingFunctional_table degree S ρ coeff tr

/-- The masked reduction's explanation uses only signing replies; generator and hash
positions carry the zero pair. -/
@[expose] def maskRepresentation {F T : Type} [Semiring F] (degree : ℕ)
    (coeff : List F) (tr : List ((T × Fin (degree + 1)) ⊕ (F × T)))
    (a b : T × Fin (degree + 1) → F) : F × F :=
  evaluate coeff ((0, 0) :: tr.map (Sum.elim (fun _ => (0, 0))
    (fun m => (((terms degree m).map fun p => p.2 * a p.1).sum,
      ((terms degree m).map fun p => p.2 * b p.1).sum))))

/-- The two coordinates of the masked explanation evaluate the same signing functional
on the slope table and the offset table. -/
theorem maskRepresentation_eq {F T : Type} [CommSemiring F] [DecidableEq T]
    (degree : ℕ) (S : Finset (T × Fin (degree + 1))) (a b : S → F) (coeff : List F)
    (tr : List ((T × Fin (degree + 1)) ⊕ (F × T))) :
    maskRepresentation degree coeff tr (extendTable S 0 a) (extendTable S 0 b) =
      (∑ i : S, signingFunctional degree coeff tr i.val * a i,
        ∑ i : S, signingFunctional degree coeff tr i.val * b i) := by
  let inputs : List (F × F) := (0, 0) :: tr.map (Sum.elim (fun _ => (0, 0))
    (fun m => (((terms degree m).map fun p => p.2 * extendTable S 0 a p.1).sum,
      ((terms degree m).map fun p => p.2 * extendTable S 0 b p.1).sum)))
  apply Prod.ext
  · have h := evaluate_map (LinearMap.fst F F F) coeff inputs
    change evaluate coeff (inputs.map Prod.fst) =
      (maskRepresentation degree coeff tr _ _).1 at h
    rw [← h]
    have hi : inputs.map Prod.fst = 0 :: tr.map (Sum.elim (fun _ => 0)
        (fun m => ((terms degree m).map fun p => p.2 * extendTable S 0 a p.1).sum)) := by
      simp only [inputs, List.map_cons, List.map_map]
      congr 2
      funext q
      cases q <;> rfl
    rw [hi, evaluate_cons, smul_zero, zero_add]
    exact signingFunctional_table degree S a coeff tr
  · have h := evaluate_map (LinearMap.snd F F F) coeff inputs
    change evaluate coeff (inputs.map Prod.snd) =
      (maskRepresentation degree coeff tr _ _).2 at h
    rw [← h]
    have hi : inputs.map Prod.snd = 0 :: tr.map (Sum.elim (fun _ => 0)
        (fun m => ((terms degree m).map fun p => p.2 * extendTable S 0 b p.1).sum)) := by
      simp only [inputs, List.map_cons, List.map_map]
      congr 2
      funext q
      cases q <;> rfl
    rw [hi, evaluate_cons, smul_zero, zero_add]
    exact signingFunctional_table degree S b coeff tr

end OOPS.AGM
