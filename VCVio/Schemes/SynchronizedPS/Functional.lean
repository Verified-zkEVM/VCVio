/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.SynchronizedPS.Execution
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedTraceExtraction
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.TraceExtraction

/-! # Two verification-gap functionals for synchronized PS

The first functional accounts for the first secret and the second for the message-weighted
second secret. When the signing log contains at most one request per period, a fresh target
forces at least one target-period coordinate to be nonzero. This is the algebraic separation
underlying the hash reduction in Gurkan's synchronized PS proof.
-/

public section

open GroupModel.Interaction GroupModel.LinearFunctional

namespace SynchronizedPS.AGM

/-- The coefficient of one period in a unit-weighted signing message. -/
@[expose] def periodWeight {F T : Type} [Zero F] [One F] [DecidableEq T]
    (tm : T × F) (t : T) : F := if tm.1 = t then 1 else 0

/-- The two signing functionals obtained from the chronological explanation after removing
its generator position and all hash-reply positions. -/
@[expose] def signingFunctional {F T : Type} [Semiring F] [DecidableEq T]
    (weighted : Bool) (coeff : List F) (tr : List (T ⊕ (T × F))) (t : T) : F :=
  evaluate coeff.tail (tr.map (Sum.elim (fun _ => 0)
    (fun tm => periodWeight tm t * if weighted then tm.2 else 1)))

/-- Target weight minus signing weight, for either of the two secret-key coordinates. -/
@[expose] def verificationGap {F T : Type} [Ring F] [DecidableEq T]
    (weighted : Bool) (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F) (t : T) : F :=
  periodWeight tm t * (if weighted then tm.2 else 1) - signingFunctional weighted coeff tr t

private theorem evaluate_periodWeight_eq_zero {F T : Type} [Field F] [DecidableEq T]
    (weighted : Bool) (coeff : List F) (signed : List (T × F)) (t : T)
    (h : ∀ tm ∈ signed, tm.1 ≠ t) :
    evaluate coeff (signed.map (fun tm =>
      periodWeight tm t * if weighted then tm.2 else 1)) = 0 := by
  induction signed generalizing coeff with
  | nil => simp [evaluate]
  | cons tm rest ih =>
    simp only [List.map_cons, evaluate_cons]
    rw [show periodWeight tm t = 0 by simp [periodWeight, h tm (by simp)]]
    simpa using ih coeff.tail (fun m hm => h m (by simp [hm]))

private theorem target_gap_ne_zero {F T : Type} [Field F] [DecidableEq T]
    (coeff : List F) (signed : List (T × F)) (tm : T × F)
    (hperiod : AggregateSignatureAlg.Synchronized.OnePerPeriod signed) (hfresh : tm ∉ signed) :
    1 - evaluate coeff (signed.map (fun m => periodWeight m tm.1)) ≠ 0 ∨
      tm.2 - evaluate coeff (signed.map (fun m => periodWeight m tm.1 * m.2)) ≠ 0 := by
  induction signed generalizing coeff with
  | nil => simp [evaluate]
  | cons m rest ih =>
    have hp := List.pairwise_cons.mp hperiod
    have hf : tm ≠ m ∧ tm ∉ rest := by simpa only [List.mem_cons, not_or] using hfresh
    by_cases ht : m.1 = tm.1
    · have hrest : ∀ n ∈ rest, n.1 ≠ tm.1 := by
        intro n hn heq
        exact hp.1 n hn (ht.trans heq.symm)
      have hzero := evaluate_periodWeight_eq_zero false coeff.tail rest tm.1 hrest
      have hzero' := evaluate_periodWeight_eq_zero true coeff.tail rest tm.1 hrest
      simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hzero
      simp only [↓reduceIte] at hzero'
      simp only [periodWeight] at hzero hzero'
      simp only [List.map_cons, evaluate_cons, periodWeight, ht, ↓reduceIte, smul_eq_mul,
        mul_one, one_mul, hzero, hzero', add_zero]
      by_cases hc : coeff.headD 0 = 1
      · right
        rw [hc, one_mul, sub_ne_zero]
        intro hm
        exact hf.1 (Prod.ext ht.symm hm)
      · left
        exact sub_ne_zero.mpr (Ne.symm hc)
    · simpa only [List.map_cons, evaluate_cons, periodWeight, ht, ↓reduceIte,
        mul_zero, zero_mul, smul_zero, zero_add] using ih coeff.tail hp.2 hf.2

/-- A fresh target and a synchronized signing log force a nonzero coordinate at the target
period in at least one of the two verification-gap functionals. -/
theorem verificationGap_ne_zero {F T : Type} [Field F] [DecidableEq T]
    (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F)
    (hperiod : AggregateSignatureAlg.Synchronized.OnePerPeriod (weightedSignedMessages tr))
    (hfresh : tm ∉ weightedSignedMessages tr) :
    verificationGap false coeff tr tm tm.1 ≠ 0 ∨
      verificationGap true coeff tr tm tm.1 ≠ 0 := by
  have h := target_gap_ne_zero (signingCoefficients coeff.tail tr)
    (weightedSignedMessages tr) tm hperiod hfresh
  simpa only [verificationGap, signingFunctional, evaluate_signingCoefficients,
    periodWeight, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul] using h

/-- Scalar table evaluation of the signing functional, with optional message weighting. -/
@[expose] def signingScalar {F T : Type} [Semiring F] (weighted : Bool)
    (coeff : List F) (tr : List (T ⊕ (T × F))) (ρ : T → F) : F :=
  evaluate coeff.tail (tr.map (Sum.elim (fun _ => 0)
    (fun tm => ρ tm.1 * if weighted then tm.2 else 1)))

/-- Both secret coefficients of the aggregate representation are chronological signing sums. -/
theorem representation_secret {F T : Type} [CommSemiring F] (weighted : Bool)
    (coeff : List F) (tr : List (T ⊕ (T × F))) (ρ : T → F) :
    (if weighted then (representation coeff tr ρ).2.2 else (representation coeff tr ρ).2.1) =
      signingScalar weighted coeff tr ρ := by
  let f : (F × F × F) →ₗ[F] F :=
    (if weighted then LinearMap.snd F F F else LinearMap.fst F F F).comp
      (LinearMap.snd F F (F × F))
  have hf (v : F × F × F) : f v = if weighted then v.2.2 else v.2.1 := by
    cases weighted <;> rfl
  have he := evaluate_map f coeff ((1, 0, 0) :: tr.map (Sum.elim
    (fun t => (ρ t, 0, 0)) (fun tm => (0, ρ tm.1, ρ tm.1 * tm.2))))
  rw [hf] at he
  unfold representation
  rw [← he]
  simp only [List.map_cons, List.map_map, evaluate_cons, hf]
  cases weighted <;> simp only [Bool.false_eq_true, ↓reduceIte, smul_zero, zero_add]
  all_goals
    unfold signingScalar
    congr 1
    apply List.map_congr_left
    intro q _
    cases q <;> simp [hf]

/-- Finite scalar tables interpret the signing functional coordinate by coordinate. -/
theorem signingScalar_table {F T : Type} [CommSemiring F] [DecidableEq T]
    (weighted : Bool) (S : Finset T) (ρ : S → F) (coeff : List F)
    (tr : List (T ⊕ (T × F))) :
    signingScalar weighted coeff tr (extendTable S 0 ρ) =
      ∑ i : S, signingFunctional weighted coeff tr i.val * ρ i := by
  have hv (tm : T × F) : extendTable S 0 ρ tm.1 * (if weighted then tm.2 else 1) =
      ∑ i : S, (periodWeight tm i.val * (if weighted then tm.2 else 1)) * ρ i := by
    rw [← sum_labelWeight_mul S tm.1 ρ, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [labelWeight, periodWeight]
    ring
  unfold signingScalar signingFunctional
  simp only [evaluate_signingCoefficients]
  simp only [hv]
  rw [evaluate_weighted_map]

/-- Each verification denominator is the finite-table evaluation of its gap functional. -/
theorem verificationGap_table {F T : Type} [CommRing F] [DecidableEq T]
    (weighted : Bool) (S : Finset T) (ρ : S → F) (coeff : List F)
    (tr : List (T ⊕ (T × F))) (tm : T × F) :
    extendTable S 0 ρ tm.1 * (if weighted then tm.2 else 1) -
      signingScalar weighted coeff tr (extendTable S 0 ρ) =
        ∑ i : S, verificationGap weighted coeff tr tm i.val * ρ i := by
  rw [signingScalar_table, ← sum_labelWeight_mul S tm.1 ρ, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [verificationGap, labelWeight, periodWeight]
  ring

/-- Select the message-weighted functional exactly when the first target-period gap vanishes. -/
@[expose] def selectedWeight {F T : Type} [Field F] [DecidableEq F] [DecidableEq T]
    (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F) : Bool :=
  decide (verificationGap false coeff tr tm tm.1 = 0)

/-- The selected verification gap has a nonzero target coordinate on every fresh synchronized
signing trace. The selection depends only on the public trace and explanation coefficients. -/
theorem selectedWeight_gap_ne_zero {F T : Type} [Field F] [DecidableEq F] [DecidableEq T]
    (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F)
    (hperiod : AggregateSignatureAlg.Synchronized.OnePerPeriod (weightedSignedMessages tr))
    (hfresh : tm ∉ weightedSignedMessages tr) :
    verificationGap (selectedWeight coeff tr tm) coeff tr tm tm.1 ≠ 0 := by
  have h := verificationGap_ne_zero coeff tr tm hperiod hfresh
  unfold selectedWeight
  by_cases hx : verificationGap false coeff tr tm tm.1 = 0
  · simpa only [hx, decide_true] using h.resolve_left (not_not.mpr hx)
  · rw [decide_eq_false hx]
    exact hx

/-- Verification of a sound representation yields the two-secret scalar equation. -/
theorem scalar_relation {F : Type} [Field F] (x y c ρ m a b d : F)
    (h : a + b * x + d * y = (x + y * m + c) * ρ) :
    x * (ρ - b) + y * (ρ * m - d) = a - c * ρ := by
  linear_combination -h

/-- The first-secret quotient extracts whenever its denominator is nonzero. -/
theorem x_quotient_eq {F : Type} [Field F] (x y dx dy k : F)
    (h : x * dx + y * dy = k) (hd : dx ≠ 0) : (k - y * dy) / dx = x := by
  apply (div_eq_iff hd).2
  linear_combination -h

/-- The second-secret quotient extracts whenever its denominator is nonzero. -/
theorem y_quotient_eq {F : Type} [Field F] (x y dx dy k : F)
    (h : x * dx + y * dy = k) (hd : dy ≠ 0) : (k - x * dx) / dy = y := by
  apply (div_eq_iff hd).2
  linear_combination -h

end SynchronizedPS.AGM
