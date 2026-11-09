/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import LatticeCrypto.MLDSA.Arithmetic
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The ML-DSA mask box

FIPS 204's `ExpandMask` draws each coefficient of the mask `y` from `[-γ₁ + 1, γ₁]`. This file
defines the uniform distribution on that box, `sampleMaskVec`, which is the mask distribution of the
identification scheme, and counts it. `prEvent_sampleMaskVec_polyVecNorm_lt` gives the exact
probability that a sample has centered norm below `b`. At `b = γ₁ - β` this is the probability
`((2(γ₁ - β) - 1)/(2γ₁))^(256ℓ)` that a sample from the box passes the response gate. The honest
response `z = y + c·s₁` passes at the same rate, because `MLDSA.honest_pregate_evalDistEq` couples
it with a sample from the box on every `z` that passes.
-/

public section

open OracleComp OracleSpec ENNReal
open LatticeCrypto

namespace MLDSA

/-- Whether `v` lies in the range of FIPS 204's `ExpandMask`: the centered representative of every
coefficient of every component is in `[-γ₁ + 1, γ₁]`. The zero vector is included outright so that
the box is inhabited at the degenerate `γ₁ = 0`; for `γ₁ ≥ 1` it already lies in the range. -/
@[expose] def maskBounded {k : ℕ} (v : RqVec k) (gamma1 : ℕ) : Prop :=
  v = 0 ∨ ∀ (j : Fin k) (i : Fin ringDegree),
    -(gamma1 : ℤ) < centeredRepr ((v.get j).get i) ∧ centeredRepr ((v.get j).get i) ≤ gamma1

/-- The uniform distribution on the mask box. -/
noncomputable instance (k gamma1 : ℕ) : SampleableType {v : RqVec k // maskBounded v gamma1} :=
  letI : Fintype {v : RqVec k // maskBounded v gamma1} := .ofFinite _
  letI : Nonempty {v : RqVec k // maskBounded v gamma1} := ⟨⟨0, .inl rfl⟩⟩
  .ofFintype _

/-- Uniform sampling from the mask box: the ideal distribution of FIPS 204's `ExpandMask`. -/
@[expose] noncomputable def sampleMaskVec (k gamma1 : ℕ) : ProbComp (RqVec k) :=
  Subtype.val <$> ($ᵗ {v : RqVec k // maskBounded v gamma1})

/-! ### Norms and coefficients -/

/-- The centered norm of an ML-DSA polynomial is the canonical centered infinity norm. -/
private lemma polyNorm_eq_cInfNorm (f : Rq) : polyNorm f = cInfNorm f := by
  simp only [polyNorm, normOps, vectorNegacyclicRing_backend, zmodPolyNormOps_cInfNorm]

/-- Each coefficient of each component is bounded by the vector's centered norm. -/
private lemma natAbs_centeredRepr_le_polyVecNorm {k : ℕ} (v : RqVec k) (j : Fin k)
    (i : Fin ringDegree) : (centeredRepr ((v.get j).get i)).natAbs ≤ polyVecNorm v :=
  calc (centeredRepr ((v.get j).get i)).natAbs ≤ polyNorm (v.get j) :=
        (polyNorm_eq_cInfNorm _).symm ▸ coeff_le_cInfNorm (v.get j) i
    _ ≤ polyVecNorm v := PolyVec.component_cInfNorm_le normOps v j

/-- A vector's centered norm is at most `b` exactly when every coefficient is. -/
private lemma polyVecNorm_le_iff {k b : ℕ} {v : RqVec k} :
    polyVecNorm v ≤ b ↔ ∀ j i, (centeredRepr ((v.get j).get i)).natAbs ≤ b := by
  refine (PolyVec.cInfNorm_le_iff normOps).trans (forall_congr' fun j => ?_)
  change polyNorm (v.get j) ≤ b ↔ _
  rw [polyNorm_eq_cInfNorm]
  exact cInfNorm_le_iff

/-- The triangle inequality for the centered norm of a difference. -/
lemma polyVecNorm_sub_le {k : ℕ} (z v : RqVec k) :
    polyVecNorm (z - v) ≤ polyVecNorm z + polyVecNorm v := by
  refine polyVecNorm_le_iff.mpr fun j i => ?_
  have hz := natAbs_centeredRepr_le_polyVecNorm z j i
  have hv := natAbs_centeredRepr_le_polyVecNorm v j i
  have hget : ((z - v).get j).get i = (z.get j).get i + -(v.get j).get i := by
    simp only [Vector.get_eq_getElem, Vector.getElem_sub]
    exact (coeffRing.coeff_sub _ _ i).trans (sub_eq_add_neg _ _)
  simp only [centeredRepr_eq_valMinAbs] at hz hv ⊢
  rw [hget]
  have hneg := ZMod.natAbs_valMinAbs_neg ((v.get j).get i)
  have hadd := ZMod.natAbs_valMinAbs_add_le ((z.get j).get i) (-(v.get j).get i)
  have htri := Int.natAbs_add_le ((z.get j).get i).valMinAbs (-(v.get j).get i).valMinAbs
  omega

/-- A vector of centered norm below `γ₁` lies in the mask box. -/
lemma maskBounded_of_polyVecNorm_lt {k gamma1 : ℕ} {v : RqVec k} (hv : polyVecNorm v < gamma1) :
    maskBounded v gamma1 := by
  refine .inr fun j i => ?_
  have h := natAbs_centeredRepr_le_polyVecNorm v j i
  omega

/-- For `γ₁ ≥ 1` the mask box is exactly the coefficient range. -/
lemma maskBounded_iff {k gamma1 : ℕ} (hgamma1 : 0 < gamma1) {v : RqVec k} :
    maskBounded v gamma1 ↔ ∀ (j : Fin k) (i : Fin ringDegree),
      -(gamma1 : ℤ) < centeredRepr ((v.get j).get i) ∧
        centeredRepr ((v.get j).get i) ≤ gamma1 := by
  refine ⟨?_, .inr⟩
  rintro (rfl | h) j i
  · have hz : polyVecNorm (0 : RqVec k) ≤ 0 := polyVecNorm_le_iff.mpr fun j i => by
      have hj : (0 : RqVec k).get j = (0 : Rq) := by
        change (0 : Vector Rq k).get j = 0
        simp [Vector.get]
      have hi : Vector.get (0 : Rq) i = (0 : Coeff) := NegacyclicRing.coeff_zero coeffRing i
      rw [hj, hi]
      simp [centeredRepr_eq_valMinAbs]
    have h := natAbs_centeredRepr_le_polyVecNorm (0 : RqVec k) j i
    omega
  · exact h j i

/-! ### Counting -/

/-- The number of vectors whose centered coefficients all lie in an interval `(a, b]` inside the
centered window of `ℤ_q`. -/
private lemma natCard_coeffBox (k : ℕ) {a b : ℤ} (ha : -(modulus : ℤ) < a * 2)
    (hb : b * 2 ≤ modulus) :
    Nat.card {v : RqVec k // ∀ (j : Fin k) (i : Fin ringDegree),
        a < centeredRepr ((v.get j).get i) ∧ centeredRepr ((v.get j).get i) ≤ b} =
      (b - a).toNat ^ (ringDegree * k) := by
  have hcast : ∀ z : Set.Ioc a b, centeredRepr ((z.1 : ℤ) : Coeff) = z.1 := fun z =>
    centeredRepr_intCast_eq z.1 (by have := z.2.1; omega) (by have := z.2.2; omega)
  have hget : ∀ (f : Fin k → Fin ringDegree → Set.Ioc a b) (j : Fin k) (i : Fin ringDegree),
      ((Vector.ofFn fun j => (Poly.ofPi fun i => ((f j i).1 : Coeff) : Rq)).get j).get i =
        ((f j i).1 : Coeff) := fun f j i => by
    rw [Poly.get_vectorOfFn]
    exact Poly.get_ofPi _ i
  let e : {v : RqVec k // ∀ (j : Fin k) (i : Fin ringDegree),
        a < centeredRepr ((v.get j).get i) ∧ centeredRepr ((v.get j).get i) ≤ b} ≃
      (Fin k → Fin ringDegree → Set.Ioc a b) :=
    { toFun := fun v j i => ⟨centeredRepr ((v.1.get j).get i), v.2 j i⟩
      invFun := fun f => ⟨Vector.ofFn fun j => (Poly.ofPi fun i => ((f j i).1 : Coeff) : Rq),
        fun j i => by rw [hget, hcast]; exact (f j i).2⟩
      left_inv := fun v => Subtype.ext <| Vector.ext fun j hj => Poly.ext_get_eq fun i => by
        have := hget (fun j i => ⟨centeredRepr ((v.1.get j).get i), v.2 j i⟩) ⟨j, hj⟩ i
        exact this.trans (centeredRepr_intCast ((v.1.get ⟨j, hj⟩).get i)).symm
      right_inv := fun f => by
        funext j i
        refine Subtype.ext ?_
        change centeredRepr ((Vector.ofFn fun j =>
          (Poly.ofPi fun i => ((f j i).1 : Coeff) : Rq)).get j |>.get i) = _
        rw [hget, hcast] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  simp [pow_mul]

/-- The exact probability that a sample from the mask box has centered norm below `b`, for
`0 < b ≤ γ₁` and a box inside the centered window of `ℤ_q`. -/
theorem prEvent_sampleMaskVec_polyVecNorm_lt (k : ℕ) {gamma1 b : ℕ} (hb : 0 < b)
    (hbgamma1 : b ≤ gamma1) (hq : 2 * gamma1 < modulus) :
    Pr{let z ← sampleMaskVec k gamma1}[polyVecNorm z < b] =
      ((2 * b - 1 : ℕ) : ℝ≥0∞) ^ (ringDegree * k) /
        ((2 * gamma1 : ℕ) : ℝ≥0∞) ^ (ringDegree * k) := by
  classical
  let : Fintype {v : RqVec k // maskBounded v gamma1} := .ofFinite _
  have hgamma1 : 0 < gamma1 := by omega
  have hden : Fintype.card {v : RqVec k // maskBounded v gamma1} =
      (2 * gamma1) ^ (ringDegree * k) := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (Equiv.subtypeEquivRight fun v => maskBounded_iff hgamma1),
      natCard_coeffBox k (a := -(gamma1 : ℤ)) (b := gamma1) (by omega) (by omega)]
    congr 1
    omega
  have hnum : (Finset.univ.filter fun a : {v : RqVec k // maskBounded v gamma1} =>
      polyVecNorm a.1 < b).card = (2 * b - 1) ^ (ringDegree * k) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    have hgate : ∀ v : RqVec k, polyVecNorm v < b ↔ ∀ (j : Fin k) (i : Fin ringDegree),
        -(b : ℤ) < centeredRepr ((v.get j).get i) ∧
          centeredRepr ((v.get j).get i) ≤ (b : ℤ) - 1 := fun v => by
      rw [Nat.lt_iff_le_pred hb, polyVecNorm_le_iff]
      exact forall_congr' fun j => forall_congr' fun i => by omega
    let e : {a : {v : RqVec k // maskBounded v gamma1} // polyVecNorm a.1 < b} ≃
        {v : RqVec k // ∀ (j : Fin k) (i : Fin ringDegree),
          -(b : ℤ) < centeredRepr ((v.get j).get i) ∧
            centeredRepr ((v.get j).get i) ≤ (b : ℤ) - 1} :=
      { toFun := fun a => ⟨a.1.1, (hgate _).mp a.2⟩
        invFun := fun v => ⟨⟨v.1, maskBounded_of_polyVecNorm_lt
          (((hgate _).mpr v.2).trans_le hbgamma1)⟩, (hgate _).mpr v.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, natCard_coeffBox k (a := -(b : ℤ)) (b := (b : ℤ) - 1)
      (by omega) (by omega)]
    congr 1
    omega
  rw [sampleMaskVec, prEvent_map]
  simp only [SampleableType.prEvent_uniformSample, hnum, hden]
  push_cast
  rfl

end MLDSA
