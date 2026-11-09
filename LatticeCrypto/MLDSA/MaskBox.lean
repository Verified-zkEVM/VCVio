/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import LatticeCrypto.MLDSA.Arithmetic
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The ML-DSA mask sampler

FIPS 204's `ExpandMask` decodes each coefficient of the mask `y` from a value `v < 2γ₁` as `γ₁ - v`,
so the coefficients lie in `[-γ₁ + 1, γ₁]` (`maskBounded`). `sampleMaskVec`, the identification
scheme's mask, applies the same decoding (`maskDecode`) to uniform values, coefficient by
coefficient, and is computable. When `2γ₁ < q` the decoding is injective
(`maskDecode_injective`) and lands in the range (`maskBounded_maskDecode`). It reaches every
vector of centered norm below `γ₁` (`exists_maskDecode_eq_of_polyVecNorm_lt`).

`prEvent_sampleMaskVec_polyVecNorm_lt` gives the exact probability that a mask has centered norm
below `b`. At `b = γ₁ - β` this is `((2(γ₁ - β) - 1)/(2γ₁))^(256ℓ)`, the rate at which a fresh mask
passes the response gate. The honest response `z = y + c·s₁` passes at the same rate, because
`MLDSA.honest_pregate_evalDistEq` couples it with a fresh mask on every `z` that passes.
-/

public section

open OracleComp OracleSpec ENNReal
open LatticeCrypto

namespace MLDSA

/-- The values a raw mask coefficient is drawn from: `Fin (2γ₁)` when `γ₁ ≥ 1`. The form
`Fin (2γ₁ - 1 + 1)` is nonempty for every `γ₁`, so sampling it needs no hypothesis; at `γ₁ = 0`,
where FIPS 204's range is empty, the mask is `0`, and the lemmas below that need `0 < γ₁` say so. -/
abbrev MaskValue (gamma1 : ℕ) : Type := Fin (2 * gamma1 - 1 + 1)

/-- A raw mask sample: one value for each coefficient of each component. -/
abbrev MaskSample (k gamma1 : ℕ) : Type := Vector (Vector (MaskValue gamma1) ringDegree) k

/-- FIPS 204's decoding of one mask coefficient: the value `v` becomes `γ₁ - v`. -/
@[expose] def maskDecodeCoeff (gamma1 : ℕ) (v : MaskValue gamma1) : Coeff :=
  (((gamma1 : ℤ) - (v.val : ℤ) : ℤ) : Coeff)

/-- Decode a raw mask sample coefficient by coefficient. -/
@[expose] def maskDecode {k gamma1 : ℕ} (a : MaskSample k gamma1) : RqVec k :=
  Vector.ofFn fun j => (Poly.ofPi fun i => maskDecodeCoeff gamma1 ((a.get j).get i) : Rq)

/-- The identification scheme's mask: uniform values decoded as in FIPS 204's `ExpandMask`. -/
@[expose] def sampleMaskVec (k gamma1 : ℕ) : ProbComp (RqVec k) :=
  maskDecode <$> ($ᵗ (MaskSample k gamma1))

/-! ### The decoding -/

/-- The coefficients of a decoded sample are the decoded values. -/
theorem maskDecode_get {k gamma1 : ℕ} (a : MaskSample k gamma1) (j : Fin k)
    (i : Fin ringDegree) :
    ((maskDecode a).get j).get i = maskDecodeCoeff gamma1 ((a.get j).get i) := by
  rw [maskDecode, Poly.get_vectorOfFn]
  exact Poly.get_ofPi _ i

/-- The centered representative of a decoded coefficient is `γ₁ - v` when `2γ₁ < q`. -/
theorem centeredRepr_maskDecodeCoeff {gamma1 : ℕ} (hq : 2 * gamma1 < modulus)
    (v : MaskValue gamma1) :
    centeredRepr (maskDecodeCoeff gamma1 v) = (gamma1 : ℤ) - (v.val : ℤ) := by
  have hv := v.isLt
  exact centeredRepr_intCast_eq _ (by omega) (by omega)

/-- The decoding is injective when `2γ₁ < q`. -/
theorem maskDecode_injective {k gamma1 : ℕ} (hq : 2 * gamma1 < modulus) :
    Function.Injective (maskDecode (k := k) (gamma1 := gamma1)) := by
  intro a b h
  refine Vector.ext fun j hj => Vector.ext fun i hi => Fin.ext ?_
  have hc := congrArg (fun z : RqVec k => centeredRepr ((z.get ⟨j, hj⟩).get ⟨i, hi⟩)) h
  simp only [maskDecode_get, centeredRepr_maskDecodeCoeff hq] at hc
  simp only [Vector.get_eq_getElem] at hc
  omega

/-- Decoded samples lie in the mask range when `0 < γ₁` and `2γ₁ < q`. -/
theorem maskBounded_maskDecode {k gamma1 : ℕ} (hgamma1 : 0 < gamma1)
    (hq : 2 * gamma1 < modulus) (a : MaskSample k gamma1) :
    maskBounded (maskDecode a) gamma1 := fun j i => by
  rw [maskDecode_get, centeredRepr_maskDecodeCoeff hq]
  have hv := ((a.get j).get i).isLt
  omega

/-- Every vector of centered norm below `γ₁` is a decoded sample. -/
theorem exists_maskDecode_eq_of_polyVecNorm_lt {k gamma1 : ℕ} {z : RqVec k}
    (hz : polyVecNorm z < gamma1) :
    ∃ a : MaskSample k gamma1, maskDecode a = z := by
  have hc : ∀ j i, (centeredRepr ((z.get j).get i)).natAbs < gamma1 := fun j i =>
    (natAbs_centeredRepr_le_polyVecNorm z j i).trans_lt hz
  refine ⟨Vector.ofFn fun j => Vector.ofFn fun i =>
    ⟨((gamma1 : ℤ) - centeredRepr ((z.get j).get i)).toNat, by have := hc j i; omega⟩, ?_⟩
  refine Vector.ext fun j hj => Poly.ext_get_eq fun i => ?_
  have hz' := maskDecode_get (Vector.ofFn fun j => Vector.ofFn fun i =>
    (⟨((gamma1 : ℤ) - centeredRepr ((z.get j).get i)).toNat, by have := hc j i; omega⟩ :
      MaskValue gamma1)) ⟨j, hj⟩ i
  refine hz'.trans ?_
  have hji := hc ⟨j, hj⟩ i
  simp only [maskDecodeCoeff, Vector.get_ofFn]
  rw [show ((gamma1 : ℤ) - (((gamma1 : ℤ) - centeredRepr ((z.get ⟨j, hj⟩).get i)).toNat : ℤ)) =
      centeredRepr ((z.get ⟨j, hj⟩).get i) by omega]
  exact (centeredRepr_intCast ((z.get ⟨j, hj⟩).get i)).symm

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

/-- The exact probability that a mask has centered norm below `b`, for `0 < b ≤ γ₁` and
`2γ₁ < q`: `(2b - 1)` of the `2γ₁` values of each coefficient decode below `b`. -/
theorem prEvent_sampleMaskVec_polyVecNorm_lt (k : ℕ) {gamma1 b : ℕ} (hb : 0 < b)
    (hbgamma1 : b ≤ gamma1) (hq : 2 * gamma1 < modulus) :
    Pr{let z ← sampleMaskVec k gamma1}[polyVecNorm z < b] =
      ((2 * b - 1 : ℕ) : ℝ≥0∞) ^ (ringDegree * k) /
        ((2 * gamma1 : ℕ) : ℝ≥0∞) ^ (ringDegree * k) := by
  classical
  have hden : Fintype.card (MaskSample k gamma1) = (2 * gamma1) ^ (ringDegree * k) := by
    rw [Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun,
      Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    congr 1
    omega
  have hgate : ∀ v : RqVec k, polyVecNorm v < b ↔ ∀ (j : Fin k) (i : Fin ringDegree),
      -(b : ℤ) < centeredRepr ((v.get j).get i) ∧
        centeredRepr ((v.get j).get i) ≤ (b : ℤ) - 1 := fun v => by
    rw [Nat.lt_iff_le_pred hb, polyVecNorm_le_iff]
    exact forall_congr' fun j => forall_congr' fun i => by omega
  have hnum : (Finset.univ.filter fun a : MaskSample k gamma1 =>
      polyVecNorm (maskDecode a) < b).card = (2 * b - 1) ^ (ringDegree * k) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    let e : {a : MaskSample k gamma1 // polyVecNorm (maskDecode a) < b} ≃
        {v : RqVec k // ∀ (j : Fin k) (i : Fin ringDegree),
          -(b : ℤ) < centeredRepr ((v.get j).get i) ∧
            centeredRepr ((v.get j).get i) ≤ (b : ℤ) - 1} :=
      Equiv.ofBijective (fun a => ⟨maskDecode a.1, (hgate _).mp a.2⟩)
        ⟨fun a a' h => Subtype.ext (maskDecode_injective hq (congrArg Subtype.val h)),
          fun v => by
            obtain ⟨a, ha⟩ := exists_maskDecode_eq_of_polyVecNorm_lt
              (((hgate _).mpr v.2).trans_le hbgamma1)
            exact ⟨⟨a, ha ▸ (hgate _).mpr v.2⟩, Subtype.ext ha⟩⟩
    rw [Nat.card_congr e, natCard_coeffBox k (a := -(b : ℤ)) (b := (b : ℤ) - 1)
      (by omega) (by omega)]
    congr 1
    omega
  rw [sampleMaskVec, prEvent_map, SampleableType.prEvent_uniformSample, hnum, hden]
  push_cast
  rfl

end MLDSA
