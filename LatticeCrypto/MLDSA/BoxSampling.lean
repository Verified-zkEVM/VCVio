/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import LatticeCrypto.MLDSA.Arithmetic
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Box sampling for ML-DSA

FIPS 204 draws the mask `y` and the secrets `s₁, s₂` by decoding uniform values around a center:
`ExpandMask` decodes a value `v < 2γ₁` as `γ₁ - v`, and `ExpandS` decodes a value `v ≤ 2η` as
`η - v`. `boxDecode c` applies `v ↦ c - v` to every coefficient of a raw sample whose values lie
below a width `w`, and `sampleBoxVec k w c` decodes uniform raw samples. It is computable. When
`2c < q` and `w ≤ 2c + 1`, the decoding:
- is injective (`boxDecode_injective`);
- gives coefficients with centered representatives in `(c - w, c]` (`boxDecode_mem`);
- reaches every vector with coefficients in that range (`exists_boxDecode_eq`).

The identification scheme's mask is `sampleMaskVec k γ₁ = sampleBoxVec k (2γ₁) γ₁`, with
coefficients in `[-γ₁ + 1, γ₁]` (`mem_support_sampleMaskVec`). Sampling it needs `γ₁ ≠ 0`
(`[NeZero γ₁]`), which every FIPS 204 parameter set meets. The short secrets of the
no-message-attack games are `NMA.sampleShortVec k η = sampleBoxVec k (2η + 1) η`.

`prEvent_sampleMaskVec_polyVecNorm_lt` gives the exact probability that a mask has centered norm
below `b`. At `b = γ₁ - β` this is `((2(γ₁ - β) - 1)/(2γ₁))^(256ℓ)`, the rate at which a fresh mask
passes the response gate. The honest response `z = y + c·s₁` passes at the same rate, because
`MLDSA.honest_pregate_evalDistEq` couples it with a fresh mask on every `z` that passes.
-/

public section

open OracleComp OracleSpec ENNReal
open LatticeCrypto

namespace MLDSA

/-- A raw sample of width `w`: one value `v < w` for each coefficient of each component. -/
abbrev BoxSample (k w : ℕ) : Type := Vector (Vector (Fin w) ringDegree) k

/-- FIPS 204's decoding of one coefficient around the center `c`: the value `v` becomes `c - v`. -/
@[expose] def boxDecodeCoeff (c : ℕ) {w : ℕ} (v : Fin w) : Coeff :=
  (((c : ℤ) - (v.val : ℤ) : ℤ) : Coeff)

/-- Decode a raw sample coefficient by coefficient around the center `c`. -/
@[expose] def boxDecode (c : ℕ) {k w : ℕ} (a : BoxSample k w) : RqVec k :=
  Vector.ofFn fun j => (Poly.ofPi fun i => boxDecodeCoeff c ((a.get j).get i) : Rq)

/-- Uniform raw values below `w`, decoded around the center `c`. -/
@[expose] def sampleBoxVec (k w c : ℕ) [NeZero w] : ProbComp (RqVec k) :=
  boxDecode c <$> ($ᵗ (BoxSample k w))

/-- The identification scheme's mask: values below `2γ₁` decoded as `γ₁ - v`, as in FIPS 204's
`ExpandMask`. Every FIPS 204 parameter set has `γ₁ ≠ 0`, which makes the values nonempty. -/
@[expose] def sampleMaskVec (k gamma1 : ℕ) [NeZero gamma1] : ProbComp (RqVec k) :=
  sampleBoxVec k (2 * gamma1) gamma1

/-! ### The decoding -/

/-- The coefficients of a decoded sample are the decoded values. -/
theorem boxDecode_get (c : ℕ) {k w : ℕ} (a : BoxSample k w) (j : Fin k) (i : Fin ringDegree) :
    ((boxDecode c a).get j).get i = boxDecodeCoeff c ((a.get j).get i) := by
  rw [boxDecode, Poly.get_vectorOfFn]
  exact Poly.get_ofPi _ i

/-- The centered representative of a decoded coefficient is `c - v` when `2c < q` and
`w ≤ 2c + 1`. -/
theorem centeredRepr_boxDecodeCoeff {c w : ℕ} (hq : 2 * c < modulus) (hw : w ≤ 2 * c + 1)
    (v : Fin w) :
    centeredRepr (boxDecodeCoeff c v) = (c : ℤ) - (v.val : ℤ) := by
  have hv := v.isLt
  exact centeredRepr_intCast_eq _ (by omega) (by omega)

/-- The decoding is injective when `2c < q` and `w ≤ 2c + 1`. -/
theorem boxDecode_injective {c k w : ℕ} (hq : 2 * c < modulus) (hw : w ≤ 2 * c + 1) :
    Function.Injective (boxDecode c (k := k) (w := w)) := by
  intro a b h
  refine Vector.ext fun j hj => Vector.ext fun i hi => Fin.ext ?_
  have hc := congrArg (fun z : RqVec k => centeredRepr ((z.get ⟨j, hj⟩).get ⟨i, hi⟩)) h
  simp only [boxDecode_get, centeredRepr_boxDecodeCoeff hq hw] at hc
  simp only [Vector.get_eq_getElem] at hc
  omega

/-- The coefficients of a decoded sample have centered representatives in `(c - w, c]` when
`2c < q` and `w ≤ 2c + 1`. -/
theorem boxDecode_mem {c k w : ℕ} (hq : 2 * c < modulus) (hw : w ≤ 2 * c + 1)
    (a : BoxSample k w) (j : Fin k) (i : Fin ringDegree) :
    (c : ℤ) - w < centeredRepr (((boxDecode c a).get j).get i) ∧
      centeredRepr (((boxDecode c a).get j).get i) ≤ c := by
  rw [boxDecode_get, centeredRepr_boxDecodeCoeff hq hw]
  have hv := ((a.get j).get i).isLt
  omega

/-- Every vector whose coefficients have centered representatives in `(c - w, c]` is a decoded
sample. -/
theorem exists_boxDecode_eq {c k w : ℕ} {z : RqVec k}
    (hz : ∀ j i, (c : ℤ) - w < centeredRepr ((z.get j).get i) ∧
      centeredRepr ((z.get j).get i) ≤ c) :
    ∃ a : BoxSample k w, boxDecode c a = z := by
  refine ⟨Vector.ofFn fun j => Vector.ofFn fun i =>
    ⟨((c : ℤ) - centeredRepr ((z.get j).get i)).toNat, by have := hz j i; omega⟩, ?_⟩
  refine Vector.ext fun j hj => Poly.ext_get_eq fun i => ?_
  have hz' := boxDecode_get c (Vector.ofFn fun j => Vector.ofFn fun i =>
    (⟨((c : ℤ) - centeredRepr ((z.get j).get i)).toNat, by have := hz j i; omega⟩ :
      Fin w)) ⟨j, hj⟩ i
  refine hz'.trans ?_
  have hji := hz ⟨j, hj⟩ i
  simp only [boxDecodeCoeff, Vector.get_ofFn]
  rw [show ((c : ℤ) - (((c : ℤ) - centeredRepr ((z.get ⟨j, hj⟩).get i)).toNat : ℤ)) =
      centeredRepr ((z.get ⟨j, hj⟩).get i) by omega]
  exact (centeredRepr_intCast ((z.get ⟨j, hj⟩).get i)).symm

/-! ### The mask -/

/-- Every mask lies in the mask range when `2γ₁ < q`: the support of `sampleMaskVec` is the range
that `Primitives.Laws.expandMask_bound` gives the deterministic `ExpandMask`. -/
theorem mem_support_sampleMaskVec {k gamma1 : ℕ} [NeZero gamma1] (hq : 2 * gamma1 < modulus)
    {v : RqVec k} (hv : v ∈ support (sampleMaskVec k gamma1)) : maskBounded v gamma1 := by
  simp only [sampleMaskVec, sampleBoxVec, support_map] at hv
  obtain ⟨a, -, rfl⟩ := hv
  intro j i
  have := boxDecode_mem hq (by omega) a j i
  omega

/-- Every vector of centered norm below `γ₁` is a decoded mask sample. -/
theorem exists_boxDecode_eq_of_polyVecNorm_lt {k gamma1 : ℕ} {z : RqVec k}
    (hz : polyVecNorm z < gamma1) :
    ∃ a : BoxSample k (2 * gamma1), boxDecode gamma1 a = z :=
  exists_boxDecode_eq fun j i => by
    have := (natAbs_centeredRepr_le_polyVecNorm z j i).trans_lt hz
    omega

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
theorem prEvent_sampleMaskVec_polyVecNorm_lt (k : ℕ) {gamma1 b : ℕ} [NeZero gamma1] (hb : 0 < b)
    (hbgamma1 : b ≤ gamma1) (hq : 2 * gamma1 < modulus) :
    Pr{let z ← sampleMaskVec k gamma1}[polyVecNorm z < b] =
      ((2 * b - 1 : ℕ) : ℝ≥0∞) ^ (ringDegree * k) /
        ((2 * gamma1 : ℕ) : ℝ≥0∞) ^ (ringDegree * k) := by
  classical
  have hden : Fintype.card (BoxSample k (2 * gamma1)) = (2 * gamma1) ^ (ringDegree * k) := by
    rw [Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun,
      Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  have hgate : ∀ v : RqVec k, polyVecNorm v < b ↔ ∀ (j : Fin k) (i : Fin ringDegree),
      -(b : ℤ) < centeredRepr ((v.get j).get i) ∧
        centeredRepr ((v.get j).get i) ≤ (b : ℤ) - 1 := fun v => by
    rw [Nat.lt_iff_le_pred hb, polyVecNorm_le_iff]
    exact forall_congr' fun j => forall_congr' fun i => by omega
  have hnum : (Finset.univ.filter fun a : BoxSample k (2 * gamma1) =>
      polyVecNorm (boxDecode gamma1 a) < b).card = (2 * b - 1) ^ (ringDegree * k) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    let e : {a : BoxSample k (2 * gamma1) // polyVecNorm (boxDecode gamma1 a) < b} ≃
        {v : RqVec k // ∀ (j : Fin k) (i : Fin ringDegree),
          -(b : ℤ) < centeredRepr ((v.get j).get i) ∧
            centeredRepr ((v.get j).get i) ≤ (b : ℤ) - 1} :=
      Equiv.ofBijective (fun a => ⟨boxDecode gamma1 a.1, (hgate _).mp a.2⟩)
        ⟨fun a a' h => Subtype.ext (boxDecode_injective hq (by omega) (congrArg Subtype.val h)),
          fun v => by
            obtain ⟨a, ha⟩ := exists_boxDecode_eq_of_polyVecNorm_lt
              (((hgate _).mpr v.2).trans_le hbgamma1)
            exact ⟨⟨a, ha ▸ (hgate _).mpr v.2⟩, Subtype.ext ha⟩⟩
    rw [Nat.card_congr e, natCard_coeffBox k (a := -(b : ℤ)) (b := (b : ℤ) - 1)
      (by omega) (by omega)]
    congr 1
    omega
  rw [sampleMaskVec, sampleBoxVec, prEvent_map, SampleableType.prEvent_uniformSample, hnum, hden]
  push_cast
  rfl

end MLDSA
