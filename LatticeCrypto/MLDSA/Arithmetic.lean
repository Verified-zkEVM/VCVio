/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.MLDSA.Params
public import LatticeCrypto.Ring.Sampling
public import LatticeCrypto.Ring.SchoolbookCert
public import LatticeCrypto.Ring.Transform
public import LatticeCrypto.Ring.Norms
public import LatticeCrypto.Ring.Rounding

/-!
# ML-DSA Arithmetic Assembly

Instantiates the generic negacyclic ring architecture for the ML-DSA coefficient
ring `ℤ_q[X]/(X^256 + 1)` where `q = 8380417`, and exposes scheme-local type
and operation aliases consumed by downstream ML-DSA files.

Provides:
- `coeffRing` / `polyBackend` / `polyKernel` / `coeffSemantics`: the bundled
  executable ring, backend, kernel, and proof-facing semantics.
- `Rq`, `Tq`, `RqVec`, `TqVec`, `TqMatrix`, `Quotient`: scheme-local
  carrier aliases.
- `negacyclicMul`, `quotientOfRq`: coefficient-domain multiplication and
  quotient embedding.
- `NTTRingOps` / `NTTRingLaws`: transform-domain interface and law aliases.
- `normOps`, `polyNorm`, `polyVecNorm`, `polyBounded`, `polyVecBounded`:
  norm infrastructure, with the coefficientwise characterization `polyVecNorm_le_iff` and the
  triangle inequality `polyVecNorm_sub_le`.
- `maskBounded`: the coefficient range `[-γ₁ + 1, γ₁]` of FIPS 204's `ExpandMask`.
- `RoundingOps`, `Power2RoundOps`: rounding interface aliases.

This module is mixed: the executable aliases are computable, while
`coeffSemantics` and `quotientOfRq` are `noncomputable`.
-/

@[expose] public section


namespace MLDSA

/-- Coefficients in the ML-DSA base ring. -/
abbrev Coeff := ZMod modulus

instance : NeZero modulus := ⟨by
  unfold modulus
  decide
⟩

/-- The canonical bundled coefficient-domain ring used by the current ML-DSA development. -/
abbrev coeffRing : LatticeCrypto.NegacyclicRing Coeff :=
  LatticeCrypto.vectorNegacyclicRing Coeff ringDegree

/-- The semantic backend used by the bundled ML-DSA ring. -/
abbrev polyBackend : LatticeCrypto.PolyBackend Coeff :=
  coeffRing.backend

/-- The executable kernel used by the bundled ML-DSA ring. -/
abbrev polyKernel : LatticeCrypto.PolyKernel Coeff polyBackend :=
  coeffRing.kernel

/-- The proof-facing semantic interpretation of the bundled ML-DSA ring. -/
noncomputable abbrev coeffSemantics : LatticeCrypto.NegacyclicRingSemantics coeffRing :=
  LatticeCrypto.vectorNegacyclicSemantics Coeff (by norm_num [ringDegree])

/-- The proof-facing quotient `Z_q[X] / (X^256 + 1)`. -/
abbrev Quotient := LatticeCrypto.NegacyclicRingSemantics.Quotient coeffSemantics

/-- Coefficient-domain polynomials in `R_q = Z_q[X] / (X^256 + 1)`. -/
abbrev Rq := coeffRing.Poly

instance : AddCommGroup Rq := inferInstance

/-- Transform-domain polynomials for the ML-DSA bundled ring. -/
abbrev Tq := LatticeCrypto.TransformPoly coeffRing

instance : DecidableEq Rq := by
  change DecidableEq (LatticeCrypto.Poly Coeff ringDegree)
  infer_instance

instance : DecidableEq Tq := by
  change DecidableEq (LatticeCrypto.TransformPoly coeffRing)
  infer_instance

/-- Length-`k` vectors over `R_q`. -/
abbrev RqVec (k : ℕ) := LatticeCrypto.PolyVec Rq k

/-- Length-`k` vectors over `T_q`. -/
abbrev TqVec (k : ℕ) := LatticeCrypto.PolyVec Tq k

/-- `rows × cols` row-major matrices over `T_q`. -/
abbrev TqMatrix (rows cols : ℕ) := LatticeCrypto.PolyMatrix Tq rows cols

/-- The quotient interpretation of a coefficient-domain polynomial. -/
noncomputable abbrev quotientOfRq (f : Rq) : Quotient :=
  coeffSemantics.quotientOf f

/-- The canonical executable negacyclic multiplication on `Rq`. -/
abbrev negacyclicMul (f g : Rq) : Rq :=
  coeffRing.mul f g

/-- Optional transform-domain acceleration specialized to ML-DSA carriers. -/
abbrev NTTRingOps := LatticeCrypto.TransformOps coeffRing Tq

/-- Proof-oriented transform laws specialized to ML-DSA carriers. -/
abbrev NTTRingLaws (ops : NTTRingOps) := LatticeCrypto.TransformOps.Laws ops

section Norms

/-- The canonical norm bundle on ML-DSA coefficient-domain polynomials. -/
def normOps : LatticeCrypto.NormOps polyBackend :=
  LatticeCrypto.zmodPolyNormOps modulus polyBackend

/-- The centered infinity norm of an ML-DSA polynomial. -/
abbrev polyNorm (f : Rq) : ℕ :=
  normOps.cInfNorm f

/-- The centered infinity norm of an ML-DSA polynomial vector. -/
abbrev polyVecNorm {k : ℕ} (v : RqVec k) : ℕ :=
  LatticeCrypto.PolyVec.cInfNorm normOps v

/-- Whether all coefficients of a polynomial are in `[-b, b]`. -/
def polyBounded (f : Rq) (b : ℕ) : Prop :=
  polyNorm f ≤ b

/-- Whether all coefficients of every component of a polynomial vector are in `[-b, b]`. -/
def polyVecBounded {k : ℕ} (v : RqVec k) (b : ℕ) : Prop :=
  polyVecNorm v ≤ b

/-- Whether the centered representative of every coefficient of every component of `v` lies in
`[-γ₁ + 1, γ₁]`, the range of FIPS 204's `ExpandMask`. -/
def maskBounded {k : ℕ} (v : RqVec k) (gamma1 : ℕ) : Prop :=
  ∀ (j : Fin k) (i : Fin ringDegree),
    -(gamma1 : ℤ) < LatticeCrypto.centeredRepr ((v.get j).get i) ∧
      LatticeCrypto.centeredRepr ((v.get j).get i) ≤ gamma1

/-- The centered norm of an ML-DSA polynomial is the canonical centered infinity norm. -/
theorem polyNorm_eq_cInfNorm (f : Rq) : polyNorm f = LatticeCrypto.cInfNorm f :=
  LatticeCrypto.zmodPolyNormOps_cInfNorm f

/-- Each coefficient of each component is bounded by the vector's centered norm. -/
theorem natAbs_centeredRepr_le_polyVecNorm {k : ℕ} (v : RqVec k) (j : Fin k)
    (i : Fin ringDegree) :
    (LatticeCrypto.centeredRepr ((v.get j).get i)).natAbs ≤ polyVecNorm v :=
  calc (LatticeCrypto.centeredRepr ((v.get j).get i)).natAbs ≤ polyNorm (v.get j) :=
        (polyNorm_eq_cInfNorm _).symm ▸ LatticeCrypto.coeff_le_cInfNorm (v.get j) i
    _ ≤ polyVecNorm v := LatticeCrypto.PolyVec.component_cInfNorm_le normOps v j

/-- A vector's centered norm is at most `b` exactly when every coefficient is. -/
theorem polyVecNorm_le_iff {k b : ℕ} {v : RqVec k} :
    polyVecNorm v ≤ b ↔
      ∀ j i, (LatticeCrypto.centeredRepr ((v.get j).get i)).natAbs ≤ b := by
  refine (LatticeCrypto.PolyVec.cInfNorm_le_iff normOps).trans (forall_congr' fun j => ?_)
  change polyNorm (v.get j) ≤ b ↔ _
  rw [polyNorm_eq_cInfNorm]
  exact LatticeCrypto.cInfNorm_le_iff

/-- The triangle inequality for the centered norm of a difference. -/
theorem polyVecNorm_sub_le {k : ℕ} (z v : RqVec k) :
    polyVecNorm (z - v) ≤ polyVecNorm z + polyVecNorm v := by
  refine polyVecNorm_le_iff.mpr fun j i => ?_
  have hz := natAbs_centeredRepr_le_polyVecNorm z j i
  have hv := natAbs_centeredRepr_le_polyVecNorm v j i
  have hget : ((z - v).get j).get i = (z.get j).get i + -(v.get j).get i := by
    simp only [Vector.get_eq_getElem, Vector.getElem_sub]
    exact (coeffRing.coeff_sub _ _ i).trans (sub_eq_add_neg _ _)
  simp only [LatticeCrypto.centeredRepr_eq_valMinAbs] at hz hv ⊢
  rw [hget]
  have hneg := ZMod.natAbs_valMinAbs_neg ((v.get j).get i)
  have hadd := ZMod.natAbs_valMinAbs_add_le ((z.get j).get i) (-(v.get j).get i)
  have htri := Int.natAbs_add_le ((z.get j).get i).valMinAbs (-(v.get j).get i).valMinAbs
  omega

end Norms

section Rounding

/-- Abstract rounding operations for ML-DSA, parameterized by `2 * γ₂`. -/
abbrev RoundingOps (alpha : ℕ) := LatticeCrypto.RoundingOps.{0, 0} coeffRing alpha

/-- Abstract power-2 rounding operations for ML-DSA, parameterized by `d = 13`. -/
abbrev Power2RoundOps := LatticeCrypto.Power2RoundOps coeffRing droppedBits

end Rounding

end MLDSA
