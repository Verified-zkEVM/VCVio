/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.Falcon.PrecisionTrueTree
import all LatticeCrypto.Falcon.PackedFFT

/-!
# Basis coordinates of a Falcon preimage

Write `ψ(w) = w · B` for `B = [[g, -f], [G, -F]]`, read coefficientwise (`basisCoeffFst`,
`basisCoeffSnd`). At exact FFT fields `ψ(t) = (c, 0)` (`basisCoeff_toFFTTarget`) and `ψ(t - z)` is
the integer lift of the output of `fromFFTPreimage` (`fromFFTPreimage_eq_basisCoeff`).

By the NTRU equation (`det B = q`), two integer pairs with every coordinate of `ψ(t - z)` below
`(q + 1) / 2` and the same reduction are equal (`eq_of_fromFFTPreimage_eq`), so the point mass of
`trapdoorSample` is at most the largest point mass of `ffSampling` plus the mass of the far event
`BasisFar` (`trapdoorSample_pointMass_le`).
-/

public section

open OracleComp LatticeCrypto
open scoped ENNReal ComplexConjugate

namespace Falcon

variable {p : Params}

/-! ## The basis coordinates -/

/-- Coefficient `i` of `w₀ g + w₁ G`, the first polynomial of `w · B`. -/
@[expose] noncomputable def basisCoeffFst (sk : SecretKey p) (i : Fin (2 * 2 ^ p.fftDepth))
    (w : FFTPair p.fftDepth) : ℝ :=
  RealFFTPoly.toCoeffs p.fftDepth (Primitives.mulFFT w.1 (Primitives.exactFftInt p sk.g) +
    Primitives.mulFFT w.2 (Primitives.exactFftInt p sk.capG)) i

/-- Coefficient `i` of `-(w₀ f + w₁ F)`, the second polynomial of `w · B`. -/
@[expose] noncomputable def basisCoeffSnd (sk : SecretKey p) (i : Fin (2 * 2 ^ p.fftDepth))
    (w : FFTPair p.fftDepth) : ℝ :=
  RealFFTPoly.toCoeffs p.fftDepth (-(Primitives.mulFFT w.1 (Primitives.exactFftInt p sk.f) +
    Primitives.mulFFT w.2 (Primitives.exactFftInt p sk.capF))) i

theorem fftPairLinear_basisCoeffFst (sk : SecretKey p) (i : Fin (2 * 2 ^ p.fftDepth)) :
    FFTPairLinear (basisCoeffFst sk i) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩
  · simp only [basisCoeffFst]
    rw [← RealFFTPoly.toCoeffs_add]
    refine congrArg (fun P => RealFFTPoly.toCoeffs p.fftDepth P i)
      (RealFFTPoly.ext_coord fun j => ?_)
    simp only [Prod.fst_add, Prod.snd_add, RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT]
    ring
  · simp only [basisCoeffFst]
    rw [← RealFFTPoly.toCoeffs_scaleFFT]
    refine congrArg (fun P => RealFFTPoly.toCoeffs p.fftDepth P i)
      (RealFFTPoly.ext_coord fun j => ?_)
    simp only [RealFFTPoly.coord_scaleFFT, RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT]
    ring

theorem fftPairLinear_basisCoeffSnd (sk : SecretKey p) (i : Fin (2 * 2 ^ p.fftDepth)) :
    FFTPairLinear (basisCoeffSnd sk i) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩
  · simp only [basisCoeffSnd]
    rw [← RealFFTPoly.toCoeffs_add]
    refine congrArg (fun P => RealFFTPoly.toCoeffs p.fftDepth P i)
      (RealFFTPoly.ext_coord fun j => ?_)
    simp only [Prod.fst_add, Prod.snd_add, RealFFTPoly.coord_add, RealFFTPoly.coord_neg,
      RealFFTPoly.coord_mulFFT]
    ring
  · simp only [basisCoeffSnd]
    rw [← RealFFTPoly.toCoeffs_scaleFFT]
    refine congrArg (fun P => RealFFTPoly.toCoeffs p.fftDepth P i)
      (RealFFTPoly.ext_coord fun j => ?_)
    simp only [RealFFTPoly.coord_scaleFFT, RealFFTPoly.coord_add, RealFFTPoly.coord_neg,
      RealFFTPoly.coord_mulFFT]
    ring

/-- The radius `(q + 1) / 2` beyond which a coordinate is a far representative. -/
@[expose] noncomputable def farRadius : ℝ := ((modulus : ℝ) + 1) / 2

/-- Some coordinate of `d · B` is at least `(q + 1) / 2` in absolute value. -/
@[expose] def BasisFar (sk : SecretKey p) (d : FFTPair p.fftDepth) : Prop :=
  ∃ i, farRadius ≤ |basisCoeffFst sk i d| ∨ farRadius ≤ |basisCoeffSnd sk i d|

private theorem ofCoeffs_sub {k : ℕ} (a b : Fin (2 * 2 ^ k) → ℝ) :
    RealFFTPoly.ofCoeffs k (fun i => a i - b i) =
      RealFFTPoly.ofCoeffs k a - RealFFTPoly.ofCoeffs k b := by
  refine RealFFTPoly.ext_coord fun j => ?_
  rw [RealFFTPoly.coord_sub, show (fun i => a i - b i) = fun i => a i + -b i from
    funext fun i => sub_eq_add_neg _ _, RealFFTPoly.ofCoeffs_add, RealFFTPoly.ofCoeffs_neg,
    RealFFTPoly.coord_add, RealFFTPoly.coord_neg]
  ring

private theorem toCoeffs_zero {k : ℕ} (i : Fin (2 * 2 ^ k)) :
    RealFFTPoly.toCoeffs k 0 i = 0 := by
  have h0 : Primitives.scaleFFT 0 (0 : RealFFTPoly k) = 0 := RealFFTPoly.ext_coord fun j => by
    rw [RealFFTPoly.coord_scaleFFT, RealFFTPoly.coord_zero, mul_zero]
  rw [← h0, RealFFTPoly.toCoeffs_scaleFFT, zero_mul]

private theorem exactFftTarget_eq (hn : 2 * 2 ^ p.fftDepth = p.n) (c : Rq p.n) :
    Primitives.exactFftTarget p c =
      RealFFTPoly.ofCoeffs p.fftDepth fun i => (((c.get (Fin.cast hn i)).val : ℕ) : ℝ) := by
  simp [Primitives.exactFftTarget, hn]

/-- At exact fields the target satisfies `t · B = (c, 0)` slotwise. -/
private theorem coord_basis_toFFTTarget (hn : 2 * 2 ^ p.fftDepth = p.n) (prims : Primitives p)
    (hex : prims.ExactFFT hn) (htgt : prims.fftTarget = Primitives.exactFftTarget p)
    (sk : SecretKey p) (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (c : Rq p.n)
    (j : Fin (2 ^ p.fftDepth)) :
    RealFFTPoly.coord (Primitives.mulFFT (toFFTTarget p prims c sk).1
        (Primitives.exactFftInt p sk.g) +
      Primitives.mulFFT (toFFTTarget p prims c sk).2 (Primitives.exactFftInt p sk.capG)) j =
        RealFFTPoly.coord (Primitives.exactFftTarget p c) j ∧
      RealFFTPoly.coord (-(Primitives.mulFFT (toFFTTarget p prims c sk).1
        (Primitives.exactFftInt p sk.f) +
      Primitives.mulFFT (toFFTTarget p prims c sk).2 (Primitives.exactFftInt p sk.capF))) j =
        0 := by
  have hneg : ∀ u : IntPoly p.n, RealFFTPoly.coord (prims.fftInt (-u)) j =
      -RealFFTPoly.coord (Primitives.exactFftInt p u) j := fun u => by
    rw [hex.fftInt_eq, Primitives.exactFftInt_eq p hn, ← RealFFTPoly.coord_neg,
      ← RealFFTPoly.ofCoeffs_neg]
    congr 2
    funext i
    rw [Poly.get_neg, Int.cast_neg]
  have hq := ntru_coord hn sk hntru j
  have hq0 : ((modulus : ℕ) : ℂ) ≠ 0 := by norm_num [modulus]
  have he : (((1 : ℝ) / ((modulus : ℕ) : ℝ) : ℝ) : ℂ) * ((modulus : ℕ) : ℂ) = 1 := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    exact one_div_mul_cancel hq0
  simp only [toFFTTarget, RealFFTPoly.coord_add, RealFFTPoly.coord_neg,
    RealFFTPoly.coord_mulFFT, RealFFTPoly.coord_scaleFFT, hneg, htgt, Complex.ofReal_neg]
  constructor
  · linear_combination
      ((((1 : ℝ) / ((modulus : ℕ) : ℝ) : ℝ) : ℂ) *
        RealFFTPoly.coord (Primitives.exactFftTarget p c) j) * hq +
      RealFFTPoly.coord (Primitives.exactFftTarget p c) j * he
  · ring

/-- The integer coordinates `ψ(t - z)` of a near preimage, first half: `c - (a g + b G)`. -/
private noncomputable def nearFst (hn : 2 * 2 ^ p.fftDepth = p.n) (sk : SecretKey p)
    (c : Rq p.n) (a b : Fin (2 * 2 ^ p.fftDepth) → ℤ) (i : Fin (2 * 2 ^ p.fftDepth)) : ℤ :=
  ((c.get (Fin.cast hn i)).val : ℤ) -
    (intPolyMul (Poly.ofPi fun i => a (Fin.cast hn.symm i)) sk.g +
      intPolyMul (Poly.ofPi fun i => b (Fin.cast hn.symm i)) sk.capG).get (Fin.cast hn i)

/-- The integer coordinates `ψ(t - z)` of a near preimage, second half: `a f + b F`. -/
private noncomputable def nearSnd (hn : 2 * 2 ^ p.fftDepth = p.n) (sk : SecretKey p)
    (a b : Fin (2 * 2 ^ p.fftDepth) → ℤ) (i : Fin (2 * 2 ^ p.fftDepth)) : ℤ :=
  (intPolyMul (Poly.ofPi fun i => a (Fin.cast hn.symm i)) sk.f +
    intPolyMul (Poly.ofPi fun i => b (Fin.cast hn.symm i)) sk.capF).get (Fin.cast hn i)

/-- At exact fields, for an integer pair `z`, both polynomials of `(t - z) · B` are the packed
FFTs of the integer vectors `nearFst`, `nearSnd`, and `fromFFTPreimage` is their reduction. -/
private theorem basis_sub_eq (hn : 2 * 2 ^ p.fftDepth = p.n) (prims : Primitives p)
    (hex : prims.ExactFFT hn) (htgt : prims.fftTarget = Primitives.exactFftTarget p)
    (sk : SecretKey p) (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (c : Rq p.n)
    (z : FFTPair p.fftDepth) (a b : Fin (2 * 2 ^ p.fftDepth) → ℤ)
    (ha : z.1 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (a i : ℝ)))
    (hb : z.2 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (b i : ℝ))) :
    Primitives.mulFFT (toFFTTarget p prims c sk - z).1 (Primitives.exactFftInt p sk.g) +
        Primitives.mulFFT (toFFTTarget p prims c sk - z).2 (Primitives.exactFftInt p sk.capG) =
      RealFFTPoly.ofCoeffs p.fftDepth (fun i => (nearFst hn sk c a b i : ℝ)) ∧
    -(Primitives.mulFFT (toFFTTarget p prims c sk - z).1 (Primitives.exactFftInt p sk.f) +
        Primitives.mulFFT (toFFTTarget p prims c sk - z).2 (Primitives.exactFftInt p sk.capF)) =
      RealFFTPoly.ofCoeffs p.fftDepth (fun i => (nearSnd hn sk a b i : ℝ)) ∧
    ∀ i, (fromFFTPreimage p prims c sk z).1.get (Fin.cast hn i) = (nearFst hn sk c a b i : Coeff) ∧
      (fromFFTPreimage p prims c sk z).2.get (Fin.cast hn i) = (nearSnd hn sk a b i : Coeff) := by
  have hZ₀ : Primitives.mulFFT z.1 (Primitives.exactFftInt p sk.g) +
      Primitives.mulFFT z.2 (Primitives.exactFftInt p sk.capG) =
      RealFFTPoly.ofCoeffs p.fftDepth fun i =>
        (((intPolyMul (Poly.ofPi fun i => a (Fin.cast hn.symm i)) sk.g +
          intPolyMul (Poly.ofPi fun i => b (Fin.cast hn.symm i)) sk.capG).get
            (Fin.cast hn i) : ℤ) : ℝ) := by
    rw [ha, hb, Primitives.exactFftInt_eq p hn, Primitives.exactFftInt_eq p hn]
    exact (ofCoeffs_latticePoint p hn a b sk.g sk.capG).symm
  have hZ₁ : Primitives.mulFFT z.1 (Primitives.exactFftInt p sk.f) +
      Primitives.mulFFT z.2 (Primitives.exactFftInt p sk.capF) =
      RealFFTPoly.ofCoeffs p.fftDepth fun i => (nearSnd hn sk a b i : ℝ) := by
    rw [ha, hb, Primitives.exactFftInt_eq p hn, Primitives.exactFftInt_eq p hn]
    exact (ofCoeffs_latticePoint p hn a b sk.f sk.capF).symm
  have hS₀ : RealFFTPoly.ofCoeffs p.fftDepth (fun i => (nearFst hn sk c a b i : ℝ)) =
      Primitives.exactFftTarget p c -
        (Primitives.mulFFT z.1 (Primitives.exactFftInt p sk.g) +
          Primitives.mulFFT z.2 (Primitives.exactFftInt p sk.capG)) := by
    rw [hZ₀, exactFftTarget_eq hn, ← ofCoeffs_sub]
    congr 1
    funext i
    simp only [nearFst]
    push_cast
    rfl
  refine ⟨?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hS₀]
    refine RealFFTPoly.ext_coord fun j => ?_
    have h1 := (coord_basis_toFFTTarget hn prims hex htgt sk hntru c j).1
    simp only [Prod.fst_sub, Prod.snd_sub, RealFFTPoly.coord_add, RealFFTPoly.coord_sub,
      RealFFTPoly.coord_mulFFT] at h1 ⊢
    linear_combination h1
  · rw [← hZ₁]
    refine RealFFTPoly.ext_coord fun j => ?_
    have h1 := (coord_basis_toFFTTarget hn prims hex htgt sk hntru c j).2
    simp only [Prod.fst_sub, Prod.snd_sub, RealFFTPoly.coord_add, RealFFTPoly.coord_sub,
      RealFFTPoly.coord_neg, RealFFTPoly.coord_mulFFT] at h1 ⊢
    linear_combination h1
  · have hR : prims.ifftRound (Primitives.mulFFT z.1 (prims.fftInt sk.g) +
        Primitives.mulFFT z.2 (prims.fftInt sk.capG)) =
        intPolyMul (Poly.ofPi fun i => a (Fin.cast hn.symm i)) sk.g +
          intPolyMul (Poly.ofPi fun i => b (Fin.cast hn.symm i)) sk.capG := by
      rw [ha, hb, hex.fftInt_eq, hex.fftInt_eq, ← ofCoeffs_latticePoint p hn a b sk.g sk.capG,
        hex.ifftRound_eq, RealFFTPoly.toCoeffs_ofCoeffs]
      apply Poly.ext_get_eq
      intro i
      simp [round_intCast]
    simp only [fromFFTPreimage]
    rw [hR, Rq.get_sub, toRq_get, nearFst]
    push_cast
    rw [ZMod.natCast_zmod_val]
  · have hR : prims.ifftRound (-(Primitives.mulFFT z.1 (prims.fftInt sk.f) +
        Primitives.mulFFT z.2 (prims.fftInt sk.capF))) =
        -(intPolyMul (Poly.ofPi fun i => a (Fin.cast hn.symm i)) sk.f +
          intPolyMul (Poly.ofPi fun i => b (Fin.cast hn.symm i)) sk.capF) := by
      rw [ha, hb, hex.fftInt_eq, hex.fftInt_eq, ← ofCoeffs_latticePoint p hn a b sk.f sk.capF,
        ← RealFFTPoly.ofCoeffs_neg, hex.ifftRound_eq, RealFFTPoly.toCoeffs_ofCoeffs]
      apply Poly.ext_get_eq
      intro i
      rw [Poly.get_ofPi, Poly.get_neg, Fin.cast_cast, Fin.cast_eq_self, ← Int.cast_neg,
        round_intCast]
    simp only [fromFFTPreimage]
    rw [hR, Rq.get_neg, toRq_get, Poly.get_neg, Int.cast_neg, neg_neg, nearSnd]

/-- **The target in basis coordinates.** At exact fields and on a key with the NTRU equation,
`ψ(t) = (c, 0)` with `c` read in `[0, q)`. -/
theorem basisCoeff_toFFTTarget (hn : 2 * 2 ^ p.fftDepth = p.n) (prims : Primitives p)
    (hex : prims.ExactFFT hn) (htgt : prims.fftTarget = Primitives.exactFftTarget p)
    (sk : SecretKey p) (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (c : Rq p.n)
    (i : Fin (2 * 2 ^ p.fftDepth)) :
    basisCoeffFst sk i (toFFTTarget p prims c sk) = ((c.get (Fin.cast hn i)).val : ℝ) ∧
      basisCoeffSnd sk i (toFFTTarget p prims c sk) = 0 := by
  have h1 : Primitives.mulFFT (toFFTTarget p prims c sk).1 (Primitives.exactFftInt p sk.g) +
      Primitives.mulFFT (toFFTTarget p prims c sk).2 (Primitives.exactFftInt p sk.capG) =
      Primitives.exactFftTarget p c := RealFFTPoly.ext_coord fun j =>
    (coord_basis_toFFTTarget hn prims hex htgt sk hntru c j).1
  have h2 : -(Primitives.mulFFT (toFFTTarget p prims c sk).1 (Primitives.exactFftInt p sk.f) +
      Primitives.mulFFT (toFFTTarget p prims c sk).2 (Primitives.exactFftInt p sk.capF)) = 0 :=
    RealFFTPoly.ext_coord fun j => by
      rw [(coord_basis_toFFTTarget hn prims hex htgt sk hntru c j).2, RealFFTPoly.coord_zero]
  constructor
  · rw [basisCoeffFst, h1, exactFftTarget_eq hn, RealFFTPoly.toCoeffs_ofCoeffs]
  · rw [basisCoeffSnd, h2, toCoeffs_zero]

/-- **The preimage is `ψ(t - z)` modulo `q`.** At exact fields, for an integer pair `z`,
`ψ(t - z)` is an integer vector whose reduction is `fromFFTPreimage c sk z`. -/
theorem fromFFTPreimage_eq_basisCoeff (hn : 2 * 2 ^ p.fftDepth = p.n) (prims : Primitives p)
    (hex : prims.ExactFFT hn) (htgt : prims.fftTarget = Primitives.exactFftTarget p)
    (sk : SecretKey p) (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (c : Rq p.n)
    (z : FFTPair p.fftDepth)
    (hz : ∃ a b : Fin (2 * 2 ^ p.fftDepth) → ℤ,
      z.1 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (a i : ℝ)) ∧
      z.2 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (b i : ℝ))) :
    ∃ s₁ s₂ : Fin (2 * 2 ^ p.fftDepth) → ℤ,
      (∀ i, basisCoeffFst sk i (toFFTTarget p prims c sk - z) = s₁ i ∧
        basisCoeffSnd sk i (toFFTTarget p prims c sk - z) = s₂ i) ∧
      ∀ i, (fromFFTPreimage p prims c sk z).1.get (Fin.cast hn i) = (s₁ i : Coeff) ∧
        (fromFFTPreimage p prims c sk z).2.get (Fin.cast hn i) = (s₂ i : Coeff) := by
  obtain ⟨a, b, ha, hb⟩ := hz
  obtain ⟨h₁, h₂, hred⟩ := basis_sub_eq hn prims hex htgt sk hntru c z a b ha hb
  refine ⟨nearFst hn sk c a b, nearSnd hn sk a b, fun i => ⟨?_, ?_⟩, hred⟩
  · rw [basisCoeffFst, h₁, RealFFTPoly.toCoeffs_ofCoeffs]
  · rw [basisCoeffSnd, h₂, RealFFTPoly.toCoeffs_ofCoeffs]

/-! ## Point mass of the reduced output -/

/-- **At most one near preimage.** Two integer pairs whose basis coordinates are all below
`(q + 1) / 2` and that reduce to the same preimage are equal: their difference `δ` has
`δ · B = 0`, and `det B = q` (the NTRU equation). -/
theorem eq_of_fromFFTPreimage_eq (hn : 2 * 2 ^ p.fftDepth = p.n) (prims : Primitives p)
    (hex : prims.ExactFFT hn) (htgt : prims.fftTarget = Primitives.exactFftTarget p)
    (sk : SecretKey p) (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG) (c : Rq p.n)
    (z z' : FFTPair p.fftDepth)
    (hz : ∃ a b : Fin (2 * 2 ^ p.fftDepth) → ℤ,
      z.1 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (a i : ℝ)) ∧
      z.2 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (b i : ℝ)))
    (hz' : ∃ a b : Fin (2 * 2 ^ p.fftDepth) → ℤ,
      z'.1 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (a i : ℝ)) ∧
      z'.2 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (b i : ℝ)))
    (hnear : ¬ BasisFar sk (toFFTTarget p prims c sk - z))
    (hnear' : ¬ BasisFar sk (toFFTTarget p prims c sk - z'))
    (heq : fromFFTPreimage p prims c sk z = fromFFTPreimage p prims c sk z') : z = z' := by
  obtain ⟨a, b, ha, hb⟩ := hz
  obtain ⟨a', b', ha', hb'⟩ := hz'
  obtain ⟨h₁, h₂, hred⟩ := basis_sub_eq hn prims hex htgt sk hntru c z a b ha hb
  obtain ⟨h₁', h₂', hred'⟩ := basis_sub_eq hn prims hex htgt sk hntru c z' a' b' ha' hb'
  have key : ∀ s s' : ℤ, |(s : ℝ)| < farRadius → |(s' : ℝ)| < farRadius →
      (s : Coeff) = (s' : Coeff) → s = s' := by
    intro s s' h h' hc
    have hr : farRadius = (6145 : ℝ) := by norm_num [farRadius, modulus]
    rw [hr, abs_lt] at h h'
    have hs₁ : -6145 < s := by exact_mod_cast h.1
    have hs₂ : s < 6145 := by exact_mod_cast h.2
    have hs₁' : -6145 < s' := by exact_mod_cast h'.1
    have hs₂' : s' < 6145 := by exact_mod_cast h'.2
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub s s' modulus).mp hc
    obtain ⟨k, hk⟩ := hd
    have hm : ((modulus : ℕ) : ℤ) = 12289 := rfl
    rw [hm] at hk
    omega
  simp only [BasisFar, not_exists, not_or, not_le] at hnear hnear'
  have hψ : ∀ (w : FFTPair p.fftDepth) (u : Fin (2 * 2 ^ p.fftDepth) → ℤ) i,
      Primitives.mulFFT w.1 (Primitives.exactFftInt p sk.g) +
          Primitives.mulFFT w.2 (Primitives.exactFftInt p sk.capG) =
        RealFFTPoly.ofCoeffs p.fftDepth (fun i => (u i : ℝ)) →
      basisCoeffFst sk i w = u i := fun w u i h => by
    rw [basisCoeffFst, h, RealFFTPoly.toCoeffs_ofCoeffs]
  have hψ' : ∀ (w : FFTPair p.fftDepth) (u : Fin (2 * 2 ^ p.fftDepth) → ℤ) i,
      -(Primitives.mulFFT w.1 (Primitives.exactFftInt p sk.f) +
          Primitives.mulFFT w.2 (Primitives.exactFftInt p sk.capF)) =
        RealFFTPoly.ofCoeffs p.fftDepth (fun i => (u i : ℝ)) →
      basisCoeffSnd sk i w = u i := fun w u i h => by
    rw [basisCoeffSnd, h, RealFFTPoly.toCoeffs_ofCoeffs]
  have e₁ : nearFst hn sk c a b = nearFst hn sk c a' b' := funext fun i => by
    refine key _ _ ?_ ?_ ?_
    · rw [← hψ _ _ i h₁]; exact (hnear i).1
    · rw [← hψ _ _ i h₁']; exact (hnear' i).1
    · rw [← (hred i).1, ← (hred' i).1, heq]
  have e₂ : nearSnd hn sk a b = nearSnd hn sk a' b' := funext fun i => by
    refine key _ _ ?_ ?_ ?_
    · rw [← hψ' _ _ i h₂]; exact (hnear i).2
    · rw [← hψ' _ _ i h₂']; exact (hnear' i).2
    · rw [← (hred i).2, ← (hred' i).2, heq]
  rw [e₁, ← h₁'] at h₁
  rw [e₂, ← h₂'] at h₂
  have hq0 : ((modulus : ℕ) : ℂ) ≠ 0 := by norm_num [modulus]
  refine Prod.ext (RealFFTPoly.ext_coord fun j => ?_) (RealFFTPoly.ext_coord fun j => ?_)
  · have c₁ := congrArg (fun P => RealFFTPoly.coord P j) h₁
    have c₂ := congrArg (fun P => RealFFTPoly.coord P j) h₂
    have hq := ntru_coord hn sk hntru j
    simp only [Prod.fst_sub, Prod.snd_sub, RealFFTPoly.coord_add, RealFFTPoly.coord_sub,
      RealFFTPoly.coord_neg, RealFFTPoly.coord_mulFFT] at c₁ c₂
    have h0 : ((modulus : ℕ) : ℂ) * (RealFFTPoly.coord z.1 j - RealFFTPoly.coord z'.1 j) = 0 := by
      linear_combination RealFFTPoly.coord (Primitives.exactFftInt p sk.capG) j * c₂ +
        RealFFTPoly.coord (Primitives.exactFftInt p sk.capF) j * c₁ +
        (RealFFTPoly.coord z'.1 j - RealFFTPoly.coord z.1 j) * hq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hq0)
  · have c₁ := congrArg (fun P => RealFFTPoly.coord P j) h₁
    have c₂ := congrArg (fun P => RealFFTPoly.coord P j) h₂
    have hq := ntru_coord hn sk hntru j
    simp only [Prod.fst_sub, Prod.snd_sub, RealFFTPoly.coord_add, RealFFTPoly.coord_sub,
      RealFFTPoly.coord_neg, RealFFTPoly.coord_mulFFT] at c₁ c₂
    have h0 : ((modulus : ℕ) : ℂ) * (RealFFTPoly.coord z.2 j - RealFFTPoly.coord z'.2 j) = 0 := by
      linear_combination -RealFFTPoly.coord (Primitives.exactFftInt p sk.f) j * c₁ -
        RealFFTPoly.coord (Primitives.exactFftInt p sk.g) j * c₂ +
        (RealFFTPoly.coord z'.2 j - RealFFTPoly.coord z.2 j) * hq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hq0)

/-- **Point mass of the reduced output**: at most the largest point mass of `ffSampling` plus the
mass of the far event, for every `x`. -/
theorem trapdoorSample_pointMass_le (hn : 2 * 2 ^ p.fftDepth = p.n) (prims : Primitives p)
    (hex : prims.ExactFFT hn) (htgt : prims.fftTarget = Primitives.exactFftTarget p)
    (pk : PublicKey p) (sk : SecretKey p) (hntru : ntruEquation p sk.f sk.g sk.capF sk.capG)
    (c : Rq p.n) (x : Rq p.n × Rq p.n) :
    Pr{let y ← (falconPSF p prims).trapdoorSample pk sk c}[y = x] ≤
      (⨆ z, Pr{let w ← prims.ffSampling p.fftDepth (toFFTTarget p prims c sk) sk.tree}[w = z]) +
        Pr{let z ← prims.ffSampling p.fftDepth (toFFTTarget p prims c sk) sk.tree}[
          BasisFar sk (toFFTTarget p prims c sk - z)] := by
  set t := toFFTTarget p prims c sk with ht
  set ffs := prims.ffSampling p.fftDepth t sk.tree with hffs
  have hts : (falconPSF p prims).trapdoorSample pk sk c = fromFFTPreimage p prims c sk <$> ffs := by
    simp only [falconPSF, map_eq_bind_pure_comp]
    rfl
  rw [hts, prEvent_map]
  calc Pr{let z ← ffs}[fromFFTPreimage p prims c sk z = x]
      ≤ Pr{let z ← ffs}[(fromFFTPreimage p prims c sk z = x ∧ ¬ BasisFar sk (t - z)) ∨
          BasisFar sk (t - z)] :=
        prEvent_mono _ _ _ fun z h => by
          by_cases hz : BasisFar sk (t - z)
          · exact Or.inr hz
          · exact Or.inl ⟨h, hz⟩
    _ ≤ Pr{let z ← ffs}[fromFFTPreimage p prims c sk z = x ∧ ¬ BasisFar sk (t - z)] +
          Pr{let z ← ffs}[BasisFar sk (t - z)] := prEvent_or_le _ _ _
    _ ≤ _ := by
      refine add_le_add ?_ le_rfl
      by_cases hnear : ∃ z₀ ∈ support ffs,
          fromFFTPreimage p prims c sk z₀ = x ∧ ¬ BasisFar sk (t - z₀)
      · obtain ⟨z₀, hz₀, hx₀, hn₀⟩ := hnear
        calc _ ≤ Pr{let z ← ffs}[z = z₀] := prEvent_mono_of_support _ _ _ fun z hz hzx =>
              eq_of_fromFFTPreimage_eq hn prims hex htgt sk hntru c z z₀
                (Primitives.ffSampling_support_ofCoeffs prims _ _ _ z hz)
                (Primitives.ffSampling_support_ofCoeffs prims _ _ _ z₀ hz₀) hzx.2 hn₀
                (hzx.1.trans hx₀.symm)
          _ ≤ _ := le_iSup (fun w => Pr{let z ← ffs}[z = w]) z₀
      · push Not at hnear
        rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => h.2 (hnear z hz h.1)]
        exact zero_le

end Falcon

end
