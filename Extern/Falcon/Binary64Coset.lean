/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all Extern.Falcon.Instance
import all LatticeCrypto.Falcon.Concrete.FloatLike
import all LatticeCrypto.Falcon.Concrete.FPR
import all LatticeCrypto.Falcon.PackedFFT
import all LatticeCrypto.Falcon.Coset
public import Extern.Falcon.Binary64FFT
public import Extern.Falcon.Instance
public import LatticeCrypto.Falcon.Coset
public import LatticeCrypto.Falcon.Security

/-!
# The coset condition at the binary64 FFT primitives

`binary64FFTPrimitives` is `Falcon.Concrete.concretePrimitives` with its three FFT conversion
fields computed by the executable binary64 code of `Extern.Falcon.FFT` on `FPR`:

- `fftInt` and `fftTarget` convert the coefficients with `fpolySetSmall` (`FPR.ofInt`) and run
  `fpolyFFT`;
- `ifftRound` reads its real input through `Binary64.encode` (significand truncated to 53 bits,
  zero below `2^(-64)`), runs `fpolyIFFT`, and rounds the real value of each output to the
  nearest integer with `round`, where the reference rounds with `fpr_rint`.

The rest of `Primitives` stays exact: `toFFTTarget`'s products and `1/q`, `ffSampling`, and the
products and sums of `fromFFTPreimage` are fixed real-valued definitions of `Primitives`, so this is
not the floating-point signer of `Extern.Falcon.Sign`, which also computes those in binary64.
The results are about `FPR`, the bit-exact binary64 emulation that `Extern.Falcon.FPRBridge`
bounds, not about the native `Float` backend. Nothing is proved about `fftTarget`.

`landsOnLattice_of_binary64FFTFields` proves `Falcon.LandsOnLattice` for any bundle with these
`fftInt` and `ifftRound` fields (`Binary64FFTFields`), for every sampler output that is the packed
FFT of an integer pair with coefficients bounded by `Z`, for keys with coefficients in
`[-127, 127]` (`KeyCoeffsLe127`) and `2 ≤ logn ≤ 9`, whenever the explicit deviation bound
`cosetDeviation (logn - 1) Z` is below `1/2`. `cosetDeviation_falcon512` evaluates it below `1/2`
at Falcon-512 for `Z = 2^16`.

The bound on sampled coefficients is the hypothesis `Falcon.SampledCoeffsLe`: `Primitives` places
no bound on `samplerZ`, on the tree, or on the target, so nothing here bounds what `ffSampling`
returns. `Falcon.sampledCoeffsLe_of_samplerZ_le` derives it only for samplers whose values are
bounded independently of the centre, which excludes Falcon's sampler and any discrete Gaussian.
The sampler loop of `concretePrimitives` (`SamplerZ.samplerZLoop`) is a `partial def`, so no bound
on its outputs beyond the `Int32` range can be proved in Lean, and that range is far outside the
regime where `cosetDeviation` is below `1/2`. The corollaries
`hpreimage_of_binary64FFTFields_of_sampledCoeffsLe`,
`verify_sign_correct_of_binary64FFTFields_of_sampledCoeffsLe` and
`verify_sign_correct_falcon512_of_binary64FFTFields_of_sampledCoeffsLe` therefore take the bound
as a hypothesis, for any bundle with these fields. `LatticeCryptoTest.FalconBinary64Coset`
instantiates them with a sampler bounded independently of the centre and a key that satisfies the
key relations; no valid Falcon key pair (`validKeyPair`) is constructed in Lean.

The argument stops at `logn = 9`: the bounds of `Extern.Falcon.FPRBridge` exclude exact results
below `2^(-1022)`, and this argument's lower bound on nonzero intermediates (`Binary64.lowAt`)
only stays above that through eight butterfly stages. At `logn = 10` the deviation bound would
also need `Z ≤ 17950`.
-/

public section

open OracleComp OracleSpec LatticeCrypto Complex

namespace Falcon.Concrete

open Falcon Falcon.FFTStages Falcon.Concrete.FPR Falcon.Concrete.FPRBridge Falcon.Concrete.Binary64
  Falcon.Concrete.FFTOps

/-! ## The binary64 FFT fields -/

/-- The packed FFT computed by the binary64 `fpolyFFT` on an array, read through `toReal`. -/
noncomputable def binary64FFTOf (p : Params) (a : Array FPR) : RealFFTPoly p.fftDepth :=
  Vector.ofFn fun i => toReal ((fpolyFFT p.logn a).getD i.1 0)

/-- The binary64 `fftInt`: `fpolySetSmall` then `fpolyFFT`. -/
noncomputable def binary64FftInt (p : Params) (f : IntPoly p.n) : RealFFTPoly p.fftDepth :=
  binary64FFTOf p (fpolySetSmall p.logn (Array.ofFn fun i : Fin p.n => Int32.ofInt (f.get i)))

/-- The binary64 `fftTarget`: the hash target's coefficients in `[0, q)` through `fpolySetSmall`,
then `fpolyFFT`. -/
noncomputable def binary64FftTarget (p : Params) (c : Rq p.n) : RealFFTPoly p.fftDepth :=
  binary64FFTOf p (fpolySetSmall p.logn
    (Array.ofFn fun i : Fin p.n => Int32.ofInt ((c.get i).val : ℤ)))

/-- The binary64 `ifftRound`: each real input read by `Binary64.encode` (significand truncated to
53 bits, zero below `2^(-64)`), `fpolyIFFT`, then the nearest integer (`round`) to the real value
of each output. The reading and the final rounding are modelling choices, not IEEE
round-to-nearest or `fpr_rint`. -/
noncomputable def binary64IfftRound (p : Params) (v : RealFFTPoly p.fftDepth) : IntPoly p.n :=
  Poly.ofPi fun i : Fin p.n => round (toReal ((fpolyIFFT p.logn
    (Array.ofFn fun j : Fin (2 * 2 ^ p.fftDepth) => encode (v.get j))).getD i.1 0))

/-- `concretePrimitives` with its three FFT fields computed by the binary64 FFT code; the sampler,
the products and `ffSampling` are those of `concretePrimitives` and `Primitives`. -/
@[expose] noncomputable def binary64FFTPrimitives (p : Params) (hn : p.n = 2 ^ p.logn) :
    Primitives p :=
  { concretePrimitives p hn with
    fftTarget := binary64FftTarget p
    fftInt := binary64FftInt p
    ifftRound := binary64IfftRound p }

/-- A primitive bundle whose `fftInt` and `ifftRound` are the binary64 ones. -/
structure Binary64FFTFields {p : Params} (prims : Primitives p) : Prop where
  fftInt_eq : prims.fftInt = binary64FftInt p
  ifftRound_eq : prims.ifftRound = binary64IfftRound p

/-- `binary64FFTPrimitives` has the binary64 FFT fields. -/
theorem binary64FFTPrimitives_binary64FFTFields (p : Params) (hn : p.n = 2 ^ p.logn) :
    Binary64FFTFields (binary64FFTPrimitives p hn) :=
  ⟨rfl, rfl⟩

/-- The codec of `binary64FFTPrimitives` is that of `concretePrimitives` and round-trips. -/
theorem binary64FFTPrimitives_decompress_compress (p : Params) (hn : p.n = 2 ^ p.logn)
    (s : IntPoly p.n) (slen : ℕ) (bytes : List Byte)
    (h : (binary64FFTPrimitives p hn).compress s slen = some bytes) :
    (binary64FFTPrimitives p hn).decompress bytes slen = some s :=
  decompress_compress p.n s slen bytes h

private theorem floatLike_zero_fpr : (FloatLike.zero : FPR) = 0 := by
  change FPR.zero = 0; rfl

/-! ## Bounds on packed FFTs -/

/-- The bound `((2 + ηF)^k - 2^k) · 254` on the error of the binary64 `fftInt` of a polynomial
with coefficients in `[-127, 127]` (`coord_binary64FftInt_sub`). -/
@[expose] noncomputable def fftError (k : ℕ) : ℝ := ((2 + etaF) ^ k - 2 ^ k) * 254

/-- **The binary64 `fftInt` of a key polynomial.** For `2 ≤ logn ≤ 9` and coefficients in
`[-127, 127]`, every slot of the binary64 `fftInt` is within `fftError (logn - 1)` of the exact
packed FFT. -/
theorem coord_binary64FftInt_sub (p : Params) (hn : p.n = 2 ^ p.logn) (h2 : 2 ≤ p.logn)
    (h9 : p.logn ≤ 9) (h : 2 * 2 ^ p.fftDepth = p.n) (f : IntPoly p.n)
    (hf : ∀ i, |f.get i| ≤ 127) (j : Fin (2 ^ p.fftDepth)) :
    ‖RealFFTPoly.coord (binary64FftInt p f) j - RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (f.get (Fin.cast h i) : ℝ)) j‖ ≤
      fftError p.fftDepth := by
  set F : ℕ → ℤ := fun i => if hi : i < p.n then f.get ⟨i, hi⟩ else 0 with hF
  have hFb : ∀ i < 2 ^ p.logn, |F i| ≤ 127 := by
    intro i hi; simp only [hF, show i < p.n by omega, dite_true]; exact hf _
  set ints := Array.ofFn fun i : Fin p.n => Int32.ofInt (f.get i) with hints
  have hintsF : ∀ i < 2 ^ p.logn, ints.getD i 0 = Int32.ofInt (F i) := by
    intro i hi
    simp [hints, hF, show i < p.n by omega, Array.getD_eq_getD_getElem?]
  have herr := fpolyFFT_int_error p.logn h2 h9 F hFb ints hintsF j.1 j.2
  have hsize : (fpolySetSmall (F := FPR) p.logn ints).size = 2 * 2 ^ (p.logn - 1) := by
    rw [size_fpolySetSmall, ← pow_succ']; congr 1; omega
  have hout := size_fpolyFFT p.logn h2 _ hsize
  have hcv := cv_eq_getD (2 ^ (p.logn - 1)) (fpolyFFT p.logn (fpolySetSmall p.logn ints)) j.1
    (by rw [hout]; have := j.2; change j.1 < 2 ^ (p.logn - 1) at this; omega)
  have hleft : RealFFTPoly.coord (binary64FftInt p f) j =
      cplx (cv (2 ^ (p.logn - 1)) (fpolyFFT p.logn (fpolySetSmall p.logn ints)) j.1) := by
    rw [hcv]
    apply Complex.ext <;>
      simp [binary64FftInt, binary64FFTOf, RealFFTPoly.coord, RealFFTPoly.re, RealFFTPoly.im, cplx,
        hints, Params.fftDepth, floatLike_zero_fpr]
  have hright : RealFFTPoly.coord (RealFFTPoly.ofCoeffs p.fftDepth fun i =>
      (f.get (Fin.cast h i) : ℝ)) j = fwdStages (p.logn - 1) (p.logn - 1)
        (fun r => (F r : ℂ) + I * (F (r + 2 ^ (p.logn - 1)) : ℂ)) j.1 := by
    rw [coord_ofCoeffs_eq_fwdStages]
    apply fwdStages_congr _ _ le_rfl _ _ _ j.1 j.2
    intro r hr
    change r < 2 ^ (p.logn - 1) at hr
    have hpow : 2 ^ p.logn = 2 * 2 ^ (p.logn - 1) := by rw [← pow_succ']; congr 1; omega
    have h1 : r < p.n := by omega
    have h2' : r + 2 ^ (p.logn - 1) < p.n := by omega
    simp [complexify, extend, hF, h1, h2', show r < 2 * 2 ^ p.fftDepth by
      change r < 2 * 2 ^ (p.logn - 1); omega, show r + 2 ^ p.fftDepth < 2 * 2 ^ p.fftDepth by
      change r + 2 ^ (p.logn - 1) < 2 * 2 ^ (p.logn - 1); omega]
    rfl
  rw [hleft, hright]
  exact herr

/-! ## Rounding at the binary64 inverse transform -/

/-- **The binary64 `ifftRound` recovers an integer polynomial.** If every slot of `v` is within
`D` of the exact packed FFT of `w`, those slots are bounded by `V`, and
`ifftDeviation (logn - 1) D V < 1/2`, then the binary64 `ifftRound` of `v` is `w`. -/
theorem binary64IfftRound_eq (p : Params) (h2 : 2 ≤ p.logn) (h9 : p.logn ≤ 9)
    (h : 2 * 2 ^ p.fftDepth = p.n) (v : RealFFTPoly p.fftDepth) (w : IntPoly p.n) (D V : ℝ)
    (hD : ∀ j, ‖RealFFTPoly.coord v j - RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (w.get (Fin.cast h i) : ℝ)) j‖ ≤ D)
    (hV : ∀ j, ‖RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (w.get (Fin.cast h i) : ℝ)) j‖ ≤ V)
    (hdev : ifftDeviation p.fftDepth D V < 1 / 2) :
    binary64IfftRound p v = w := by
  have hl : p.logn = p.fftDepth + 1 := by unfold Params.fftDepth; omega
  apply Poly.ext_get_eq
  intro i
  rw [binary64IfftRound, Poly.get_ofPi, hl]
  have := fpolyIFFT_round p.fftDepth (by unfold Params.fftDepth; omega)
    (by unfold Params.fftDepth; omega) v (fun i => w.get (Fin.cast h i)) D V hD hV hdev
    (Fin.cast h.symm i)
  simpa using this

/-! ## The lattice point -/

/-- The deviation bound of the coset condition at the binary64 primitives: sampler outputs with
coefficients bounded by `Z`, keys with coefficients bounded by `127`. -/
@[expose] noncomputable def cosetDeviation (k : ℕ) (Z : ℝ) : ℝ :=
  ifftDeviation k (2 * (2 ^ (k + 1) * Z) * fftError k)
    (2 * (2 ^ (k + 1) * Z) * (2 ^ (k + 1) * 127))

private theorem fftError_nonneg (k : ℕ) : 0 ≤ fftError k := by
  unfold fftError
  have : (2 : ℝ) ^ k ≤ (2 + etaF) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith [etaF_nonneg]) k
  nlinarith

/-- The binary64 sum of products is within `2 · 2^(k+1) Z · fftError k` of the exact one, slot by
slot. -/
private theorem coord_products_sub (p : Params) (hn : p.n = 2 ^ p.logn) (h2 : 2 ≤ p.logn)
    (h9 : p.logn ≤ 9) (h : 2 * 2 ^ p.fftDepth = p.n) (a b : Fin (2 * 2 ^ p.fftDepth) → ℤ)
    (Z : ℝ) (ha : ∀ i, |(a i : ℝ)| ≤ Z) (hb : ∀ i, |(b i : ℝ)| ≤ Z) (u₁ u₂ : IntPoly p.n)
    (hu₁ : ∀ i, |u₁.get i| ≤ 127) (hu₂ : ∀ i, |u₂.get i| ≤ 127) (j : Fin (2 ^ p.fftDepth)) :
    ‖RealFFTPoly.coord (Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
          (binary64FftInt p u₁) +
        Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
          (binary64FftInt p u₂)) j -
      RealFFTPoly.coord (Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₁.get (Fin.cast h i) : ℝ)) +
        Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₂.get (Fin.cast h i) : ℝ))) j‖ ≤
      2 * (2 ^ (p.fftDepth + 1) * Z) * fftError p.fftDepth := by
  simp only [RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT]
  have hA := RealFFTPoly.norm_coord_ofCoeffs_le p.fftDepth _ Z ha j
  have hB := RealFFTPoly.norm_coord_ofCoeffs_le p.fftDepth _ Z hb j
  have e1 := coord_binary64FftInt_sub p hn h2 h9 h u₁ hu₁ j
  have e2 := coord_binary64FftInt_sub p hn h2 h9 h u₂ hu₂ j
  set A := RealFFTPoly.coord (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ)) j
  set B := RealFFTPoly.coord (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ)) j
  calc _ = ‖A * (RealFFTPoly.coord (binary64FftInt p u₁) j - RealFFTPoly.coord
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₁.get (Fin.cast h i) : ℝ)) j) +
        B * (RealFFTPoly.coord (binary64FftInt p u₂) j - RealFFTPoly.coord
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₂.get (Fin.cast h i) : ℝ)) j)‖ := by
        congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ (2 ^ (p.fftDepth + 1) * Z) * fftError p.fftDepth +
        (2 ^ (p.fftDepth + 1) * Z) * fftError p.fftDepth := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hA e1 (norm_nonneg _) ((norm_nonneg _).trans hA))
          (mul_le_mul hB e2 (norm_nonneg _) ((norm_nonneg _).trans hB))
    _ = _ := by ring

private theorem norm_coord_products_le (p : Params) (h : 2 * 2 ^ p.fftDepth = p.n)
    (a b : Fin (2 * 2 ^ p.fftDepth) → ℤ) (Z : ℝ) (ha : ∀ i, |(a i : ℝ)| ≤ Z)
    (hb : ∀ i, |(b i : ℝ)| ≤ Z) (u₁ u₂ : IntPoly p.n) (hu₁ : ∀ i, |u₁.get i| ≤ 127)
    (hu₂ : ∀ i, |u₂.get i| ≤ 127) (j : Fin (2 ^ p.fftDepth)) :
    ‖RealFFTPoly.coord (Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₁.get (Fin.cast h i) : ℝ)) +
        Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₂.get (Fin.cast h i) : ℝ))) j‖ ≤
      2 * (2 ^ (p.fftDepth + 1) * Z) * (2 ^ (p.fftDepth + 1) * 127) := by
  simp only [RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT]
  have hA := RealFFTPoly.norm_coord_ofCoeffs_le p.fftDepth _ Z ha j
  have hB := RealFFTPoly.norm_coord_ofCoeffs_le p.fftDepth _ Z hb j
  have hU : ∀ u : IntPoly p.n, (∀ i, |u.get i| ≤ 127) → ‖RealFFTPoly.coord
      (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u.get (Fin.cast h i) : ℝ)) j‖ ≤
      2 ^ (p.fftDepth + 1) * 127 := by
    intro u hu
    exact RealFFTPoly.norm_coord_ofCoeffs_le p.fftDepth _ 127 (fun i => by exact_mod_cast hu _)
      j
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (2 ^ (p.fftDepth + 1) * Z) * (2 ^ (p.fftDepth + 1) * 127) +
        (2 ^ (p.fftDepth + 1) * Z) * (2 ^ (p.fftDepth + 1) * 127) := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hA (hU u₁ hu₁) (norm_nonneg _) ((norm_nonneg _).trans hA))
          (mul_le_mul hB (hU u₂ hu₂) (norm_nonneg _) ((norm_nonneg _).trans hB))
    _ = _ := by ring

/-- Key coefficients in `[-127, 127]`. Falcon's secret-key encoding stores `f`, `g` and `F` in at
most 8 signed bits (`f, g` in 6 bits at Falcon-512); `G` is not encoded, and its range is assumed
here. -/
@[expose] def KeyCoeffsLe127 {p : Params} (sk : SecretKey p) : Prop :=
  ∀ i, |sk.f.get i| ≤ 127 ∧ |sk.g.get i| ≤ 127 ∧ |sk.capF.get i| ≤ 127 ∧ |sk.capG.get i| ≤ 127

/-- **The lattice-point condition at the binary64 FFT fields**, for keys with coefficients in
`[-127, 127]` (`KeyCoeffsLe127`). For `2 ≤ logn ≤ 9` and a sampler output `z` that is the packed
FFT of an integer pair with coefficients bounded by `Z`, the binary64 basis application lands on
the lattice whenever the deviation bound `cosetDeviation (logn - 1) Z` is below `1/2`. -/
theorem landsOnLattice_of_binary64FFTFields (p : Params) (hn : p.n = 2 ^ p.logn)
    (h2 : 2 ≤ p.logn) (h9 : p.logn ≤ 9) (prims : Primitives p) (hb : Binary64FFTFields prims)
    (sk : SecretKey p) (hkey : KeyCoeffsLe127 sk) (Z : ℝ)
    (hdev : cosetDeviation p.fftDepth Z < 1 / 2) (z : FFTPair p.fftDepth)
    (hz : ∃ a b : Fin (2 * 2 ^ p.fftDepth) → ℤ, (∀ i, |(a i : ℝ)| ≤ Z) ∧ (∀ i, |(b i : ℝ)| ≤ Z) ∧
      z.1 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (a i : ℝ)) ∧
      z.2 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (b i : ℝ))) :
    LandsOnLattice p prims sk z := by
  obtain ⟨a, b, ha, hb', hza, hzb⟩ := hz
  have h : 2 * 2 ^ p.fftDepth = p.n := by
    rw [hn, Params.fftDepth, ← pow_succ']; congr 1; omega
  unfold LandsOnLattice
  refine ⟨Poly.ofPi fun i => a (Fin.cast h.symm i), Poly.ofPi fun i => b (Fin.cast h.symm i),
    ?_, ?_⟩
  · rw [hb.ifftRound_eq, hb.fftInt_eq, hza, hzb]
    apply binary64IfftRound_eq p h2 h9 h _ _ _ _ _ _ hdev
    · intro j
      rw [ofCoeffs_latticePoint]
      exact coord_products_sub p hn h2 h9 h a b Z ha hb' _ _ (fun i => (hkey i).2.1)
        (fun i => (hkey i).2.2.2) j
    · intro j
      rw [ofCoeffs_latticePoint]
      exact norm_coord_products_le p h a b Z ha hb' _ _ (fun i => (hkey i).2.1)
        (fun i => (hkey i).2.2.2) j
  · rw [hb.ifftRound_eq, hb.fftInt_eq, hza, hzb]
    apply binary64IfftRound_eq p h2 h9 h _ _ _ _ _ _ hdev
    · intro j
      have hneg : (RealFFTPoly.ofCoeffs p.fftDepth fun i => ((-(intPolyMul
          (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.f + intPolyMul
          (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capF)).get (Fin.cast h i) : ℝ)) =
          -(RealFFTPoly.ofCoeffs p.fftDepth fun i => ((intPolyMul
          (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.f + intPolyMul
          (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capF).get (Fin.cast h i) : ℝ)) := by
        rw [← RealFFTPoly.ofCoeffs_neg]; congr 1; funext i; rw [Poly.get_neg]; push_cast; rfl
      rw [hneg, ofCoeffs_latticePoint, RealFFTPoly.coord_neg, RealFFTPoly.coord_neg,
        show ∀ x y : ℂ, -x - -y = -(x - y) from fun x y => by ring, norm_neg]
      exact coord_products_sub p hn h2 h9 h a b Z ha hb' _ _ (fun i => (hkey i).1)
        (fun i => (hkey i).2.2.1) j
    · intro j
      have hneg : (RealFFTPoly.ofCoeffs p.fftDepth fun i => ((-(intPolyMul
          (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.f + intPolyMul
          (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capF)).get (Fin.cast h i) : ℝ)) =
          -(RealFFTPoly.ofCoeffs p.fftDepth fun i => ((intPolyMul
          (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.f + intPolyMul
          (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capF).get (Fin.cast h i) : ℝ)) := by
        rw [← RealFFTPoly.ofCoeffs_neg]; congr 1; funext i; rw [Poly.get_neg]; push_cast; rfl
      rw [hneg, ofCoeffs_latticePoint, RealFFTPoly.coord_neg, norm_neg]
      exact norm_coord_products_le p h a b Z ha hb' _ _ (fun i => (hkey i).1)
        (fun i => (hkey i).2.2.1) j

/-! ## The coset condition and verification correctness -/

/-- **The coset condition at the binary64 FFT fields**, for keys with coefficients in
`[-127, 127]` (`KeyCoeffsLe127`) and sampled coefficients bounded by `Z` (`SampledCoeffsLe`),
from the key relations `f · h = g` and `F · h = G`, whenever `cosetDeviation (logn - 1) Z < 1/2`.
-/
theorem hpreimage_of_binary64FFTFields_of_sampledCoeffsLe (p : Params) (hn : p.n = 2 ^ p.logn)
    (h2 : 2 ≤ p.logn) (h9 : p.logn ≤ 9) (prims : Primitives p) (hb : Binary64FFTFields prims)
    (pk : PublicKey p) (sk : SecretKey p)
    (hkey : negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)
    (hcap : negacyclicMul (IntPoly.toRq sk.capF) pk.h = IntPoly.toRq sk.capG)
    (hcoeffs : KeyCoeffsLe127 sk) (Z : ℝ) (hdev : cosetDeviation p.fftDepth Z < 1 / 2)
    (hz : SampledCoeffsLe p prims sk Z) :
    ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      x ∈ support ((falconPSF p prims).trapdoorSample pk sk c) →
        (falconPSF p prims).eval pk x = c :=
  hpreimage_of_landsOnLattice p prims (by rw [hn]; positivity) pk sk hkey hcap
    fun c z hzc => landsOnLattice_of_binary64FFTFields p hn h2 h9 prims hb sk hcoeffs Z hdev z
      (hz c z hzc)

/-- **Verification correctness at the binary64 FFT fields**, for keys with coefficients in
`[-127, 127]` (`KeyCoeffsLe127`) and sampled coefficients bounded by `Z` (`SampledCoeffsLe`),
from a codec round trip and the key relations `f · h = g` and `F · h = G`, whenever
`cosetDeviation (logn - 1) Z < 1/2`. A valid key pair with `f` invertible modulo `q` satisfies
both relations (`validKeyPair_eq_true_iff`, `capRelation_of_validKeyPair`). -/
theorem verify_sign_correct_of_binary64FFTFields_of_sampledCoeffsLe (p : Params)
    (hn : p.n = 2 ^ p.logn) (h2 : 2 ≤ p.logn) (h9 : p.logn ≤ 9) (prims : Primitives p)
    (hb : Binary64FFTFields prims)
    (hcompress : ∀ (s : IntPoly p.n) (slen : ℕ) (bytes : List Byte),
      prims.compress s slen = some bytes → prims.decompress bytes slen = some s)
    (pk : PublicKey p) (sk : SecretKey p)
    (hkey : negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)
    (hcap : negacyclicMul (IntPoly.toRq sk.capF) pk.h = IntPoly.toRq sk.capG)
    (hcoeffs : KeyCoeffsLe127 sk) (Z : ℝ) (hdev : cosetDeviation p.fftDepth Z < 1 / 2)
    (hz : SampledCoeffsLe p prims sk Z) (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign p prims pk sk msg maxAttempts)) :
    verify p prims pk msg sig = true :=
  verify_sign_correct p prims pk sk msg maxAttempts sig hcompress
    (hpreimage_of_binary64FFTFields_of_sampledCoeffsLe p hn h2 h9 prims hb pk sk hkey hcap hcoeffs
      Z hdev hz) hsig

/-! ## Falcon-512 -/

/-- At Falcon-512 the deviation bound is below `1/2` for sampled coefficients up to `2^16`. It
stays below `1/2` up to `Z = 80712`; `2^16` is the power of two above `512 · 127 = 65024`, which
bounds every coefficient of the target polynomials `-c · F / q` and `c · f / q` for keys with
coefficients in `[-127, 127]`. -/
theorem cosetDeviation_falcon512 : cosetDeviation 8 (2 ^ 16) < 1 / 2 := by
  norm_num [cosetDeviation, ifftDeviation, fftError, etaF, etaI, u]

/-- **Verification correctness at the binary64 FFT fields for Falcon-512**, for keys with
coefficients in `[-127, 127]` (`KeyCoeffsLe127`) and sampled coefficients bounded by `2^16`
(`SampledCoeffsLe`), from a codec round trip and the key relations `f · h = g` and `F · h = G`. -/
theorem verify_sign_correct_falcon512_of_binary64FFTFields_of_sampledCoeffsLe
    (prims : Primitives falcon512) (hb : Binary64FFTFields prims)
    (hcompress : ∀ (s : IntPoly falcon512.n) (slen : ℕ) (bytes : List Byte),
      prims.compress s slen = some bytes → prims.decompress bytes slen = some s)
    (pk : PublicKey falcon512) (sk : SecretKey falcon512)
    (hkey : negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)
    (hcap : negacyclicMul (IntPoly.toRq sk.capF) pk.h = IntPoly.toRq sk.capG)
    (hcoeffs : KeyCoeffsLe127 sk) (hz : SampledCoeffsLe falcon512 prims sk (2 ^ 16))
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign falcon512 prims pk sk msg maxAttempts)) :
    verify falcon512 prims pk msg sig = true :=
  verify_sign_correct_of_binary64FFTFields_of_sampledCoeffsLe falcon512 rfl (by decide)
    (by decide) prims hb hcompress pk sk hkey hcap hcoeffs (2 ^ 16) cosetDeviation_falcon512 hz
    msg maxAttempts sig hsig

end Falcon.Concrete

end
