/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all Extern.Falcon.Instance
import all Extern.Falcon.Binary64Coset
import all LatticeCrypto.Falcon.PackedFFT
import all LatticeCrypto.Falcon.Coset
public import Extern.Falcon.Binary64Coset
public import LatticeCrypto.Falcon.FixedPoint.FFT

/-!
# The coset condition at the fixed-point FFT primitives

`fx64FFTPrimitives A` is `Falcon.Concrete.concretePrimitives` with its three FFT conversion
fields computed in fixed point with 64 fractional bits by the arithmetic `A`
(`Falcon.FixedPoint.Arith64`): `fftInt` and `fftTarget` by the forward butterfly stages,
`ifftRound` by the inverse stages followed by rounding to the nearest integer. The arithmetic is
a model, a structure of rounding functions with error bounds, not executable code;
`Falcon.FixedPoint.Arith64.nearest` is one instance.

The rest of `Primitives` stays exact, as at the binary64 fields: `toFFTTarget`'s products and
`1/q`, `ffSampling`, and the products and sums of `fromFFTPreimage`. So this is not a fixed-point
signer.

`landsOnLattice_of_fx64FFTFields` proves `Falcon.LandsOnLattice` for any bundle with these
`fftInt` and `ifftRound` fields (`Fx64FFTFields`), for every sampler output that is the packed
FFT of an integer pair with coefficients bounded by `Z`, for keys with coefficients in
`[-127, 127]` (`KeyCoeffsLe127`) and every `logn ≥ 1`, whenever the explicit deviation bound
`fx64CosetDeviation (logn - 1) Z` is below `1/2`. `fx64CosetDeviation_falcon512` evaluates it
below `1/2` at Falcon-512 for `Z = 2^33`, and `fx64CosetDeviation_falcon512_max` up to
`Z = 16267515731`.

As at the binary64 fields, the bound on sampled coefficients is the hypothesis
`Falcon.SampledCoeffsLe`.

Register overflow is not represented: `Arith64` places no bound on the magnitude of a value. The
results are about that model; they do not show that an implementation with 64 integer bits keeps
every value below `2^63`, which it must for the model to describe it.
-/

public section

open OracleComp OracleSpec LatticeCrypto Complex

namespace Falcon.Concrete

open Falcon Falcon.FixedPoint

/-! ## The fixed-point FFT fields -/

/-- `concretePrimitives` with its three FFT fields computed in fixed point by `A`; the sampler,
the products and `ffSampling` are those of `concretePrimitives` and `Primitives`. -/
@[expose] noncomputable def fx64FFTPrimitives (A : Arith64) (p : Params)
    (hn : p.n = 2 ^ p.logn) : Primitives p :=
  { concretePrimitives p hn with
    fftTarget := A.fftTarget p
    fftInt := A.fftInt p
    ifftRound := A.ifftRound p }

/-- A primitive bundle whose `fftInt` and `ifftRound` are the fixed-point ones of `A`. -/
structure Fx64FFTFields (A : Arith64) {p : Params} (prims : Primitives p) : Prop where
  fftInt_eq : prims.fftInt = A.fftInt p
  ifftRound_eq : prims.ifftRound = A.ifftRound p

/-- `fx64FFTPrimitives A` has the fixed-point FFT fields of `A`. -/
theorem fx64FFTPrimitives_fx64FFTFields (A : Arith64) (p : Params) (hn : p.n = 2 ^ p.logn) :
    Fx64FFTFields A (fx64FFTPrimitives A p hn) :=
  ⟨rfl, rfl⟩

/-- The codec of `fx64FFTPrimitives` is that of `concretePrimitives` and round-trips. -/
theorem fx64FFTPrimitives_decompress_compress (A : Arith64) (p : Params)
    (hn : p.n = 2 ^ p.logn) (s : IntPoly p.n) (slen : ℕ) (bytes : List Byte)
    (h : (fx64FFTPrimitives A p hn).compress s slen = some bytes) :
    (fx64FFTPrimitives A p hn).decompress bytes slen = some s :=
  decompress_compress p.n s slen bytes h

/-! ## The lattice point -/

/-- The deviation bound of the coset condition at the fixed-point primitives: sampler outputs
with coefficients bounded by `Z`, keys with coefficients bounded by `127`. -/
@[expose] noncomputable def fx64CosetDeviation (k : ℕ) (Z : ℝ) : ℝ :=
  FixedPoint.ifftDeviation k (2 * (2 ^ (k + 1) * Z) * FixedPoint.fftError k)
    (2 * (2 ^ (k + 1) * Z) * (2 ^ (k + 1) * 127))

/-- The fixed-point sum of products is within `2 · 2^(k+1) Z · fftError k` of the exact one, slot
by slot. -/
private theorem coord_products_sub_fx64 (A : Arith64) (p : Params)
    (h : 2 * 2 ^ p.fftDepth = p.n) (a b : Fin (2 * 2 ^ p.fftDepth) → ℤ) (Z : ℝ)
    (ha : ∀ i, |(a i : ℝ)| ≤ Z) (hb : ∀ i, |(b i : ℝ)| ≤ Z) (u₁ u₂ : IntPoly p.n)
    (hu₁ : ∀ i, |u₁.get i| ≤ 127) (hu₂ : ∀ i, |u₂.get i| ≤ 127) (j : Fin (2 ^ p.fftDepth)) :
    ‖RealFFTPoly.coord (Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
          (A.fftInt p u₁) +
        Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
          (A.fftInt p u₂)) j -
      RealFFTPoly.coord (Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₁.get (Fin.cast h i) : ℝ)) +
        Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₂.get (Fin.cast h i) : ℝ))) j‖ ≤
      2 * (2 ^ (p.fftDepth + 1) * Z) * FixedPoint.fftError p.fftDepth := by
  simp only [RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT]
  have hA := RealFFTPoly.norm_coord_ofCoeffs_le p.fftDepth _ Z ha j
  have hB := RealFFTPoly.norm_coord_ofCoeffs_le p.fftDepth _ Z hb j
  have e1 := A.coord_fftInt_sub p h u₁ hu₁ j
  have e2 := A.coord_fftInt_sub p h u₂ hu₂ j
  set α := RealFFTPoly.coord (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ)) j
  set β := RealFFTPoly.coord (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ)) j
  calc _ = ‖α * (RealFFTPoly.coord (A.fftInt p u₁) j - RealFFTPoly.coord
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₁.get (Fin.cast h i) : ℝ)) j) +
        β * (RealFFTPoly.coord (A.fftInt p u₂) j - RealFFTPoly.coord
          (RealFFTPoly.ofCoeffs p.fftDepth fun i => (u₂.get (Fin.cast h i) : ℝ)) j)‖ := by
        congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ (2 ^ (p.fftDepth + 1) * Z) * FixedPoint.fftError p.fftDepth +
        (2 ^ (p.fftDepth + 1) * Z) * FixedPoint.fftError p.fftDepth := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hA e1 (norm_nonneg _) ((norm_nonneg _).trans hA))
          (mul_le_mul hB e2 (norm_nonneg _) ((norm_nonneg _).trans hB))
    _ = _ := by ring

/-- The fixed-point basis application on the packed FFT of an integer pair `(a, b)` with
coefficients bounded by `Z` rounds to the lattice point `(a, b) · B`. -/
private theorem ifftRound_basis_fx64 (A : Arith64) (p : Params) (h : 2 * 2 ^ p.fftDepth = p.n)
    (prims : Primitives p) (hb : Fx64FFTFields A prims) (sk : SecretKey p)
    (hkey : KeyCoeffsLe127 sk) (Z : ℝ) (hdev : fx64CosetDeviation p.fftDepth Z < 1 / 2)
    (a b : Fin (2 * 2 ^ p.fftDepth) → ℤ) (ha : ∀ i, |(a i : ℝ)| ≤ Z)
    (hb' : ∀ i, |(b i : ℝ)| ≤ Z) :
    prims.ifftRound (Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
        (prims.fftInt sk.g) +
      Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
        (prims.fftInt sk.capG)) =
      intPolyMul (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.g +
        intPolyMul (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capG ∧
    prims.ifftRound (-(Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (a i : ℝ))
        (prims.fftInt sk.f) +
      Primitives.mulFFT (RealFFTPoly.ofCoeffs p.fftDepth fun i => (b i : ℝ))
        (prims.fftInt sk.capF))) =
      -(intPolyMul (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.f +
        intPolyMul (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capF) := by
  constructor
  · rw [hb.ifftRound_eq, hb.fftInt_eq]
    apply A.ifftRound_eq p h _ _ _ _ _ _ hdev
    · intro j
      rw [ofCoeffs_latticePoint]
      exact coord_products_sub_fx64 A p h a b Z ha hb' _ _ (fun i => (hkey i).2.1)
        (fun i => (hkey i).2.2.2) j
    · intro j
      rw [ofCoeffs_latticePoint]
      exact norm_coord_products_le p h a b Z ha hb' _ _ (fun i => (hkey i).2.1)
        (fun i => (hkey i).2.2.2) j
  · have hneg : (RealFFTPoly.ofCoeffs p.fftDepth fun i => ((-(intPolyMul
        (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.f + intPolyMul
        (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capF)).get (Fin.cast h i) : ℝ)) =
        -(RealFFTPoly.ofCoeffs p.fftDepth fun i => ((intPolyMul
        (Poly.ofPi fun i => a (Fin.cast h.symm i)) sk.f + intPolyMul
        (Poly.ofPi fun i => b (Fin.cast h.symm i)) sk.capF).get (Fin.cast h i) : ℝ)) := by
      rw [← RealFFTPoly.ofCoeffs_neg]; congr 1; funext i; rw [Poly.get_neg]; push_cast; rfl
    rw [hb.ifftRound_eq, hb.fftInt_eq]
    apply A.ifftRound_eq p h _ _ _ _ _ _ hdev
    · intro j
      rw [hneg, ofCoeffs_latticePoint, RealFFTPoly.coord_neg, RealFFTPoly.coord_neg,
        show ∀ x y : ℂ, -x - -y = -(x - y) from fun x y => by ring, norm_neg]
      exact coord_products_sub_fx64 A p h a b Z ha hb' _ _ (fun i => (hkey i).1)
        (fun i => (hkey i).2.2.1) j
    · intro j
      rw [hneg, ofCoeffs_latticePoint, RealFFTPoly.coord_neg, norm_neg]
      exact norm_coord_products_le p h a b Z ha hb' _ _ (fun i => (hkey i).1)
        (fun i => (hkey i).2.2.1) j

/-- **The lattice-point condition at the fixed-point FFT fields**, for keys with coefficients in
`[-127, 127]` (`KeyCoeffsLe127`). For `logn ≥ 1` and a sampler output `z` that is the packed FFT
of an integer pair with coefficients bounded by `Z`, the fixed-point basis application lands on
the lattice whenever `fx64CosetDeviation (logn - 1) Z` is below `1/2`. -/
theorem landsOnLattice_of_fx64FFTFields (A : Arith64) (p : Params) (hn : p.n = 2 ^ p.logn)
    (h1 : 1 ≤ p.logn) (prims : Primitives p) (hb : Fx64FFTFields A prims) (sk : SecretKey p)
    (hkey : KeyCoeffsLe127 sk) (Z : ℝ) (hdev : fx64CosetDeviation p.fftDepth Z < 1 / 2)
    (z : FFTPair p.fftDepth)
    (hz : ∃ a b : Fin (2 * 2 ^ p.fftDepth) → ℤ, (∀ i, |(a i : ℝ)| ≤ Z) ∧ (∀ i, |(b i : ℝ)| ≤ Z) ∧
      z.1 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (a i : ℝ)) ∧
      z.2 = RealFFTPoly.ofCoeffs p.fftDepth (fun i => (b i : ℝ))) :
    LandsOnLattice p prims sk z := by
  obtain ⟨a, b, ha, hb', hza, hzb⟩ := hz
  have h : 2 * 2 ^ p.fftDepth = p.n := by
    rw [hn, Params.fftDepth, ← pow_succ']; congr 1; omega
  obtain ⟨h0, h1'⟩ := ifftRound_basis_fx64 A p h prims hb sk hkey Z hdev a b ha hb'
  unfold LandsOnLattice
  refine ⟨Poly.ofPi fun i => a (Fin.cast h.symm i), Poly.ofPi fun i => b (Fin.cast h.symm i),
    ?_, ?_⟩
  · rw [hza, hzb]; exact h0
  · rw [hza, hzb]; exact h1'

/-! ## The coset condition and verification correctness -/

/-- **The coset condition at the fixed-point FFT fields**, for keys with coefficients in
`[-127, 127]` (`KeyCoeffsLe127`) and sampled coefficients bounded by `Z` (`SampledCoeffsLe`), from
the key relations `f · h = g` and `F · h = G`, whenever `fx64CosetDeviation (logn - 1) Z < 1/2`. -/
theorem hpreimage_of_fx64FFTFields_of_sampledCoeffsLe (A : Arith64) (p : Params)
    (hn : p.n = 2 ^ p.logn) (h1 : 1 ≤ p.logn) (prims : Primitives p) (hb : Fx64FFTFields A prims)
    (pk : PublicKey p) (sk : SecretKey p)
    (hkey : negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)
    (hcap : negacyclicMul (IntPoly.toRq sk.capF) pk.h = IntPoly.toRq sk.capG)
    (hcoeffs : KeyCoeffsLe127 sk) (Z : ℝ) (hdev : fx64CosetDeviation p.fftDepth Z < 1 / 2)
    (hz : SampledCoeffsLe p prims sk Z) :
    ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      x ∈ support ((falconPSF p prims).trapdoorSample pk sk c) →
        (falconPSF p prims).eval pk x = c :=
  hpreimage_of_landsOnLattice p prims (by rw [hn]; positivity) pk sk hkey hcap
    fun c z hzc => landsOnLattice_of_fx64FFTFields A p hn h1 prims hb sk hcoeffs Z hdev z
      (hz c z hzc)

/-- **Verification correctness at the fixed-point FFT fields**, for keys with coefficients in
`[-127, 127]` (`KeyCoeffsLe127`) and sampled coefficients bounded by `Z` (`SampledCoeffsLe`), from
a codec round trip and the key relations `f · h = g` and `F · h = G`, whenever
`fx64CosetDeviation (logn - 1) Z < 1/2`. -/
theorem verify_sign_correct_of_fx64FFTFields_of_sampledCoeffsLe (A : Arith64) (p : Params)
    (hn : p.n = 2 ^ p.logn) (h1 : 1 ≤ p.logn) (prims : Primitives p) (hb : Fx64FFTFields A prims)
    (hcompress : ∀ (s : IntPoly p.n) (slen : ℕ) (bytes : List Byte),
      prims.compress s slen = some bytes → prims.decompress bytes slen = some s)
    (pk : PublicKey p) (sk : SecretKey p)
    (hkey : negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)
    (hcap : negacyclicMul (IntPoly.toRq sk.capF) pk.h = IntPoly.toRq sk.capG)
    (hcoeffs : KeyCoeffsLe127 sk) (Z : ℝ) (hdev : fx64CosetDeviation p.fftDepth Z < 1 / 2)
    (hz : SampledCoeffsLe p prims sk Z) (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign p prims pk sk msg maxAttempts)) :
    verify p prims pk msg sig = true :=
  verify_sign_correct p prims pk sk msg maxAttempts sig hcompress
    (hpreimage_of_fx64FFTFields_of_sampledCoeffsLe A p hn h1 prims hb pk sk hkey hcap hcoeffs Z
      hdev hz) hsig

/-! ## Falcon-512 -/

/-- At Falcon-512 the deviation bound is below `1/2` for sampled coefficients up to `2^33`. -/
theorem fx64CosetDeviation_falcon512 : fx64CosetDeviation 8 (2 ^ 33) < 1 / 2 := by
  norm_num [fx64CosetDeviation, FixedPoint.ifftDeviation, FixedPoint.fftError,
    FixedPoint.etaFwd, FixedPoint.etaInv]

/-- At Falcon-512 the deviation bound stays below `1/2` up to `Z = 16267515731` (about
`2^33.92`), the largest integer for which it does. -/
theorem fx64CosetDeviation_falcon512_max : fx64CosetDeviation 8 16267515731 < 1 / 2 := by
  norm_num [fx64CosetDeviation, FixedPoint.ifftDeviation, FixedPoint.fftError,
    FixedPoint.etaFwd, FixedPoint.etaInv]

/-- **Verification correctness at the fixed-point FFT fields for Falcon-512**, for keys with
coefficients in `[-127, 127]` (`KeyCoeffsLe127`) and sampled coefficients bounded by `2^33`
(`SampledCoeffsLe`), from a codec round trip and the key relations `f · h = g` and `F · h = G`. -/
theorem verify_sign_correct_falcon512_of_fx64FFTFields_of_sampledCoeffsLe (A : Arith64)
    (prims : Primitives falcon512) (hb : Fx64FFTFields A prims)
    (hcompress : ∀ (s : IntPoly falcon512.n) (slen : ℕ) (bytes : List Byte),
      prims.compress s slen = some bytes → prims.decompress bytes slen = some s)
    (pk : PublicKey falcon512) (sk : SecretKey falcon512)
    (hkey : negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)
    (hcap : negacyclicMul (IntPoly.toRq sk.capF) pk.h = IntPoly.toRq sk.capG)
    (hcoeffs : KeyCoeffsLe127 sk) (hz : SampledCoeffsLe falcon512 prims sk (2 ^ 33))
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (hsig : some sig ∈ support (sign falcon512 prims pk sk msg maxAttempts)) :
    verify falcon512 prims pk msg sig = true :=
  verify_sign_correct_of_fx64FFTFields_of_sampledCoeffsLe A falcon512 rfl (by decide) prims hb
    hcompress pk sk hkey hcap hcoeffs (2 ^ 33) fx64CosetDeviation_falcon512 hz msg maxAttempts
    sig hsig

end Falcon.Concrete

end
