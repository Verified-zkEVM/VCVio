/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import all Init.Data.Array.Basic
import all Init.Data.Vector.Algebra
import all LatticeCrypto.MLDSA.Arithmetic
import Mathlib.Tactic.ReduceModChar
public meta import LatticeCrypto.MLDSA.Arithmetic
public meta import Mathlib.Data.Fintype.Defs
public meta import Mathlib.Data.ZMod.Defs
public import LatticeCrypto.MLDSA.Arithmetic
public import LatticeCrypto.Ring.NTTCert
public import LatticeCrypto.Ring.NTTLoop
public import LatticeCrypto.Ring.NTTSplitCert
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Concrete NTT for ML-DSA

Pure-Lean executable kernels for FIPS 204 Algorithms 41, 42, and 45, specialized to
`q = 8380417`, `n = 256`, and `ζ = 1753`.

The proof-oriented `ntt` / `invNTT` interface composes eight blocked butterfly stages.
Complementary bit-reversed twiddles make the inverse stages cancel the forward stages up to
`2^8`, and `nInv` removes that factor. Coordinate `i` of `ntt f` is the evaluation of `f` at
`ζ^(2·brv(i) + 1)` (`ntt_coeff_eq_eval`). So `ntt` maps negacyclic multiplication to the pointwise
product `multiplyNTTs` of FIPS 204 Algorithm 45 (`ntt_negacyclicMul`).

`ntt` and `invNTT` are the in-place loop kernels `loopNTT` and `loopInvNTT` themselves. Their
loops are proved equal to the blocked stages by the shared loop lemmas of
`LatticeCrypto.Ring.NTTLoop`, so the code that runs is the code the laws are proved about.
-/

public section



namespace MLDSA.Concrete

open MLDSA


/-- Reverse the low 8 bits of `i` (FIPS 204: `brv(k)`). -/
def bitRev8 (i : Nat) : Nat :=
  let b := fun k => (i >>> k) &&& 1
  (b 0 <<< 7) ||| (b 1 <<< 6) ||| (b 2 <<< 5) ||| (b 3 <<< 4) |||
  (b 4 <<< 3) ||| (b 5 <<< 2) ||| (b 6 <<< 1) ||| b 7

/-- Precomputed twiddle table: `zetas[k] = ζ^(brv(k))` for `k = 0 .. 255`,
where `brv` is 8-bit reversal per FIPS 204 §4.5.
The forward NTT uses indices `1 .. 255`; the inverse NTT uses the same indices
(negated) in reverse order `255 .. 1`. -/
def zetaTable : Array Coeff :=
  (Array.range 256).map fun i => zeta ^ bitRev8 i

/-- `256⁻¹ mod q`. -/
def nInv : Coeff := ((modulus - (modulus - 1) / ringDegree : ℕ) : Coeff)

/-- Safe array access with fallback to zero. -/
private def getZ (a : Array Coeff) (i : Nat) : Coeff := a.getD i 0

private theorem bitRev8_layer_partner :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      bitRev8 (2 ^ s.val + g.val) +
          bitRev8 (2 ^ (s.val + 1) - 1 - g.val) = 256 := by
  decide

private theorem layer_twiddle_index_bounds :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      2 ^ s.val + g.val < 256 ∧
        2 ^ (s.val + 1) - 1 - g.val < 256 := by
  decide

private theorem getZ_zetaTable (i : Nat) (hi : i < 256) :
    getZ zetaTable i = zeta ^ bitRev8 i := by
  simp [getZ, zetaTable, hi]

private theorem zeta_pow_256 : (zeta : Coeff) ^ 256 = -1 := by
  change (1753 : ZMod 8380417) ^ 256 = -1
  reduce_mod_char

/-- `ζ = 1753` is a primitive `512`-th root of unity in `ℤ_q` (FIPS 204 §7.5): the twiddle half
of the NTT correctness argument. -/
theorem zeta_isPrimitiveRoot : IsPrimitiveRoot (zeta : Coeff) 512 := by
  change IsPrimitiveRoot (1753 : ZMod 8380417) 512
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by reduce_mod_char) ?_
  intro p hp hdvd
  obtain rfl : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 9 by simpa using hdvd))
  reduce_mod_char
  decide

/-- Forward and complementary inverse-table twiddles in one layer multiply to `-1`. -/
private theorem zetaTable_layer_partner :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      getZ zetaTable (2 ^ s.val + g.val) *
          getZ zetaTable (2 ^ (s.val + 1) - 1 - g.val) = -1 := by
  intro s g
  obtain ⟨hforward, hinverse⟩ := layer_twiddle_index_bounds s g
  rw [getZ_zetaTable _ hforward, getZ_zetaTable _ hinverse, ← pow_add]
  rw [bitRev8_layer_partner s g, zeta_pow_256]

/-- FIPS 204 Algorithm 41: executable loop kernel for the forward NTT. -/
def loopNTT (f : Rq) : Tq := Id.run do
  let mut a := f.toArray
  let mut k := 1
  let mut len := 128
  while len ≥ 1 do
    let mut start := 0
    while start < ringDegree do
      let z := getZ zetaTable k
      k := k + 1
      for j in [start : start + len] do
        let u := getZ a j
        let v := getZ a (j + len)
        let t := z * v
        a := a.set! (j + len) (u - t)
        a := a.set! j (u + t)
      start := start + 2 * len
    len := len / 2
  return ⟨Vector.ofFn fun i => getZ a i.val⟩

/-- FIPS 204 Algorithm 42: executable loop kernel for the inverse NTT. -/
def loopInvNTT (fHat : Tq) : Rq := Id.run do
  let mut a := fHat.toArray
  let mut k := 255
  let mut len := 1
  while len ≤ 128 do
    let mut start := 0
    while start < ringDegree do
      let z := -(getZ zetaTable k)
      k := k - 1
      for j in [start : start + len] do
        let u := getZ a j
        let v := getZ a (j + len)
        a := a.set! j (u + v)
        a := a.set! (j + len) (z * (u - v))
      start := start + 2 * len
    len := len * 2
  for j in [0 : ringDegree] do
    a := a.set! j (nInv * getZ a j)
  return Vector.ofFn fun i => getZ a i.val

private abbrev NTTCoord := Fin polyBackend.degree

private theorem degree_eq : 2 ^ 8 = polyBackend.degree := rfl

/-- The inverse twiddle of group `g` in layer `s` times the forward twiddle is `1`. -/
private theorem zetaTable_twiddle_partner (s : Fin 8) (g : Fin (2 ^ s.val)) :
    -getZ zetaTable (2 ^ (s.val + 1) - 1 - g.val) * getZ zetaTable (2 ^ s.val + g.val) = 1 := by
  rw [neg_mul, mul_comm, zetaTable_layer_partner s g, neg_neg]

private def nttStage (s : Fin 8) : LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord :=
  LatticeCrypto.NTTCert.ctStage degree_eq (getZ zetaTable) zetaTable_twiddle_partner s

private def nttStages :
    List (LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord) :=
  [nttStage 0, nttStage 1, nttStage 2, nttStage 3,
    nttStage 4, nttStage 5, nttStage 6, nttStage 7]

/-! ## Evaluation points -/

/-- The `i`-th ML-DSA NTT evaluation point `ζ^(2·brv(i) + 1)` (FIPS 204 §7.5). -/
def nttPoint (i : Fin ringDegree) : Coeff := zeta ^ (2 * bitRev8 i.val + 1)

/-- Unfolding lemma for `nttPoint`. -/
theorem nttPoint_eq (i : Fin ringDegree) : nttPoint i = zeta ^ (2 * bitRev8 i.val + 1) := by
  unfold nttPoint; rfl

/-- The residue point of block `g` after `t` layers: block `g` of size `2^(8-t)` is congruent to
the input modulo `X^(2^(8-t)) − ctPoint t g`. -/
private def ctPoint (t g : ℕ) : Coeff := zeta ^ (2 * bitRev8 g + 2 ^ (8 - t))

private theorem bitRev8_ct_sq : ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
    2 * bitRev8 (2 ^ s.val + g.val) = 2 * bitRev8 g.val + 2 ^ (8 - s.val) := by
  decide

private theorem bitRev8_ct_left : ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
    2 * bitRev8 (2 * g.val) + 2 ^ (7 - s.val) = bitRev8 (2 ^ s.val + g.val) := by
  decide

private theorem bitRev8_ct_right : ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
    2 * bitRev8 (2 * g.val + 1) + 2 ^ (7 - s.val) = bitRev8 (2 ^ s.val + g.val) + 256 := by
  decide

private theorem ctPoint_sq (s : Fin 8) (g : Fin (2 ^ s.val)) :
    (getZ zetaTable (2 ^ s.val + g.val)) ^ 2 = ctPoint s.val g.val := by
  rw [getZ_zetaTable _ (layer_twiddle_index_bounds s g).1, ← pow_mul, ctPoint, Nat.mul_comm,
    bitRev8_ct_sq s g]

private theorem ctPoint_left (s : Fin 8) (g : Fin (2 ^ s.val)) :
    ctPoint (s.val + 1) (2 * g.val) = getZ zetaTable (2 ^ s.val + g.val) := by
  rw [getZ_zetaTable _ (layer_twiddle_index_bounds s g).1, ctPoint,
    show 8 - (s.val + 1) = 7 - s.val by omega, bitRev8_ct_left s g]

private theorem ctPoint_right (s : Fin 8) (g : Fin (2 ^ s.val)) :
    ctPoint (s.val + 1) (2 * g.val + 1) = -getZ zetaTable (2 ^ s.val + g.val) := by
  rw [getZ_zetaTable _ (layer_twiddle_index_bounds s g).1, ctPoint,
    show 8 - (s.val + 1) = 7 - s.val by omega, bitRev8_ct_right s g, pow_add, zeta_pow_256,
    mul_neg_one]

private theorem ctPoint_last (i : Fin ringDegree) : ctPoint 8 i.val = nttPoint i := by
  rfl

/-- Every evaluation point is a root of `X^256 + 1`. -/
theorem nttPoint_pow_ringDegree (i : Fin ringDegree) : nttPoint i ^ ringDegree = -1 := by
  rw [nttPoint_eq, ← pow_mul, mul_comm, pow_mul, show zeta ^ ringDegree = -1 from zeta_pow_256]
  exact Odd.neg_one_pow ⟨bitRev8 i.val, rfl⟩

private theorem nttStages_eq_ofFn : nttStages = List.ofFn nttStage := by
  simp [nttStages, List.ofFn_succ]

private theorem nInv_stageScalar :
    nInv * LatticeCrypto.NTTCert.stageScalar nttStages = 1 := by
  change ((8347681 * 256 : Nat) : ZMod 8380417) = ((1 : Nat) : ZMod 8380417)
  rw [ZMod.natCast_eq_natCast_iff']

private def nttCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.forwardStages nttStages input

private def invNTTCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.scaleCoeffs nInv
    (LatticeCrypto.NTTCert.inverseStages nttStages input)

private theorem invNTTCoeffs_nttCoeffs (input : NTTCoord → Coeff) :
    invNTTCoeffs (nttCoeffs input) = input := by
  unfold invNTTCoeffs nttCoeffs
  exact LatticeCrypto.NTTCert.scale_inverseStages_forwardStages
    nttStages nInv nInv_stageScalar input

private theorem nttCoeffs_add (left right : NTTCoord → Coeff) :
    nttCoeffs (left + right) = nttCoeffs left + nttCoeffs right := by
  unfold nttCoeffs
  exact LatticeCrypto.NTTCert.forwardStages_add nttStages left right

private theorem nttCoeffs_sub (left right : NTTCoord → Coeff) :
    nttCoeffs (left - right) = nttCoeffs left - nttCoeffs right := by
  unfold nttCoeffs
  exact LatticeCrypto.NTTCert.forwardStages_sub nttStages left right

private theorem nttCoeffs_zero : nttCoeffs 0 = 0 := by
  unfold nttCoeffs
  exact LatticeCrypto.NTTCert.forwardStages_zero nttStages

/-- The forward NTT, computed by the loop kernel `loopNTT`. -/
def ntt (f : Rq) : Tq := loopNTT f

/-- The inverse NTT, computed by the loop kernel `loopInvNTT`. -/
def invNTT (fHat : Tq) : Rq := loopInvNTT fHat

private theorem loopNTT_loops (f : Rq) :
    loopNTT f = ⟨Vector.ofFn fun i =>
      (Id.run (forIn Lean.Loop.mk (f.toArray, 1, polyBackend.degree / 2)
        (LatticeCrypto.NTTCert.ctForwardBody polyBackend.degree (getZ zetaTable)))).1.getD i 0⟩ :=
  rfl

private theorem loopInvNTT_loops (fHat : Tq) :
    loopInvNTT fHat = Vector.ofFn fun i => (Id.run (forIn [0 : polyBackend.degree]
      (Id.run (forIn Lean.Loop.mk (fHat.coeffs.toArray, polyBackend.degree - 1, 1)
        (LatticeCrypto.NTTCert.ctInverseBody polyBackend.degree (getZ zetaTable)))).1
      fun j b => pure (.yield (b.set! j (nInv * b.getD j 0))))).getD i 0 :=
  rfl

/-- `ntt` is the eight blocked butterfly stages. -/
private theorem ntt_eq (f : Rq) :
    ntt f = ⟨LatticeCrypto.NTTCert.applyCoeffTransform polyBackend nttCoeffs f⟩ := by
  rw [ntt, loopNTT_loops, LatticeCrypto.NTTCert.ctForward_loop degree_eq _
    zetaTable_twiddle_partner (LatticeCrypto.NTTCert.vector_toArray_eq_ofFn f)]
  simp only [LatticeCrypto.NTTCert.getD_ofFn_eq_coeffAt, LatticeCrypto.NTTCert.coeffAt_fin]
  rfl

/-- `invNTT` is the eight inverse stages followed by scaling by `nInv`. -/
private theorem invNTT_eq (fHat : Tq) :
    invNTT fHat =
      LatticeCrypto.NTTCert.applyCoeffTransform polyBackend invNTTCoeffs fHat.coeffs := by
  rw [invNTT, loopInvNTT_loops, LatticeCrypto.NTTCert.ctInverse_loop degree_eq _
    zetaTable_twiddle_partner (LatticeCrypto.NTTCert.vector_toArray_eq_ofFn fHat.coeffs),
    LatticeCrypto.NTTCert.scale_loop]
  simp only [LatticeCrypto.NTTCert.getD_ofFn_eq_coeffAt, LatticeCrypto.NTTCert.coeffAt_fin]
  rfl

/-- FIPS 204 Algorithm 45 (`MultiplyNTT`): the pointwise product in `T_q`. -/
def multiplyNTTs (fHat gHat : Tq) : Tq :=
  ⟨Vector.ofFn fun i => fHat[i.val] * gHat[i.val]⟩

/-- Coordinate `i` of `multiplyNTTs fHat gHat` is the product of the coordinates `i`. -/
theorem coeff_multiplyNTTs (fHat gHat : Tq) (i : Fin ringDegree) :
    polyBackend.coeff (multiplyNTTs fHat gHat).coeffs i =
      polyBackend.coeff fHat.coeffs i * polyBackend.coeff gHat.coeffs i := by
  change (Vector.ofFn fun j : Fin ringDegree => fHat[j.val] * gHat[j.val]).get i = _
  rw [Vector.get_ofFn]
  rfl

/-- The concrete inverse transform is a left inverse to the concrete forward transform. -/
theorem invNTT_ntt (f : Rq) : invNTT (ntt f) = f := by
  rw [invNTT_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_comp
    nttCoeffs invNTTCoeffs invNTTCoeffs_nttCoeffs f

private def rqEquivCoeffFun : Rq ≃ (Fin ringDegree → Coeff) where
  toFun f i := f.get i
  invFun f := Vector.ofFn f
  left_inv f := by
    apply Vector.ext
    intro i hi
    exact Vector.getElem_ofFn (f := fun i => f.get i) hi
  right_inv f := by
    funext i
    exact Vector.get_ofFn f i

private def rqEquivTq : Rq ≃ Tq where
  toFun f := ⟨f⟩
  invFun fHat := fHat.coeffs
  left_inv _ := rfl
  right_inv fHat := by cases fHat; rfl

private theorem ntt_injective : Function.Injective ntt := by
  intro f g h
  have hInv := congrArg invNTT h
  simpa [invNTT_ntt] using hInv

private theorem ntt_surjective : Function.Surjective ntt := by
  let : NeZero modulus := ⟨by norm_num [modulus]⟩
  let : Fintype Coeff := by
    dsimp [Coeff]
    exact ZMod.fintype modulus
  let : Finite Rq := Finite.of_equiv (Fin ringDegree → Coeff) rqEquivCoeffFun.symm
  exact ntt_injective.surjective_of_finite rqEquivTq

/-- The concrete forward transform is a left inverse to the concrete inverse transform. -/
theorem ntt_invNTT (fHat : Tq) : ntt (invNTT fHat) = fHat := by
  obtain ⟨f, hf⟩ := ntt_surjective fHat
  calc
    ntt (invNTT fHat) = ntt (invNTT (ntt f)) := by rw [hf]
    _ = ntt f := by rw [invNTT_ntt]
    _ = fHat := hf

private theorem hadd_rq (f g : Rq) :
    polyBackend.coeff (f + g) = polyBackend.coeff f + polyBackend.coeff g := by
  funext i
  change ((LatticeCrypto.vectorNegacyclicRing Coeff ringDegree).add f g).get i = f.get i + g.get i
  simp

private theorem hsub_rq (f g : Rq) :
    polyBackend.coeff (f - g) = polyBackend.coeff f - polyBackend.coeff g := by
  funext i
  change ((LatticeCrypto.vectorNegacyclicRing Coeff ringDegree).sub f g).get i = f.get i - g.get i
  simp

private theorem hzero_rq : polyBackend.coeff (0 : Rq) = 0 := by
  funext i
  exact LatticeCrypto.vectorRing_zero_get i

/-- The concrete NTT is additive. -/
theorem ntt_add_toRq (f g : Rq) : (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_add nttCoeffs hadd_rq nttCoeffs_add f g

/-- The concrete NTT is additive. -/
theorem ntt_add (f g : Rq) : ntt (f + g) = ntt f + ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq)
  exact ntt_add_toRq f g

/-- The concrete NTT preserves subtraction. -/
theorem ntt_sub_toRq (f g : Rq) : (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_sub nttCoeffs hsub_rq nttCoeffs_sub f g

/-- The concrete NTT preserves subtraction. -/
theorem ntt_sub (f g : Rq) : ntt (f - g) = ntt f - ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq)
  exact ntt_sub_toRq f g

/-- Coordinate `i` of the concrete NTT is the evaluation of `f` at `ζ^(2·brv(i) + 1)`. -/
theorem ntt_coeff_eq_eval (f : Rq) (i : Fin ringDegree) :
    polyBackend.coeff (ntt f).coeffs i = (polyBackend.toPolynomial f).eval (nttPoint i) := by
  have h := LatticeCrypto.NTTCert.forwardStages_ofFn_dvd (N := polyBackend.degree) (k := 8)
    (fun s => 2 ^ (8 - 1 - s.val))
    (fun s => (LatticeCrypto.NTTCert.ctLayer_shape 8 s).trans degree_eq)
    (fun s g => getZ zetaTable (2 ^ s.val + g.val)) ctPoint ctPoint_sq ctPoint_left ctPoint_right
    nttStage (fun _ => rfl) (polyBackend.coeff f) i.val i.isLt
  have hN : polyBackend.degree / 2 ^ 8 = 1 := rfl
  rw [hN, pow_one, mul_one, LatticeCrypto.NTTCert.blockPoly_zero_eq_toPolynomial,
    ← nttStages_eq_ofFn, LatticeCrypto.NTTCert.blockPoly_one (i := i), ctPoint_last,
    Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
    sub_eq_zero] at h
  rw [← h, ntt_eq, LatticeCrypto.NTTCert.applyCoeffTransform,
    LatticeCrypto.PolyBackend.coeff_build_apply, nttCoeffs]

/-- The concrete NTT turns negacyclic multiplication into the pointwise product. -/
theorem ntt_negacyclicMul (f g : Rq) :
    ntt (negacyclicMul f g) = multiplyNTTs (ntt f) (ntt g) := by
  apply LatticeCrypto.TransformPoly.ext
  refine LatticeCrypto.PolyBackend.ext_coeff (backend := polyBackend) fun i => ?_
  have hmul : negacyclicMul f g = LatticeCrypto.negacyclicMulPure polyKernel f g := rfl
  rw [coeff_multiplyNTTs, ntt_coeff_eq_eval, ntt_coeff_eq_eval, ntt_coeff_eq_eval,
    ← Polynomial.eval_mul, hmul,
    ← sub_eq_zero, ← Polynomial.eval_sub]
  have h1 := LatticeCrypto.NTTCert.X_pow_sub_C_dvd_X_pow_mul_add_one (B := 1)
    (nttPoint_pow_ringDegree i)
  rw [one_mul] at h1
  obtain ⟨q, hq⟩ := h1.trans
    (LatticeCrypto.NTTCert.negacyclicModulus_dvd_toPolynomial_negacyclicMulPure
      polyBackend polyKernel f g)
  rw [hq, Polynomial.eval_mul, Polynomial.eval_sub, pow_one, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_mul]

/-- The pointwise product is negacyclic multiplication transported through the NTT. -/
theorem multiplyNTTs_eq_ntt_negacyclicMul_invNTT (fHat gHat : Tq) :
    multiplyNTTs fHat gHat = ntt (negacyclicMul (invNTT fHat) (invNTT gHat)) := by
  rw [ntt_negacyclicMul, ntt_invNTT, ntt_invNTT]

private theorem invNTT_add (g h : Tq) : invNTT (g + h) = invNTT g + invNTT h := by
  apply ntt_injective
  rw [ntt_invNTT, ntt_add, ntt_invNTT, ntt_invNTT]

private theorem invNTT_sub (g h : Tq) : invNTT (g - h) = invNTT g - invNTT h := by
  apply ntt_injective
  rw [ntt_invNTT, ntt_sub, ntt_invNTT, ntt_invNTT]

private theorem negacyclicMul_coeff (a b : Rq) (k : Fin ringDegree) :
    polyBackend.coeff (negacyclicMul a b) k =
      LatticeCrypto.negacyclicConvCoeff (polyBackend.coeff a) (polyBackend.coeff b) k :=
  LatticeCrypto.negacyclicMulPure_coeff polyKernel a b k

/-- Concrete `NTTRingOps` instance for ML-DSA. -/
@[reducible] def concreteNTTRingOps : NTTRingOps where
  toHat := ntt
  fromHat := invNTT
  mulHat := multiplyNTTs

/-- Proof-oriented algebraic laws for the ML-DSA concrete NTT. -/
theorem concreteNTTRingLaws : NTTRingLaws concreteNTTRingOps where
  fromHat_toHat := invNTT_ntt
  toHat_fromHat := ntt_invNTT
  toHat_zero := by
    change ntt 0 = 0
    rw [ntt_eq]
    apply LatticeCrypto.TransformPoly.ext
    exact LatticeCrypto.NTTCert.applyCoeffTransform_zero nttCoeffs hzero_rq nttCoeffs_zero
  toHat_mul f g := ntt_negacyclicMul f g
  toHat_add f g := ntt_add f g
  toHat_sub f g := ntt_sub f g
  mul_add f g h := by
    change multiplyNTTs f (g + h) = multiplyNTTs f g + multiplyNTTs f h
    simp only [multiplyNTTs_eq_ntt_negacyclicMul_invNTT, invNTT_add]
    rw [← ntt_add]
    exact congrArg ntt (LatticeCrypto.vectorRing_mul_add_right
      (Coeff := Coeff) (n := ringDegree) _ _ _)
  mul_sub f g h := by
    change multiplyNTTs f (g - h) = multiplyNTTs f g - multiplyNTTs f h
    simp only [multiplyNTTs_eq_ntt_negacyclicMul_invNTT, invNTT_sub]
    rw [← ntt_sub]
    exact congrArg ntt (LatticeCrypto.vectorRing_mul_sub_right
      (Coeff := Coeff) (n := ringDegree) _ _ _)
  mul_comm f g := by
    change multiplyNTTs f g = multiplyNTTs g f
    simp only [multiplyNTTs_eq_ntt_negacyclicMul_invNTT, LatticeCrypto.vectorRing_mul_comm]
  mul_assoc f g h := by
    change multiplyNTTs (multiplyNTTs f g) h = multiplyNTTs f (multiplyNTTs g h)
    simp only [multiplyNTTs_eq_ntt_negacyclicMul_invNTT, invNTT_ntt]
    exact congrArg ntt (mul_assoc (invNTT f) (invNTT g) (invNTT h))

end MLDSA.Concrete
