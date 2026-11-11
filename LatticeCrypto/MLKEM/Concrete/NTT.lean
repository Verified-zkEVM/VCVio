/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import all Init.Data.Array.Basic
import all Init.Data.Vector.Algebra
import all LatticeCrypto.MLKEM.Arithmetic
import Mathlib.Tactic.ReduceModChar
public meta import LatticeCrypto.MLKEM.Arithmetic
public meta import LatticeCrypto.MLKEM.Params
public meta import Mathlib.Data.Fintype.Defs
public meta import Mathlib.Data.ZMod.Defs
public import LatticeCrypto.MLKEM.Arithmetic
public import LatticeCrypto.Ring.NTTCert
public import LatticeCrypto.Ring.NTTLoop
public import LatticeCrypto.Ring.NTTSplitCert
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Concrete NTT for ML-KEM

Pure-Lean executable kernels for FIPS 203 Algorithms 9–12 (NTT, NTT⁻¹, MultiplyNTTs,
BaseCaseMultiply), specialised to `q = 3329`, `n = 256`, `ζ = 17`.

The public `ntt` / `invNTT` are the in-place loop kernels `loopNTT` / `loopInvNTT` of Algorithms 9
and 10, so execution keeps the intended `O(n log n)` behavior and the laws below are about the code
that runs. Algorithms 9 and 10 stop after seven of the eight radix-2 layers and run as range loops
over the layer lengths. The range-loop lemmas `ctForward_range` / `ctInverse_range` of
`LatticeCrypto.Ring.NTTLoop` identify them with the seven blocked Cooley–Tukey stages
`ctStage`, each carrying its exact coordinate layout and complementary twiddle law; the loop's
right-minus-left inverse butterfly `z * (u - t)` is `invBfly (-z)`. The structural composition of
the stages proves the inverse laws after the final normalization.

## Coefficient pairs and `MultiplyNTTs`

FIPS 203 Section 4.3 defines `γᵢ = ζ^(2 · BitRev₇(i) + 1)` for `i = 0, …, 127` (`nttGamma`).
Coordinates `(2i, 2i+1)` of `ntt f` are the coefficients of `f mod (X² − γᵢ)` (`ntt_coeff_pair`),
and Algorithm 11 multiplies each pair in `ℤ_q[X]/(X² − γᵢ)` with Algorithm 12
(`multiplyNTTs_pair`, `baseCaseMultiply`). Hence `ntt` maps negacyclic multiplication to
`multiplyNTTs` (`ntt_negacyclicMul`).

The last butterfly layer of Algorithm 9 (`len = 2`) uses `zetaArray[64 + g]` on the group of 4
coefficients starting at `4g`, so `γ_{2g} = zetaArray[64 + g]` and `γ_{2g+1} = −zetaArray[64 + g]`.
`multiplyNTTs` reads its twiddles from this table, as do the
[pqcrystals reference](https://github.com/pq-crystals/kyber/blob/main/ref/poly.c)
and [mlkem-native](https://github.com/pq-code-package/mlkem-native). The executable kernels are
also checked byte-for-byte against mlkem-native for multiple key pairs, encapsulations, and
decapsulations (see `LatticeCryptoTest/MLKEM/Main.lean`).
-/

public section



namespace MLKEM.Concrete

open MLKEM

/-! ## Bit reversal and zeta table -/

/-- Reverse the low 7 bits of `i`. -/
def bitRev7 (i : Nat) : Nat :=
  let b := fun k => (i >>> k) &&& 1
  (b 0 <<< 6) ||| (b 1 <<< 5) ||| (b 2 <<< 4) ||| (b 3 <<< 3) |||
  (b 4 <<< 2) ||| (b 5 <<< 1) ||| b 6

/-- Precomputed twiddle factors `ζ^{BitRev₇(i)}` for `i = 0 … 127`. -/
def zetaArray : Array Coeff :=
  (Array.range 128).map fun i => zeta ^ bitRev7 i

/-- `128⁻¹ mod 3329 = 3303`. Applied after the inverse NTT. -/
private def nInv : Coeff := 3303

/-- Safe array access with fallback to zero. -/
private def getZ (a : Array Coeff) (i : Nat) : Coeff := a.getD i 0

private theorem bitRev7_layer_partner :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      bitRev7 (2 ^ s.val + g.val) +
          bitRev7 (2 ^ (s.val + 1) - 1 - g.val) = 128 := by
  decide

private theorem layer_twiddle_index_bounds :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      2 ^ s.val + g.val < 128 ∧
        2 ^ (s.val + 1) - 1 - g.val < 128 := by
  decide

private theorem getZ_zetaArray (i : Nat) (hi : i < 128) :
    getZ zetaArray i = zeta ^ bitRev7 i := by
  simp [getZ, zetaArray, hi]

private theorem zeta_pow_128 : (zeta : Coeff) ^ 128 = -1 := by
  change (17 : ZMod 3329) ^ 128 = -1
  reduce_mod_char

/-- `ζ = 17` is a primitive `256`-th root of unity in `ℤ_q` (FIPS 203 §4.3): the twiddle half of
the NTT correctness argument. -/
theorem zeta_isPrimitiveRoot : IsPrimitiveRoot (zeta : Coeff) 256 := by
  change IsPrimitiveRoot (17 : ZMod 3329) 256
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by reduce_mod_char) ?_
  intro p hp hdvd
  obtain rfl : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 8 by simpa using hdvd))
  reduce_mod_char
  decide

/-- The twiddle used by a forward butterfly and the complementary twiddle
used by its matching inverse butterfly multiply to `-1`. -/
private theorem zetaArray_layer_partner :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      getZ zetaArray (2 ^ s.val + g.val) *
          getZ zetaArray (2 ^ (s.val + 1) - 1 - g.val) = -1 := by
  intro s g
  obtain ⟨hforward, hinverse⟩ := layer_twiddle_index_bounds s g
  rw [getZ_zetaArray _ hforward, getZ_zetaArray _ hinverse, ← pow_add]
  rw [bitRev7_layer_partner s g, zeta_pow_128]

/-! ## Forward NTT (Algorithm 9) -/

private def nttLayer (a : Array Coeff) (len : Nat) (k : Nat) : Array Coeff × Nat := Id.run do
  let mut arr := a
  let mut ki := k
  let numGroups := 256 / (2 * len)
  for s in [0:numGroups] do
    let start := s * 2 * len
    let z := getZ zetaArray ki
    ki := ki + 1
    for jj in [0:len] do
      let j := start + jj
      let t := z * getZ arr (j + len)
      let fj := getZ arr j
      arr := arr.set! (j + len) (fj - t)
      arr := arr.set! j (fj + t)
  return (arr, ki)

/-- FIPS 203 Algorithm 9: executable loop kernel for the Number-Theoretic Transform. -/
def loopNTT (f : Rq) : Tq :=
  let (a, _) := [128, 64, 32, 16, 8, 4, 2].foldl
    (fun (a, k) len => nttLayer a len k) (f.toArray, 1)
  ⟨Vector.ofFn fun i => getZ a i.val⟩

/-! ## Inverse NTT (Algorithm 10) -/

private def invNttLayer (a : Array Coeff) (len : Nat) (k : Nat) :
    Array Coeff × Nat := Id.run do
  let mut arr := a
  let mut ki := k
  let numGroups := 256 / (2 * len)
  for s in [0:numGroups] do
    let start := s * 2 * len
    let z := getZ zetaArray ki
    ki := ki - 1
    for jj in [0:len] do
      let j := start + jj
      let t := getZ arr j
      let u := getZ arr (j + len)
      arr := arr.set! j (t + u)
      arr := arr.set! (j + len) (z * (u - t))
  return (arr, ki)

/-- FIPS 203 Algorithm 10: executable loop kernel for the inverse Number-Theoretic Transform. -/
def loopInvNTT (fHat : Tq) : Rq :=
  let (a, _) := [2, 4, 8, 16, 32, 64, 128].foldl
    (fun (a, k) len => invNttLayer a len k) (fHat.toArray, 127)
  Vector.ofFn fun i => nInv * getZ a i.val

/-! ## Base-case multiplication and MultiplyNTTs (Algorithms 11 and 12) -/

/-- FIPS 203 Algorithm 12 (`BaseCaseMultiply`): the product of `a0 + a1·X` and `b0 + b1·X` in
`ℤ_q[X]/(X² − γ)`. -/
def baseCaseMultiply (a0 a1 b0 b1 γ : Coeff) : Coeff × Coeff :=
  (a0 * b0 + a1 * b1 * γ, a0 * b1 + a1 * b0)

/-- Unfolding lemma for `baseCaseMultiply`. -/
theorem baseCaseMultiply_eq (a0 a1 b0 b1 γ : Coeff) :
    baseCaseMultiply a0 a1 b0 b1 γ = (a0 * b0 + a1 * b1 * γ, a0 * b1 + a1 * b0) := by
  unfold baseCaseMultiply; rfl

/-- FIPS 203 Algorithm 11 (`MultiplyNTTs`): `BaseCaseMultiply` on each coefficient pair
`(2i, 2i+1)` with `γᵢ = ζ^(2·BitRev₇(i)+1)` (`multiplyNTTs_pair`). Within each group `g` of 4
coefficients, the pair at `(4g, 4g+1)` uses `zetaArray[64+g]` and the pair at `(4g+2, 4g+3)` uses
its negation. -/
def multiplyNTTs (fHat gHat : Tq) : Tq :=
  let fa := fHat.toArray
  let ga := gHat.toArray
  ⟨Vector.ofFn fun idx =>
    let pos := idx.val
    let group := pos / 4
    let z := getZ zetaArray (64 + group)
    let gamma := if (pos / 2) % 2 == 0 then z else -z
    let base := (pos / 2) * 2
    let a0 := getZ fa base
    let a1 := getZ fa (base + 1)
    let b0 := getZ ga base
    let b1 := getZ ga (base + 1)
    let c := baseCaseMultiply a0 a1 b0 b1 gamma
    if pos % 2 == 0 then c.1 else c.2⟩

/-- Coordinate `2i`, the first coefficient of pair `i`. -/
@[expose] def pairFst (i : Fin 128) : Fin polyBackend.degree :=
  ⟨2 * i.val, by have := i.isLt; change _ < 256; omega⟩

/-- Coordinate `2i + 1`, the second coefficient of pair `i`. -/
@[expose] def pairSnd (i : Fin 128) : Fin polyBackend.degree :=
  ⟨2 * i.val + 1, by have := i.isLt; change _ < 256; omega⟩

@[simp] theorem val_pairFst (i : Fin 128) : (pairFst i).val = 2 * i.val := rfl

@[simp] theorem val_pairSnd (i : Fin 128) : (pairSnd i).val = 2 * i.val + 1 := rfl

private abbrev NTTCoord := Fin polyBackend.degree

private theorem degree_eq : 2 ^ 8 = polyBackend.degree := rfl

/-- The inverse twiddle of group `g` in layer `s` times the forward twiddle is `1`. -/
private theorem zetaArray_twiddle_partner (s : Fin 7) (g : Fin (2 ^ s.val)) :
    -getZ zetaArray (2 ^ (s.val + 1) - 1 - g.val) * getZ zetaArray (2 ^ s.val + g.val) = 1 := by
  rw [neg_mul, mul_comm, zetaArray_layer_partner s g, neg_neg]

/-- Layer `s` of Algorithms 9 and 10: the first seven of the eight radix-2 layers on `256`
coefficients. -/
private def nttStage (s : Fin 7) : LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord :=
  LatticeCrypto.NTTCert.ctStage (by decide) degree_eq (getZ zetaArray) zetaArray_twiddle_partner s

/-- The seven forward layers, ordered as Algorithm 9 executes them. -/
private def nttStages :
    List (LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord) :=
  [nttStage 0, nttStage 1, nttStage 2, nttStage 3, nttStage 4, nttStage 5, nttStage 6]

/-! ## Evaluation moduli -/

/-- The modulus constant `γᵢ = ζ^(2·BitRev₇(i) + 1)` of the `i`-th quadratic factor
`X² − γᵢ` of `X^256 + 1` (FIPS 203 §4.3). -/
def nttGamma (i : Fin 128) : Coeff := zeta ^ (2 * bitRev7 i.val + 1)

/-- Unfolding lemma for `nttGamma`. -/
theorem nttGamma_eq (i : Fin 128) : nttGamma i = zeta ^ (2 * bitRev7 i.val + 1) := by
  unfold nttGamma; rfl

/-- Each `X² − γᵢ` divides `X^256 + 1`: `γᵢ^128 = −1`. -/
theorem nttGamma_pow_128 (i : Fin 128) : nttGamma i ^ 128 = -1 := by
  rw [nttGamma_eq, ← pow_mul, mul_comm, pow_mul, zeta_pow_128]
  exact Odd.neg_one_pow ⟨bitRev7 i.val, rfl⟩

/-- The residue point of block `g` after `t` layers: block `g` of size `2^(7-t)` is congruent to
the input modulo `X^(2^(7-t)) − ctPoint t g`. -/
private def ctPoint (t g : ℕ) : Coeff := zeta ^ (2 * bitRev7 g + 2 ^ (7 - t))

private theorem bitRev7_ct_sq : ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
    2 * bitRev7 (2 ^ s.val + g.val) = 2 * bitRev7 g.val + 2 ^ (7 - s.val) := by
  decide

private theorem bitRev7_ct_left : ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
    2 * bitRev7 (2 * g.val) + 2 ^ (6 - s.val) = bitRev7 (2 ^ s.val + g.val) := by
  decide

private theorem bitRev7_ct_right : ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
    2 * bitRev7 (2 * g.val + 1) + 2 ^ (6 - s.val) = bitRev7 (2 ^ s.val + g.val) + 128 := by
  decide

private theorem ctPoint_sq (s : Fin 7) (g : Fin (2 ^ s.val)) :
    (getZ zetaArray (2 ^ s.val + g.val)) ^ 2 = ctPoint s.val g.val := by
  rw [getZ_zetaArray _ (layer_twiddle_index_bounds s g).1, ← pow_mul, ctPoint, Nat.mul_comm,
    bitRev7_ct_sq s g]

private theorem ctPoint_left (s : Fin 7) (g : Fin (2 ^ s.val)) :
    ctPoint (s.val + 1) (2 * g.val) = getZ zetaArray (2 ^ s.val + g.val) := by
  rw [getZ_zetaArray _ (layer_twiddle_index_bounds s g).1, ctPoint,
    show 7 - (s.val + 1) = 6 - s.val by omega, bitRev7_ct_left s g]

private theorem ctPoint_right (s : Fin 7) (g : Fin (2 ^ s.val)) :
    ctPoint (s.val + 1) (2 * g.val + 1) = -getZ zetaArray (2 ^ s.val + g.val) := by
  rw [getZ_zetaArray _ (layer_twiddle_index_bounds s g).1, ctPoint,
    show 7 - (s.val + 1) = 6 - s.val by omega, bitRev7_ct_right s g, pow_add, zeta_pow_128,
    mul_neg_one]

private theorem ctPoint_last (i : Fin 128) : ctPoint 7 i.val = nttGamma i := by
  rfl

/-- The last butterfly layer's twiddles: `γ_{2g} = zetaArray[64 + g]` and
`γ_{2g+1} = −zetaArray[64 + g]`. -/
private theorem nttGamma_eq_getZ (i : Fin 128) :
    nttGamma i = if i.val % 2 = 0 then getZ zetaArray (64 + i.val / 2)
      else -getZ zetaArray (64 + i.val / 2) := by
  have hg : i.val / 2 < 2 ^ (6 : Fin 7).val := by have := i.isLt; simp; omega
  rw [← ctPoint_last]
  split_ifs with h
  · convert ctPoint_left 6 ⟨i.val / 2, hg⟩ using 2
    all_goals simp
    omega
  · convert ctPoint_right 6 ⟨i.val / 2, hg⟩ using 2
    all_goals simp
    omega

private theorem nttStages_eq_ofFn : nttStages = List.ofFn nttStage := by
  simp [nttStages, List.ofFn_succ]

private theorem nInv_stageScalar :
    nInv * LatticeCrypto.NTTCert.stageScalar nttStages = 1 := by
  change ((3303 * 128 : Nat) : ZMod 3329) = ((1 : Nat) : ZMod 3329)
  rw [ZMod.natCast_eq_natCast_iff']

/-- Named proof-facing coefficient transform. Keeping the assembled stage list behind this
boundary lets downstream algebraic proofs use focused interface lemmas. -/
private def nttCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.forwardStages nttStages input

/-- Named proof-facing inverse coefficient transform, including the final normalization. -/
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

/-- The NTT, computed by the loop kernel `loopNTT`. -/
def ntt (f : Rq) : Tq := loopNTT f

/-- The inverse NTT, computed by the loop kernel `loopInvNTT`. -/
def invNTT (fHat : Tq) : Rq := loopInvNTT fHat

private theorem nttLayer_eq (a : Array Coeff) (len k : ℕ) :
    nttLayer a len k = LatticeCrypto.NTTCert.rangeLayer polyBackend.degree
      (fun len k => LatticeCrypto.NTTCert.fwdBfly (getZ zetaArray k) len) (· + 1) (a, k) len := by
  simp only [nttLayer, LatticeCrypto.NTTCert.forIn_range_pure, pure_bind, Nat.sub_zero]
  rfl

/-- The butterfly of Algorithm 10 is the inverse butterfly with the negated twiddle. -/
private theorem invNttBfly_eq (z : Coeff) (len : ℕ) (b : Array Coeff) (j : ℕ) :
    (b.set! j (getZ b j + getZ b (j + len))).set! (j + len) (z * (getZ b (j + len) - getZ b j)) =
      LatticeCrypto.NTTCert.invBfly (-z) len b j := by
  simp only [LatticeCrypto.NTTCert.invBfly, getZ, neg_mul, ← mul_neg, neg_sub]

private theorem invNttLayer_eq (a : Array Coeff) (len k : ℕ) :
    invNttLayer a len k = LatticeCrypto.NTTCert.rangeLayer polyBackend.degree
      (fun len k => LatticeCrypto.NTTCert.invBfly (-getZ zetaArray k) len) (· - 1) (a, k) len := by
  simp only [invNttLayer, invNttBfly_eq, LatticeCrypto.NTTCert.forIn_range_pure, pure_bind,
    Nat.sub_zero]
  rfl

private theorem loopNTT_layers (f : Rq) :
    loopNTT f = ⟨Vector.ofFn fun i =>
      (((List.range' 0 7).map fun s => 2 ^ (8 - 1 - s)).foldl
        (LatticeCrypto.NTTCert.rangeLayer polyBackend.degree
          (fun len k => LatticeCrypto.NTTCert.fwdBfly (getZ zetaArray k) len) (· + 1))
        (f.toArray, 1)).1.getD i 0⟩ := by
  simp only [loopNTT, nttLayer_eq]
  rfl

private theorem loopInvNTT_layers (fHat : Tq) :
    loopInvNTT fHat = Vector.ofFn fun i => nInv *
      (((List.range' 0 7).map fun i => 2 ^ (8 - 7 + i)).foldl
        (LatticeCrypto.NTTCert.rangeLayer polyBackend.degree
          (fun len k => LatticeCrypto.NTTCert.invBfly (-getZ zetaArray k) len) (· - 1))
        (fHat.coeffs.toArray, 2 ^ 7 - 1)).1.getD i 0 := by
  simp only [loopInvNTT, invNttLayer_eq]
  rfl

/-- `ntt` is the seven blocked butterfly layers. -/
private theorem ntt_eq (f : Rq) :
    ntt f = ⟨LatticeCrypto.NTTCert.applyCoeffTransform polyBackend nttCoeffs f⟩ := by
  rw [ntt, loopNTT_layers, LatticeCrypto.NTTCert.ctForward_range (by decide) degree_eq _
    zetaArray_twiddle_partner (LatticeCrypto.NTTCert.vector_toArray_eq_ofFn f)]
  simp only [LatticeCrypto.NTTCert.getD_ofFn_eq_coeffAt, LatticeCrypto.NTTCert.coeffAt_fin]
  rfl

/-- `invNTT` is the seven inverse layers followed by scaling by `nInv`. -/
private theorem invNTT_eq (fHat : Tq) :
    invNTT fHat =
      LatticeCrypto.NTTCert.applyCoeffTransform polyBackend invNTTCoeffs fHat.coeffs := by
  rw [invNTT, loopInvNTT_layers, LatticeCrypto.NTTCert.ctInverse_range (by decide) degree_eq _
    zetaArray_twiddle_partner (LatticeCrypto.NTTCert.vector_toArray_eq_ofFn fHat.coeffs)]
  simp only [LatticeCrypto.NTTCert.getD_ofFn_eq_coeffAt, LatticeCrypto.NTTCert.coeffAt_fin]
  rfl

/-- The concrete inverse transform is a left inverse to the concrete forward transform. -/
theorem invNTT_ntt (f : Rq) : invNTT (ntt f) = f := by
  rw [invNTT_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_comp
    nttCoeffs invNTTCoeffs invNTTCoeffs_nttCoeffs f

private theorem ntt_injective : Function.Injective ntt := by
  intro f g h
  have hInv := congrArg invNTT h
  simpa [invNTT_ntt] using hInv

private theorem ntt_surjective : Function.Surjective ntt := by
  let : NeZero modulus := ⟨by norm_num [modulus]⟩
  let : Fintype Coeff := by
    dsimp [Coeff]
    exact ZMod.fintype modulus
  exact ntt_injective.surjective_of_finite (LatticeCrypto.TransformPoly.equivPoly _).symm

/-- The concrete forward transform is a left inverse to the concrete inverse transform. -/
theorem ntt_invNTT (fHat : Tq) : ntt (invNTT fHat) = fHat := by
  obtain ⟨f, hf⟩ := ntt_surjective fHat
  calc
    ntt (invNTT fHat) = ntt (invNTT (ntt f)) := by rw [hf]
    _ = ntt f := by rw [invNTT_ntt]
    _ = fHat := hf

/-- The concrete NTT is additive on the coefficient-vector carrier of `T_q`. -/
theorem ntt_add_toRq (f g : Rq) : (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_add nttCoeffs
    (fun f g => funext (LatticeCrypto.NegacyclicRing.coeff_add coeffRing f g))
    nttCoeffs_add f g

/-- The concrete NTT preserves subtraction on the coefficient-vector carrier of `T_q`. -/
theorem ntt_sub_toRq (f g : Rq) : (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_sub nttCoeffs
    (fun f g => funext (LatticeCrypto.NegacyclicRing.coeff_sub coeffRing f g))
    nttCoeffs_sub f g

/-- The concrete NTT is additive. -/
theorem ntt_add (f g : Rq) : ntt (f + g) = ntt f + ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq)
  exact ntt_add_toRq f g

/-- The concrete NTT preserves subtraction. -/
theorem ntt_sub (f g : Rq) : ntt (f - g) = ntt f - ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq)
  exact ntt_sub_toRq f g

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

/-! ## Multiplication in the NTT domain -/

private theorem coeff_ntt (f : Rq) (j : Fin polyBackend.degree) :
    polyBackend.coeff (ntt f).coeffs j =
      LatticeCrypto.NTTCert.coeffAt (LatticeCrypto.NTTCert.forwardStages nttStages
        (polyBackend.coeff f)) j.val := by
  rw [LatticeCrypto.NTTCert.coeffAt_fin, ntt_eq, LatticeCrypto.NTTCert.applyCoeffTransform,
    LatticeCrypto.PolyBackend.coeff_build_apply, nttCoeffs]

/-- Coordinates `(2i, 2i+1)` of the concrete NTT are the coefficients of `f mod (X² − γᵢ)`. -/
theorem ntt_coeff_pair (f : Rq) (i : Fin 128) :
    Polynomial.X ^ 2 - Polynomial.C (nttGamma i) ∣
      Polynomial.C (polyBackend.coeff (ntt f).coeffs (pairFst i)) +
        Polynomial.C (polyBackend.coeff (ntt f).coeffs (pairSnd i)) * Polynomial.X -
        polyBackend.toPolynomial f := by
  have h := LatticeCrypto.NTTCert.forwardStages_ofFn_dvd (N := polyBackend.degree) (k := 7)
    (fun s => 2 ^ (8 - 1 - s.val))
    (fun s => (LatticeCrypto.NTTCert.ctLayer_shape 8 (Fin.castLE (by decide) s)).trans degree_eq)
    (fun s g => getZ zetaArray (2 ^ s.val + g.val)) ctPoint ctPoint_sq ctPoint_left ctPoint_right
    nttStage (fun _ => rfl) (polyBackend.coeff f) i.val i.isLt
  have hN : polyBackend.degree / 2 ^ 7 = 2 := rfl
  rw [hN, LatticeCrypto.NTTCert.blockPoly_zero_eq_toPolynomial, ← nttStages_eq_ofFn,
    LatticeCrypto.NTTCert.blockPoly_two, ctPoint_last] at h
  rw [coeff_ntt, coeff_ntt]
  rw [Nat.mul_comm _ 2] at h
  exact h

private theorem getZ_toArray (fHat : Tq) {n m : ℕ} (hm : m < polyBackend.degree) (h : n = m) :
    getZ fHat.toArray n = polyBackend.coeff fHat.coeffs ⟨m, hm⟩ := by
  subst h
  have hm' : n < 256 := hm
  change (fHat.coeffs : Vector Coeff 256).toArray.getD n 0 =
    (fHat.coeffs : Vector Coeff 256).get ⟨n, hm'⟩
  have hs : n < fHat.coeffs.toArray.size :=
    Nat.lt_of_lt_of_eq hm' (Vector.size_toArray (self := (fHat.coeffs : Vector Coeff 256))).symm
  simp only [Array.getD, hs, ↓reduceDIte]
  rfl

/-- FIPS 203 Algorithm 11: coordinates `(2i, 2i+1)` of `multiplyNTTs fHat gHat` are
`BaseCaseMultiply` of the corresponding coordinates of `fHat` and `gHat` with `γᵢ`. -/
theorem multiplyNTTs_pair (fHat gHat : Tq) (i : Fin 128) :
    (polyBackend.coeff (multiplyNTTs fHat gHat).coeffs (pairFst i),
      polyBackend.coeff (multiplyNTTs fHat gHat).coeffs (pairSnd i)) =
      baseCaseMultiply
        (polyBackend.coeff fHat.coeffs (pairFst i)) (polyBackend.coeff fHat.coeffs (pairSnd i))
        (polyBackend.coeff gHat.coeffs (pairFst i)) (polyBackend.coeff gHat.coeffs (pairSnd i))
        (nttGamma i) := by
  have hi := i.isLt
  have h0 : 2 * i.val < polyBackend.degree := by change _ < 256; omega
  have h1 : 2 * i.val + 1 < polyBackend.degree := by change _ < 256; omega
  have e2 : (2 * i.val + 1) / 2 = i.val := by omega
  have e3 : 2 * i.val / 2 = i.val := by omega
  have e4 : 2 * i.val / 4 = i.val / 2 := by omega
  have e5 : (2 * i.val + 1) / 4 = i.val / 2 := by omega
  have hγ : (if i.val % 2 == 0 then getZ zetaArray (64 + i.val / 2)
      else -getZ zetaArray (64 + i.val / 2)) = nttGamma i := by
    rw [nttGamma_eq_getZ]
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h <;> simp [h]
  refine Prod.ext ?_ ?_
  · change (Vector.ofFn _).get ⟨2 * i.val, h0⟩ = _
    rw [Vector.get_ofFn]
    simp only [e3, e4, hγ, baseCaseMultiply_eq, pairFst, pairSnd]
    simp [getZ_toArray fHat h0 (Nat.mul_comm _ _), getZ_toArray gHat h0 (Nat.mul_comm _ _),
      getZ_toArray fHat h1 (by rw [Nat.mul_comm]), getZ_toArray gHat h1 (by rw [Nat.mul_comm])]
  · change (Vector.ofFn _).get ⟨2 * i.val + 1, h1⟩ = _
    rw [Vector.get_ofFn]
    simp only [e2, e5, hγ, baseCaseMultiply_eq, pairFst, pairSnd]
    simp [getZ_toArray fHat h0 (Nat.mul_comm _ _), getZ_toArray gHat h0 (Nat.mul_comm _ _),
      getZ_toArray fHat h1 (by rw [Nat.mul_comm]), getZ_toArray gHat h1 (by rw [Nat.mul_comm])]

/-- The concrete NTT turns negacyclic multiplication into `multiplyNTTs`. -/
theorem ntt_negacyclicMul (f g : Rq) :
    ntt (negacyclicMul f g) = multiplyNTTs (ntt f) (ntt g) := by
  apply LatticeCrypto.TransformPoly.ext
  refine LatticeCrypto.PolyBackend.ext_coeff (backend := polyBackend) fun pos => ?_
  have hpos : pos.val < 256 := pos.isLt
  let i : Fin 128 := ⟨pos.val / 2, by omega⟩
  have hFG : Polynomial.X ^ 2 - Polynomial.C (nttGamma i) ∣
      polyBackend.toPolynomial (negacyclicMul f g) -
        polyBackend.toPolynomial f * polyBackend.toPolynomial g :=
    (LatticeCrypto.NTTCert.X_pow_sub_C_dvd_X_pow_mul_add_one (B := 2)
      (nttGamma_pow_128 i)).trans
      (LatticeCrypto.NTTCert.negacyclicModulus_dvd_toPolynomial_negacyclicMulPure
        polyBackend polyKernel f g)
  obtain ⟨hc0, hc1⟩ := LatticeCrypto.NTTCert.baseCaseMul_of_dvd (ntt_coeff_pair f i)
    (ntt_coeff_pair g i) (ntt_coeff_pair (negacyclicMul f g) i) hFG
  have hm := multiplyNTTs_pair (ntt f) (ntt g) i
  simp only [baseCaseMultiply_eq, Prod.mk.injEq] at hm
  rcases Nat.mod_two_eq_zero_or_one pos.val with h | h
  · have hp : pos = pairFst i := Fin.ext (by simp [i]; omega)
    rw [hp, hc0, hm.1]
  · have hp : pos = pairSnd i := Fin.ext (by simp [i]; omega)
    rw [hp, hc1, hm.2]

/-- `multiplyNTTs` is negacyclic multiplication transported through the NTT. -/
theorem multiplyNTTs_eq_ntt_negacyclicMul_invNTT (fHat gHat : Tq) :
    multiplyNTTs fHat gHat = ntt (negacyclicMul (invNTT fHat) (invNTT gHat)) := by
  rw [ntt_negacyclicMul, ntt_invNTT, ntt_invNTT]

/-- Concrete `NTTRingOps` instance for ML-KEM. -/
@[reducible] def concreteNTTRingOps : NTTRingOps where
  toHat := ntt
  fromHat := invNTT
  mulHat := multiplyNTTs

/-- Proof bundle showing that the concrete ML-KEM NTT implementation satisfies the abstract
`NTTRingLaws`. -/
theorem concreteNTTRingLaws : NTTRingLaws concreteNTTRingOps where
  fromHat_toHat := invNTT_ntt
  toHat_fromHat := ntt_invNTT
  toHat_zero := by
    change ntt 0 = 0
    rw [ntt_eq]
    apply LatticeCrypto.TransformPoly.ext
    exact LatticeCrypto.NTTCert.applyCoeffTransform_zero nttCoeffs
      (funext (LatticeCrypto.NegacyclicRing.coeff_zero coeffRing)) nttCoeffs_zero
  toHat_mul f g := ntt_negacyclicMul f g
  toHat_add f g := by
    change ntt (f + g) = ntt f + ntt g
    exact ntt_add f g
  toHat_sub f g := by
    change ntt (f - g) = ntt f - ntt g
    exact ntt_sub f g
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

end MLKEM.Concrete
