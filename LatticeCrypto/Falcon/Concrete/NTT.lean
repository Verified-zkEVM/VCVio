/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
import Mathlib.Tactic.ReduceModChar
public import LatticeCrypto.Falcon.Arithmetic
public import LatticeCrypto.Ring.NTTCert
public import LatticeCrypto.Ring.NTTLoop
public import LatticeCrypto.Ring.NTTSplitCert
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Concrete NTT for Falcon

Concrete executable NTT operations for `q = 12289`, parameterized by ring degree `n`.
Falcon uses `n ∈ {512, 1024}` (logn ∈ {9, 10}).

The NTT splits `R_q = ℤ_q[x]/(x^n + 1)` into `n` linear factors since
`q ≡ 1 mod 2n` for both parameter sets (`12289 = 12·1024 + 1`).

Implements in-place Cooley–Tukey (forward) and Gentleman–Sande (inverse) butterflies,
with twiddle factors `ζ^(brv(k))` where `ζ` is a primitive `2n`-th root of unity mod `q`.

`11` is a primitive root mod `12289` (order `12288 = 2^12 · 3`), so:
- For `n = 1024`: `ζ = 11^(12288/2048) = 11^6 mod 12289`
- For `n = 512`:  `ζ = 11^(12288/1024) = 11^12 mod 12289`

For `logn ≤ 11` (`n ≤ 2048`), entry `i` of `ntt logn f` is `f(ζ^(2·brv(i) + 1))`
(`ntt_coeff_eq_eval`), and these are `n` distinct roots of `X^n + 1` (`nttPoint_injective`,
`nttPoint_pow_two_pow`). Evaluation at the roots makes the ring operations coordinate-wise
(Falcon specification v1.2, §3.5): `ntt` is additive (`ntt_add`, `ntt_sub`) and maps negacyclic
multiplication to the pointwise product `multiplyNTTs` (`ntt_negacyclicMul`). `invNTT` is its
two-sided inverse (`invNTT_ntt`, `ntt_invNTT`), and `concreteNTTRingLaws` collects these laws.
The loops of `butterflyNTT` and `butterflyInvNTT` are proved equal to `logn` blocked butterfly
stages of `LatticeCrypto.Ring.NTTCert`; the inverse then scales by `nInv`. So the laws hold for the
in-place loops themselves.
-/

public section


namespace Falcon.Concrete

open Falcon

private def primitiveRoot2N (logn : ℕ) : Coeff :=
  (11 : Coeff) ^ ((modulus - 1) / (2 * (2 ^ logn)))

/-- `primitiveRoot2N 10 = 11 ^ 6` is a primitive `2048`-th root of unity in `ℤ_q` (`n = 1024`): the
twiddle half of an NTT correctness argument for the concrete backend. -/
private theorem primitiveRoot2N_isPrimitiveRoot_1024 :
    IsPrimitiveRoot (primitiveRoot2N 10) 2048 := by
  change IsPrimitiveRoot ((11 : ZMod 12289) ^ 6) 2048
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by reduce_mod_char) ?_
  intro p hp hdvd
  obtain rfl : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 11 by simpa using hdvd))
  reduce_mod_char
  decide

/-- `primitiveRoot2N 9 = 11 ^ 12` is a primitive `1024`-th root of unity in `ℤ_q` (`n = 512`). -/
private theorem primitiveRoot2N_isPrimitiveRoot_512 :
    IsPrimitiveRoot (primitiveRoot2N 9) 1024 := by
  change IsPrimitiveRoot ((11 : ZMod 12289) ^ 12) 1024
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by reduce_mod_char) ?_
  intro p hp hdvd
  obtain rfl : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 10 by simpa using hdvd))
  reduce_mod_char
  decide

private def bitRevN (logn : ℕ) (i : Nat) : Nat := Id.run do
  let mut r := 0
  let mut v := i
  for k in [0:logn] do
    r := r ||| ((v &&& 1) <<< (logn - 1 - k))
    v := v >>> 1
  return r

/-- The twiddle factors `ζ^(brv i)` for `i < 2^logn`, where `brv` reverses `logn`-bit indices and
`ζ = 11^((q - 1) / 2^(logn + 1))`, a primitive `2^(logn + 1)`-th root of unity modulo `q` for
`logn ≤ 11`. -/
def zetaTable (logn : ℕ) : Array Coeff :=
  let n := 2 ^ logn
  let z := primitiveRoot2N logn
  (Array.range n).map fun i => z ^ bitRevN logn i

/-- The inverse of `n = 2^logn` modulo `q` for `n ∣ q - 1`, computed as `q - (q - 1) / n`; it
scales the output of `butterflyInvNTT`. -/
def nInv (logn : ℕ) : Coeff :=
  let n := (2 ^ logn : ℕ)
  ((modulus - (modulus - 1) / n : ℕ) : Coeff)

/-- The forward NTT of `f ∈ ℤ_q[x]/(x^n + 1)`, `n = 2^logn`, by in-place Cooley–Tukey
butterflies with twiddles from `zetaTable`. Entry `i` of the result is `f(ζ^(2 · brv i + 1))`,
so the evaluations at the roots of `x^n + 1` appear in bit-reversed order. -/
def butterflyNTT (logn : ℕ) (f : Rq (2 ^ logn)) : Tq (2 ^ logn) := Id.run do
  let n := 2 ^ logn
  let table := zetaTable logn
  let mut a := f.toArray
  let mut k := 1
  let mut len := n / 2
  while len ≥ 1 do
    let mut start := 0
    while start < n do
      let z := table.getD k 0
      k := k + 1
      for j in [start : start + len] do
        let u := a.getD j 0
        let v := a.getD (j + len) 0
        let t := z * v
        a := a.set! (j + len) (u - t)
        a := a.set! j (u + t)
      start := start + 2 * len
    len := len / 2
  return ⟨Vector.ofFn fun i => a.getD i.val 0⟩

/-- The inverse of `butterflyNTT`, by in-place Gentleman–Sande butterflies with the negated
twiddles taken in reverse order, followed by scaling by `nInv`. -/
def butterflyInvNTT (logn : ℕ) (fHat : Tq (2 ^ logn)) : Rq (2 ^ logn) := Id.run do
  let n := 2 ^ logn
  let table := zetaTable logn
  let mut a := fHat.toArray
  let mut k := n - 1
  let mut len := 1
  while len ≤ n / 2 do
    let mut start := 0
    while start < n do
      let z := -(table.getD k 0)
      k := k - 1
      for j in [start : start + len] do
        let u := a.getD j 0
        let v := a.getD (j + len) 0
        a := a.set! j (u + v)
        a := a.set! (j + len) (z * (u - v))
      start := start + 2 * len
    len := len * 2
  let scale := nInv logn
  for j in [0 : n] do
    a := a.set! j (scale * a.getD j 0)
  return Vector.ofFn fun i => a.getD i.val 0

/-- Multiplication in the NTT domain: the pointwise product of two transforms. -/
def multiplyNTTs {n : ℕ} (fHat gHat : Tq n) : Tq n :=
  ⟨Vector.ofFn fun i => fHat[i.val] * gHat[i.val]⟩

/-! ## Public API -/

/-- The NTT of a Falcon polynomial modulo `q = 12289`, computed by `butterflyNTT`. -/
def ntt (logn : ℕ) (f : Rq (2 ^ logn)) : Tq (2 ^ logn) := butterflyNTT logn f

/-- The inverse NTT modulo `q = 12289`, computed by `butterflyInvNTT`. -/
def invNTT (logn : ℕ) (fHat : Tq (2 ^ logn)) : Rq (2 ^ logn) :=
  butterflyInvNTT logn fHat

/-- The executable transform-domain operations for degree `2^logn`: `ntt`, `invNTT` and the
pointwise product `multiplyNTTs`. -/
@[reducible] def concreteNTTRingOps (logn : ℕ) : NTTRingOps (2 ^ logn) where
  toHat := ntt logn
  fromHat := invNTT logn
  mulHat := multiplyNTTs

/-! ## Correctness

The loops of `butterflyNTT` and `butterflyInvNTT` compute the blocked butterfly stages of
`LatticeCrypto.Ring.NTTCert`, layer by layer (`ctForward_loop` and `ctInverse_loop` of
`LatticeCrypto.Ring.NTTLoop`). So the transform laws follow from the structural
certificates: the residue theorem `forwardStages_ofFn_dvd` and the stage roundtrip
`scale_inverseStages_forwardStages`. -/

open LatticeCrypto LatticeCrypto.NTTCert

/-! ### Bit reversal -/

/-- Reversal of the low `m` bits of `i`, appending one bit of `i` at a time. -/
private def brv : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, i => 2 * brv m i + i / 2 ^ m % 2

private theorem brv_succ (m i : ℕ) : brv (m + 1) i = 2 * brv m i + i / 2 ^ m % 2 := rfl

private theorem bitRevN_eq (logn i : ℕ) : bitRevN logn i = brv logn i := by
  have key : ∀ m j, j + m ≤ logn →
      List.foldl (fun b a => (b.1 ||| (b.2 &&& 1) <<< (logn - 1 - a), b.2 >>> 1))
        (brv j i * 2 ^ (logn - j), i / 2 ^ j) (List.range' j m) =
      (brv (j + m) i * 2 ^ (logn - (j + m)), i / 2 ^ (j + m)) := by
    intro m
    induction m with
    | zero => intro j _; rfl
    | succ m ih =>
      intro j hj
      have hb : i / 2 ^ j % 2 * 2 ^ (logn - 1 - j) < 2 ^ (logn - 1 - j + 1) := by
        have h2 := Nat.two_pow_pos (logn - 1 - j)
        have h1 : i / 2 ^ j % 2 ≤ 1 := by omega
        rw [pow_succ]
        calc i / 2 ^ j % 2 * 2 ^ (logn - 1 - j) ≤ 1 * 2 ^ (logn - 1 - j) :=
              Nat.mul_le_mul_right _ h1
          _ < 2 ^ (logn - 1 - j) * 2 := by omega
      have hstep : (brv j i * 2 ^ (logn - j) ||| (i / 2 ^ j &&& 1) <<< (logn - 1 - j),
          (i / 2 ^ j) >>> 1) = (brv (j + 1) i * 2 ^ (logn - (j + 1)), i / 2 ^ (j + 1)) := by
        rw [Nat.and_one_is_mod, Nat.shiftLeft_eq, show logn - j = logn - 1 - j + 1 by omega,
          show logn - (j + 1) = logn - 1 - j by omega, ← Nat.shiftLeft_eq (brv j i),
          ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, brv_succ, pow_succ,
          Nat.shiftRight_eq_div_pow, pow_one, Nat.div_div_eq_div_mul, ← pow_succ]
        congr 1
        ring
      simp only [List.range'_succ, List.foldl_cons]
      rw [hstep, ih (j + 1) (by omega), show j + 1 + m = j + (m + 1) by omega]
  have h := key logn 0 (by omega)
  rw [show brv 0 i = 0 from rfl, zero_mul, pow_zero, Nat.div_one, Nat.zero_add, Nat.sub_self,
    pow_zero, mul_one] at h
  unfold bitRevN
  simp only [Id.run, forIn_range_pure, pure_bind, Nat.sub_zero]
  rw [h]
  rfl

private theorem brv_add_two_pow_mul (s x q : ℕ) : brv s (x + 2 ^ s * q) = brv s x := by
  induction s generalizing q with
  | zero => rfl
  | succ s ih =>
    rw [brv_succ, brv_succ, show x + 2 ^ (s + 1) * q = x + 2 ^ s * (2 * q) by ring, ih,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.add_mul_mod_self_left]

private theorem brv_two_mul_add (s g b : ℕ) (hb : b < 2) :
    brv (s + 1) (2 * g + b) = b * 2 ^ s + brv s g := by
  induction s with
  | zero => simp only [brv]; omega
  | succ s ih =>
    rw [brv_succ, ih, brv_succ s g, show (2 * g + b) / 2 ^ (s + 1) = g / 2 ^ s by
      rw [pow_succ', ← Nat.div_div_eq_div_mul]; congr 1; omega]
    ring

private theorem brv_pad (s m x : ℕ) (hx : x < 2 ^ s) : brv (s + m) x = 2 ^ m * brv s x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, brv_succ, ih, Nat.div_eq_of_lt (lt_of_lt_of_le hx
      (Nat.pow_le_pow_right two_pos (Nat.le_add_right s m)))]
    ring

private theorem brv_two_pow_add (s m g : ℕ) (hg : g < 2 ^ s) :
    brv (s + 1 + m) (2 ^ s + g) = 2 ^ m * (2 * brv s g + 1) := by
  have hP := Nat.two_pow_pos s
  rw [brv_pad (s + 1) m _ (by rw [pow_succ]; omega), brv_succ,
    show 2 ^ s + g = g + 2 ^ s * 1 by ring, brv_add_two_pow_mul,
    Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hg]

private theorem brv_compl (s g : ℕ) (hg : g < 2 ^ s) :
    brv s g + brv s (2 ^ s - 1 - g) = 2 ^ s - 1 := by
  induction s generalizing g with
  | zero => simp [brv]
  | succ s ih =>
    obtain ⟨g, b, hb, rfl⟩ : ∃ g' b, b < 2 ∧ g = 2 * g' + b :=
      ⟨g / 2, g % 2, Nat.mod_lt _ two_pos, (Nat.div_add_mod g 2).symm⟩
    have hP := Nat.two_pow_pos s
    rw [pow_succ] at hg
    have e : 2 ^ (s + 1) - 1 - (2 * g + b) = 2 * (2 ^ s - 1 - g) + (1 - b) := by
      rw [pow_succ]; omega
    rw [e, brv_two_mul_add _ _ _ hb, brv_two_mul_add _ _ _ (by omega)]
    have := ih g (by omega)
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp only [pow_succ] <;> omega

private theorem brv_partner (s m g : ℕ) (hg : g < 2 ^ s) :
    brv (s + 1 + m) (2 ^ s + g) + brv (s + 1 + m) (2 ^ (s + 1) - 1 - g) = 2 ^ (s + 1 + m) := by
  have hP := Nat.two_pow_pos s
  have hc := brv_compl s g hg
  rw [show 2 ^ (s + 1) - 1 - g = 2 ^ s + (2 ^ s - 1 - g) by rw [pow_succ]; omega,
    brv_two_pow_add s m g hg, brv_two_pow_add s m _ (by omega), ← mul_add,
    show 2 * brv s g + 1 + (2 * brv s (2 ^ s - 1 - g) + 1) = 2 ^ (s + 1) by
      rw [pow_succ]; omega]
  ring

/-! ### Twiddles -/

private theorem zetaTable_getD {logn i : ℕ} (hi : i < 2 ^ logn) :
    (zetaTable logn).getD i 0 = primitiveRoot2N logn ^ brv logn i := by
  simp [zetaTable, hi, bitRevN_eq]

private theorem two_pow_mul_two_pow_sub {logn : ℕ} (hlogn : logn ≤ 11) :
    2 ^ logn * 2 ^ (11 - logn) = 2048 := by
  rw [← pow_add, Nat.add_sub_cancel' hlogn]
  rfl

/-- `ζ^n = -1`: the twiddle root has order `2n` for `n = 2^logn ≤ 2048`. -/
private theorem primitiveRoot2N_pow_two_pow {logn : ℕ} (hlogn : logn ≤ 11) :
    primitiveRoot2N logn ^ 2 ^ logn = -1 := by
  have h := two_pow_mul_two_pow_sub hlogn
  have e : (modulus - 1) / (2 * 2 ^ logn) * 2 ^ logn = 6144 := by
    rw [show modulus - 1 = 2 * 2 ^ logn * (3 * 2 ^ (11 - logn)) by
        rw [show 2 * 2 ^ logn * (3 * 2 ^ (11 - logn)) = 6 * (2 ^ logn * 2 ^ (11 - logn)) by ring,
          h]; rfl,
      Nat.mul_div_cancel_left _ (by positivity),
      show 3 * 2 ^ (11 - logn) * 2 ^ logn = 3 * (2 ^ logn * 2 ^ (11 - logn)) by ring, h]
  rw [primitiveRoot2N, ← pow_mul, e, show (6144 : ℕ) = 6 * 1024 from rfl, pow_mul]
  exact (by reduce_mod_char : ((11 : ZMod 12289) ^ 6) ^ 1024 = -1)

private theorem twiddle_index_lt {logn : ℕ} (s : Fin logn) (g : Fin (2 ^ s.val)) :
    2 ^ s.val + g.val < 2 ^ logn ∧ 2 ^ (s.val + 1) - 1 - g.val < 2 ^ logn := by
  have h : 2 ^ (s.val + 1) ≤ 2 ^ logn := Nat.pow_le_pow_right two_pos s.isLt
  have := g.isLt
  rw [pow_succ] at h
  omega

/-- The `s`-layer forward twiddle of group `g` and the inverse twiddle the inverse loop reads
for it multiply to `1`. -/
private theorem twiddle_partner {logn : ℕ} (hlogn : logn ≤ 11) (s : Fin logn)
    (g : Fin (2 ^ s.val)) :
    -(zetaTable logn).getD (2 ^ (s.val + 1) - 1 - g.val) 0 *
        (zetaTable logn).getD (2 ^ s.val + g.val) 0 = 1 := by
  obtain ⟨h1, h2⟩ := twiddle_index_lt s g
  have e := brv_partner s.val (logn - 1 - s.val) g.val g.isLt
  rw [show s.val + 1 + (logn - 1 - s.val) = logn by omega] at e
  rw [zetaTable_getD h1, zetaTable_getD h2, neg_mul, ← pow_add, add_comm, e,
    primitiveRoot2N_pow_two_pow hlogn, neg_neg]

/-! ### Stages -/

/-- Layer `s` of the transform: `2^s` blocks of `2^(logn - s)` coefficients, with the forward
twiddles `zetaTable[2^s + g]` and the inverse twiddles `-zetaTable[2^(s+1) - 1 - g]` of the
loops. -/
private def nttStage (logn : ℕ) (hlogn : logn ≤ 11) (s : Fin logn) :
    ScaledStage Coeff (Fin (2 ^ logn)) :=
  ctStage le_rfl rfl (fun k => (zetaTable logn).getD k 0) (twiddle_partner hlogn) s

private def nttCoeffs (logn : ℕ) (hlogn : logn ≤ 11) (input : Fin (2 ^ logn) → Coeff) :
    Fin (2 ^ logn) → Coeff :=
  forwardStages (List.ofFn (nttStage logn hlogn)) input

private def invNTTCoeffs (logn : ℕ) (hlogn : logn ≤ 11) (input : Fin (2 ^ logn) → Coeff) :
    Fin (2 ^ logn) → Coeff :=
  scaleCoeffs (nInv logn) (inverseStages (List.ofFn (nttStage logn hlogn)) input)

private theorem nInv_stageScalar {logn : ℕ} (hlogn : logn ≤ 11) :
    nInv logn * stageScalar (List.ofFn (nttStage logn hlogn)) = 1 := by
  rw [stageScalar_ofFn _ (c := 2) fun _ => rfl]
  have h := two_pow_mul_two_pow_sub hlogn
  have hd : (modulus - 1) / 2 ^ logn * 2 ^ logn = modulus - 1 := by
    rw [show modulus - 1 = 2 ^ logn * (6 * 2 ^ (11 - logn)) by
        rw [show 2 ^ logn * (6 * 2 ^ (11 - logn)) = 6 * (2 ^ logn * 2 ^ (11 - logn)) by ring,
          h]; rfl,
      Nat.mul_div_cancel_left _ (by positivity), mul_comm]
  have hle : (modulus - 1) / 2 ^ logn ≤ modulus := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  rw [nInv, Nat.cast_sub hle, ZMod.natCast_self, zero_sub, neg_mul,
    show (2 : Coeff) ^ logn = ((2 ^ logn : ℕ) : Coeff) by norm_cast, ← Nat.cast_mul, hd]
  decide

private theorem invNTTCoeffs_nttCoeffs {logn : ℕ} (hlogn : logn ≤ 11)
    (input : Fin (2 ^ logn) → Coeff) :
    invNTTCoeffs logn hlogn (nttCoeffs logn hlogn input) = input :=
  scale_inverseStages_forwardStages _ _ (nInv_stageScalar hlogn) input

/-! ### Evaluation points -/

/-- The `i`-th evaluation point `ζ^(2·brv(i) + 1)` of the Falcon NTT of degree `2^logn`. -/
def nttPoint (logn : ℕ) (i : Fin (2 ^ logn)) : Coeff :=
  primitiveRoot2N logn ^ (2 * bitRevN logn i.val + 1)

/-- Every evaluation point is a root of `X^n + 1`. -/
theorem nttPoint_pow_two_pow {logn : ℕ} (hlogn : logn ≤ 11) (i : Fin (2 ^ logn)) :
    nttPoint logn i ^ 2 ^ logn = -1 := by
  rw [nttPoint, ← pow_mul, mul_comm, pow_mul, primitiveRoot2N_pow_two_pow hlogn]
  exact Odd.neg_one_pow ⟨bitRevN logn i.val, rfl⟩

/-- The residue point of block `g` after `t` layers: block `g` of size `2^(logn - t)` is
congruent to the input modulo `X^(2^(logn - t)) − ctPoint logn t g`. -/
private def ctPoint (logn t g : ℕ) : Coeff :=
  primitiveRoot2N logn ^ (2 ^ (logn - t) * (2 * brv t g + 1))

private theorem zetaTable_getD_layer {logn : ℕ} (s : Fin logn) (g : Fin (2 ^ s.val)) :
    (zetaTable logn).getD (2 ^ s.val + g.val) 0 =
      primitiveRoot2N logn ^ (2 ^ (logn - 1 - s.val) * (2 * brv s.val g.val + 1)) := by
  rw [zetaTable_getD (twiddle_index_lt s g).1]
  have e := brv_two_pow_add s.val (logn - 1 - s.val) g.val g.isLt
  rw [show s.val + 1 + (logn - 1 - s.val) = logn by omega] at e
  rw [e]

private theorem ctPoint_sq {logn : ℕ} (s : Fin logn) (g : Fin (2 ^ s.val)) :
    (zetaTable logn).getD (2 ^ s.val + g.val) 0 ^ 2 = ctPoint logn s.val g.val := by
  rw [zetaTable_getD_layer, ← pow_mul, ctPoint,
    show logn - s.val = logn - 1 - s.val + 1 by omega, pow_succ]
  ring

private theorem ctPoint_left {logn : ℕ} (s : Fin logn) (g : Fin (2 ^ s.val)) :
    ctPoint logn (s.val + 1) (2 * g.val) = (zetaTable logn).getD (2 ^ s.val + g.val) 0 := by
  rw [zetaTable_getD_layer, ctPoint, show 2 * g.val = 2 * g.val + 0 from rfl,
    brv_two_mul_add _ _ _ two_pos, show logn - (s.val + 1) = logn - 1 - s.val by omega]
  ring

private theorem ctPoint_right {logn : ℕ} (hlogn : logn ≤ 11) (s : Fin logn)
    (g : Fin (2 ^ s.val)) :
    ctPoint logn (s.val + 1) (2 * g.val + 1) =
      -(zetaTable logn).getD (2 ^ s.val + g.val) 0 := by
  rw [zetaTable_getD_layer, ctPoint, brv_two_mul_add _ _ _ one_lt_two,
    show logn - (s.val + 1) = logn - 1 - s.val by omega,
    show 2 ^ (logn - 1 - s.val) * (2 * (1 * 2 ^ s.val + brv s.val g.val) + 1) =
      2 ^ logn + 2 ^ (logn - 1 - s.val) * (2 * brv s.val g.val + 1) by
        rw [← ctLayer_shape logn s]; ring,
    pow_add, primitiveRoot2N_pow_two_pow hlogn, neg_one_mul]

private theorem ctPoint_last {logn : ℕ} (i : Fin (2 ^ logn)) :
    ctPoint logn logn i.val = nttPoint logn i := by
  rw [ctPoint, nttPoint, Nat.sub_self, pow_zero, one_mul, bitRevN_eq]

/-! ### Loops -/

private theorem butterflyNTT_loops (logn : ℕ) (f : Rq (2 ^ logn)) :
    butterflyNTT logn f = ⟨Vector.ofFn fun i =>
      (Id.run (forIn Lean.Loop.mk (f.toArray, 1, 2 ^ logn / 2)
        (ctForwardBody (2 ^ logn) fun k => (zetaTable logn).getD k 0))).1.getD i 0⟩ :=
  rfl

private theorem butterflyInvNTT_loops (logn : ℕ) (fHat : Tq (2 ^ logn)) :
    butterflyInvNTT logn fHat = Vector.ofFn fun i => (Id.run (forIn [0 : 2 ^ logn]
      (Id.run (forIn Lean.Loop.mk (fHat.coeffs.toArray, 2 ^ logn - 1, 1)
        (ctInverseBody (2 ^ logn) fun k => (zetaTable logn).getD k 0))).1
      fun j b => pure (.yield (b.set! j (nInv logn * b.getD j 0))))).getD i 0 :=
  rfl

/-! ### Transform laws -/

private theorem ntt_eq {logn : ℕ} (hlogn : logn ≤ 11) (f : Rq (2 ^ logn)) :
    ntt logn f = ⟨applyCoeffTransform (polyBackend (2 ^ logn)) (nttCoeffs logn hlogn) f⟩ := by
  rw [ntt, butterflyNTT_loops,
    ctForward_loop rfl _ (twiddle_partner hlogn) (vector_toArray_eq_ofFn f)]
  simp only [getD_ofFn_eq_coeffAt, coeffAt_fin]
  rfl

private theorem invNTT_eq {logn : ℕ} (hlogn : logn ≤ 11) (fHat : Tq (2 ^ logn)) :
    invNTT logn fHat =
      applyCoeffTransform (polyBackend (2 ^ logn)) (invNTTCoeffs logn hlogn) fHat.coeffs := by
  rw [invNTT, butterflyInvNTT_loops,
    ctInverse_loop rfl _ (twiddle_partner hlogn) (vector_toArray_eq_ofFn fHat.coeffs), scale_loop]
  simp only [getD_ofFn_eq_coeffAt, coeffAt_fin]
  rfl

/-- `invNTT` is a left inverse of `ntt`. -/
theorem invNTT_ntt {logn : ℕ} (hlogn : logn ≤ 11) (f : Rq (2 ^ logn)) :
    invNTT logn (ntt logn f) = f := by
  rw [invNTT_eq hlogn, ntt_eq hlogn]
  exact applyCoeffTransform_comp _ _ (invNTTCoeffs_nttCoeffs hlogn) f

private def rqEquivCoeffFun (n : ℕ) : Rq n ≃ (Fin n → Coeff) where
  toFun f i := f.get i
  invFun f := Vector.ofFn f
  left_inv f := by
    apply Vector.ext
    intro i hi
    exact Vector.getElem_ofFn (f := fun i => f.get i) hi
  right_inv f := by
    funext i
    exact Vector.get_ofFn f i

private def rqEquivTq (n : ℕ) : Rq n ≃ Tq n where
  toFun f := ⟨f⟩
  invFun fHat := fHat.coeffs
  left_inv _ := rfl
  right_inv fHat := by cases fHat; rfl

private theorem ntt_injective {logn : ℕ} (hlogn : logn ≤ 11) :
    Function.Injective (ntt logn) := by
  intro f g h
  have hInv := congrArg (invNTT logn) h
  rwa [invNTT_ntt hlogn, invNTT_ntt hlogn] at hInv

private theorem ntt_surjective {logn : ℕ} (hlogn : logn ≤ 11) :
    Function.Surjective (ntt logn) := by
  let : Fintype Coeff := ZMod.fintype modulus
  let : Finite (Rq (2 ^ logn)) := Finite.of_equiv _ (rqEquivCoeffFun (2 ^ logn)).symm
  exact (ntt_injective hlogn).surjective_of_finite (rqEquivTq (2 ^ logn))

/-- `ntt` is a left inverse of `invNTT`. -/
theorem ntt_invNTT {logn : ℕ} (hlogn : logn ≤ 11) (fHat : Tq (2 ^ logn)) :
    ntt logn (invNTT logn fHat) = fHat := by
  obtain ⟨f, rfl⟩ := ntt_surjective hlogn fHat
  rw [invNTT_ntt hlogn]

private theorem hadd_rq {n : ℕ} (f g : Rq n) :
    (polyBackend n).coeff (f + g) = (polyBackend n).coeff f + (polyBackend n).coeff g := by
  funext i
  change ((vectorNegacyclicRing Coeff n).add f g).get i = f.get i + g.get i
  simp

private theorem hsub_rq {n : ℕ} (f g : Rq n) :
    (polyBackend n).coeff (f - g) = (polyBackend n).coeff f - (polyBackend n).coeff g := by
  funext i
  change ((vectorNegacyclicRing Coeff n).sub f g).get i = f.get i - g.get i
  simp

private theorem hzero_rq {n : ℕ} : (polyBackend n).coeff (0 : Rq n) = 0 := by
  funext i
  exact vectorRing_zero_get i

/-- `ntt` is additive. -/
theorem ntt_add {logn : ℕ} (hlogn : logn ≤ 11) (f g : Rq (2 ^ logn)) :
    ntt logn (f + g) = ntt logn f + ntt logn g := by
  apply TransformPoly.ext
  change (ntt logn (f + g)).coeffs = (ntt logn f).coeffs + (ntt logn g).coeffs
  rw [ntt_eq hlogn, ntt_eq hlogn, ntt_eq hlogn]
  exact applyCoeffTransform_add _ hadd_rq (forwardStages_add _) f g

/-- `ntt` preserves subtraction. -/
theorem ntt_sub {logn : ℕ} (hlogn : logn ≤ 11) (f g : Rq (2 ^ logn)) :
    ntt logn (f - g) = ntt logn f - ntt logn g := by
  apply TransformPoly.ext
  change (ntt logn (f - g)).coeffs = (ntt logn f).coeffs - (ntt logn g).coeffs
  rw [ntt_eq hlogn, ntt_eq hlogn, ntt_eq hlogn]
  exact applyCoeffTransform_sub _ hsub_rq (forwardStages_sub _) f g

/-- `ntt` preserves zero. -/
theorem ntt_zero {logn : ℕ} (hlogn : logn ≤ 11) : ntt logn 0 = 0 := by
  apply TransformPoly.ext
  rw [ntt_eq hlogn]
  exact applyCoeffTransform_zero _ hzero_rq (forwardStages_zero _)

/-- Entry `i` of `ntt logn f` is the evaluation of `f` at `nttPoint logn i = ζ^(2·brv(i) + 1)`. -/
theorem ntt_coeff_eq_eval {logn : ℕ} (hlogn : logn ≤ 11) (f : Rq (2 ^ logn))
    (i : Fin (2 ^ logn)) :
    (polyBackend (2 ^ logn)).coeff (ntt logn f).coeffs i =
      ((polyBackend (2 ^ logn)).toPolynomial f).eval (nttPoint logn i) := by
  have h := forwardStages_ofFn_dvd (N := (polyBackend (2 ^ logn)).degree) (k := logn)
    (fun s => 2 ^ (logn - 1 - s.val)) (ctLayer_shape logn)
    (fun s g => (zetaTable logn).getD (2 ^ s.val + g.val) 0) (ctPoint logn) ctPoint_sq
    ctPoint_left (ctPoint_right hlogn) (nttStage logn hlogn) (fun _ => rfl)
    ((polyBackend (2 ^ logn)).coeff f) i.val i.isLt
  have hN : (polyBackend (2 ^ logn)).degree / 2 ^ logn = 1 := Nat.div_self (Nat.two_pow_pos _)
  rw [hN, pow_one, mul_one, blockPoly_zero_eq_toPolynomial, blockPoly_one (i := i),
    ctPoint_last, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_sub,
    Polynomial.eval_C, sub_eq_zero] at h
  rw [← h, ntt_eq hlogn, applyCoeffTransform, PolyBackend.coeff_build_apply, nttCoeffs]

/-- The `n` evaluation points are distinct. -/
theorem nttPoint_injective {logn : ℕ} (hlogn : logn ≤ 11) :
    Function.Injective (nttPoint logn) := by
  intro i j hij
  by_contra hne
  have h := ntt_coeff_eq_eval hlogn
    (invNTT logn ⟨(polyBackend (2 ^ logn)).build fun k => if k = i then 1 else 0⟩)
  rw [ntt_invNTT hlogn] at h
  have hi := h i
  rw [hij, ← h j, PolyBackend.coeff_build_apply, PolyBackend.coeff_build_apply,
    ite_eq_left rfl, ite_eq_right (Ne.symm hne)] at hi
  exact absurd hi (by decide)

/-- Coordinate `i` of `multiplyNTTs fHat gHat` is `fHat i * gHat i`. -/
theorem coeff_multiplyNTTs {n : ℕ} (fHat gHat : Tq n) (i : Fin n) :
    (polyBackend n).coeff (multiplyNTTs fHat gHat).coeffs i =
      (polyBackend n).coeff fHat.coeffs i * (polyBackend n).coeff gHat.coeffs i := by
  change (Vector.ofFn fun j : Fin n => fHat[j.val] * gHat[j.val]).get i = _
  rw [Vector.get_ofFn]
  rfl

/-- `ntt` turns negacyclic multiplication into the pointwise product. -/
theorem ntt_negacyclicMul {logn : ℕ} (hlogn : logn ≤ 11) (f g : Rq (2 ^ logn)) :
    ntt logn (negacyclicMul f g) = multiplyNTTs (ntt logn f) (ntt logn g) := by
  apply TransformPoly.ext
  refine PolyBackend.ext_coeff (backend := polyBackend (2 ^ logn)) fun i => ?_
  have hmul : negacyclicMul f g = negacyclicMulPure (vectorKernel Coeff (2 ^ logn)) f g := rfl
  rw [coeff_multiplyNTTs, ntt_coeff_eq_eval hlogn, ntt_coeff_eq_eval hlogn,
    ntt_coeff_eq_eval hlogn, ← Polynomial.eval_mul, hmul, ← sub_eq_zero, ← Polynomial.eval_sub]
  have h1 := X_pow_sub_C_dvd_X_pow_mul_add_one (B := 1) (nttPoint_pow_two_pow hlogn i)
  rw [one_mul] at h1
  obtain ⟨q, hq⟩ := h1.trans (negacyclicModulus_dvd_toPolynomial_negacyclicMulPure
    (polyBackend (2 ^ logn)) (vectorKernel Coeff (2 ^ logn)) f g)
  rw [hq, Polynomial.eval_mul, Polynomial.eval_sub, pow_one, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_mul]

/-- The pointwise product is negacyclic multiplication transported through the NTT. -/
theorem multiplyNTTs_eq_ntt_negacyclicMul_invNTT {logn : ℕ} (hlogn : logn ≤ 11)
    (fHat gHat : Tq (2 ^ logn)) :
    multiplyNTTs fHat gHat = ntt logn (negacyclicMul (invNTT logn fHat) (invNTT logn gHat)) := by
  rw [ntt_negacyclicMul hlogn, ntt_invNTT hlogn, ntt_invNTT hlogn]

private theorem coeff_coeffs_add {n : ℕ} (fHat gHat : Tq n) (i : Fin n) :
    (polyBackend n).coeff (fHat + gHat).coeffs i =
      (polyBackend n).coeff fHat.coeffs i + (polyBackend n).coeff gHat.coeffs i :=
  congrFun (hadd_rq fHat.coeffs gHat.coeffs) i

private theorem coeff_coeffs_sub {n : ℕ} (fHat gHat : Tq n) (i : Fin n) :
    (polyBackend n).coeff (fHat - gHat).coeffs i =
      (polyBackend n).coeff fHat.coeffs i - (polyBackend n).coeff gHat.coeffs i :=
  congrFun (hsub_rq fHat.coeffs gHat.coeffs) i

/-- The transform laws of the concrete Falcon NTT for `n = 2^logn ≤ 2048`. -/
theorem concreteNTTRingLaws (logn : ℕ) (hlogn : logn ≤ 11) :
    NTTRingLaws (concreteNTTRingOps logn) where
  fromHat_toHat := invNTT_ntt hlogn
  toHat_fromHat := ntt_invNTT hlogn
  toHat_zero := ntt_zero hlogn
  toHat_mul f g := ntt_negacyclicMul hlogn f g
  toHat_add f g := ntt_add hlogn f g
  toHat_sub f g := ntt_sub hlogn f g
  mul_add f g h := by
    change multiplyNTTs f (g + h) = multiplyNTTs f g + multiplyNTTs f h
    apply TransformPoly.ext
    refine PolyBackend.ext_coeff (backend := polyBackend (2 ^ logn)) fun i => ?_
    simp only [coeff_coeffs_add, coeff_multiplyNTTs, mul_add]
  mul_sub f g h := by
    change multiplyNTTs f (g - h) = multiplyNTTs f g - multiplyNTTs f h
    apply TransformPoly.ext
    refine PolyBackend.ext_coeff (backend := polyBackend (2 ^ logn)) fun i => ?_
    simp only [coeff_coeffs_sub, coeff_multiplyNTTs, mul_sub]
  mul_comm f g := by
    change multiplyNTTs f g = multiplyNTTs g f
    apply TransformPoly.ext
    refine PolyBackend.ext_coeff (backend := polyBackend (2 ^ logn)) fun i => ?_
    rw [coeff_multiplyNTTs, coeff_multiplyNTTs, mul_comm]
  mul_assoc f g h := by
    change multiplyNTTs (multiplyNTTs f g) h = multiplyNTTs f (multiplyNTTs g h)
    apply TransformPoly.ext
    refine PolyBackend.ext_coeff (backend := polyBackend (2 ^ logn)) fun i => ?_
    simp only [coeff_multiplyNTTs, mul_assoc]

end Falcon.Concrete
