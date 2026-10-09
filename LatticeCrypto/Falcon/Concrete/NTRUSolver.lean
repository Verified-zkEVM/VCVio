/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.Falcon.Concrete.BigInt31
public import LatticeCrypto.Falcon.Concrete.FXR
public import LatticeCrypto.Falcon.Concrete.PolyBigInt
public import LatticeCrypto.Falcon.Concrete.SmallPrimeNTT

/-!
# NTRU Equation Solver for Falcon Key Generation

Port of the NTRU equation solver from Pornin's `c-fn-dsa/kgen_ntru.c`.

Given short polynomials `f, g ∈ ℤ[x]/(x^n + 1)`, the NTRU equation solver
finds short polynomials `F, G` satisfying `fG - gF = q` where `q = 12289`.

## Algorithm Overview

1. **Descent**: Compute field norms `N(f), N(g)` recursively to reduce
   the polynomial degree from `n = 2^logn` down to 1 (scalar).
2. **Base case**: Solve `f₀ · G₀ - g₀ · F₀ = q` via extended binary GCD.
3. **Ascent**: Lift `(F, G)` through each level using NTT-based polynomial
   multiplication, then apply Babai's nearest-plane reduction.

## Representation

- Big integers use 31-bit limbs in multi-word interleaved format (stride `n`).
- Small-prime RNS + NTT for fast polynomial multiplication.
- Fixed-point 32.32 arithmetic (FXR) for the Babai rounding step.

## References

- Pornin 2025, eprint 2025/1239
- `c-fn-dsa/kgen_ntru.c`, `c-fn-dsa/kgen_inner.h`
-/

public section


namespace Falcon.Concrete.NTRUSolver

open Falcon.Concrete.FXR

/-! ## Constants -/

/-- The Falcon modulus `q = 12289`. -/
def Q : UInt32 := 12289

/-- Maximum big-integer word count for `(f, g)` at each depth. -/
def MAX_BL_SMALL : Array Nat := #[1, 1, 2, 3, 4, 8, 14, 27, 53, 104, 207]

/-- Maximum big-integer word count for unreduced `(F, G)` at each depth. -/
def MAX_BL_LARGE : Array Nat := #[1, 2, 3, 6, 11, 21, 40, 78, 155, 308]

/-- Number of top words used for fixed-point approximation at each depth. -/
def WORD_WIN : Array Nat := #[1, 1, 2, 2, 2, 3, 3, 4, 5, 7]

/-- Minimum depth at which intermediate `(f, g)` are saved during descent. -/
def MIN_SAVE_FG : Array Nat := #[0, 0, 1, 2, 2, 2, 2, 2, 2, 3, 3]

/-! ## Helper types and conversions -/

/-- Convert from `SmallPrimeNTT.SmallPrime` to `BigInt31.SmallPrime`
(dropping the `g` and `ig` fields which are only needed for NTT). -/
@[inline] def toBigInt31Prime (sp : SmallPrimeNTT.SmallPrime) :
    BigInt31.SmallPrime :=
  ⟨sp.p, sp.p0i, sp.R2, sp.s⟩

/-- The PRIMES table converted to `BigInt31.SmallPrime` format
(used by CRT reconstruction). -/
def PRIMES_BI : Array BigInt31.SmallPrime :=
  SmallPrimeNTT.PRIMES.map toBigInt31Prime

/-! ## Buffer manipulation helpers -/

@[inline] private def getU32 (arr : Array UInt32) (i : Nat) : UInt32 :=
  arr.getD i 0

/-- Extract `len` words from `arr` starting at offset `off`. -/
private def extractRange (arr : Array UInt32) (off len : Nat) : Array UInt32 :=
  arr.extract off (off + len)

/-- Overwrite `src.size` words into `arr` starting at offset `off`. -/
private def writeRange (arr : Array UInt32) (off : Nat) (src : Array UInt32) :
    Array UInt32 := Id.run do
  let mut arr := arr
  for i in [:src.size] do
    if off + i < arr.size then
      arr := arr.set! (off + i) (src.getD i 0)
  return arr

/-- Ensure array has at least `sz` elements, zero-extending if needed. -/
private def ensureSize (arr : Array UInt32) (sz : Nat) : Array UInt32 :=
  if arr.size >= sz then arr
  else arr ++ Array.replicate (sz - arr.size) (0 : UInt32)

/-- Construct inverse-NTT twiddle factors for prime `pr` at degree `2^logn`.
Uses `mp_mkgmigm` and returns only the `igm` component. -/
private def mkigm (logn : Nat) (pr : SmallPrimeNTT.SmallPrime) : Array UInt32 :=
  (SmallPrimeNTT.mp_mkgmigm logn pr.g pr.ig pr.p pr.p0i).2

/-- Reduce a big integer modulo a small prime using signed convention.
Port of the inline `zint_mod_small_signed` from `kgen_inner.h`.
The big integer has `len` limbs starting at `offset` with stride `stride`.
`Rx = 2^(31*len) mod p`. -/
private def zint_mod_small_signed (d : Array UInt32) (len : Nat)
    (offset stride : Nat) (p p0i R2 Rx : UInt32) : UInt32 :=
  if len == 0 then 0
  else
    let z := BigInt31.zint_mod_small_unsigned d len offset stride p p0i R2
    let topWord := BigInt31.getLimb d offset stride (len - 1)
    SmallPrimeNTT.mp_sub z (Rx &&& (0 - (topWord >>> (30 : UInt32)))) p

/-! ## make_fg_zero

Convert source `f` and `g` into RNS+NTT (one word per coefficient) using
the first small prime. Returns `ft ++ gt` (each `n = 2^logn` words). -/

def make_fg_zero (logn : Nat) (f g : Array Int8) : Array UInt32 :=
  let pr := SmallPrimeNTT.PRIMES.getD 0 default
  let p := pr.p
  let p0i := pr.p0i
  let gm := SmallPrimeNTT.mp_mkgm logn pr.g p p0i
  let ft := SmallPrimeNTT.mp_NTT logn
    (SmallPrimeNTT.mp_set_small logn f p) gm p p0i
  let gt := SmallPrimeNTT.mp_NTT logn
    (SmallPrimeNTT.mp_set_small logn g p) gm p p0i
  ft ++ gt

/-! ## make_fg_step

One step of field-norm computation. Given `(f, g)` at depth `d` with degree
`n = 2^(logn_top - d)` and `slen = MAX_BL_SMALL[d]` RNS words per coefficient,
compute `(f', g')` at depth `d + 1` with degree `n/2` and
`tlen = MAX_BL_SMALL[d + 1]` words.

In NTT representation, the field norm satisfies:
  `N(f)[j] = f[2j] · f[2j+1] · R²` (Montgomery form)

**Phase 1** (primes `0..slen-1`): compute norms from existing NTT data,
then inverse-NTT the source to recover `(f, g)` in RNS (non-NTT).

**Phase 2**: CRT-reconstruct `(f, g)` from RNS to plain integers.

**Phase 3** (primes `slen..tlen-1`): reduce plain-integer coefficients
modulo each new prime, forward-NTT, compute norms. -/

def make_fg_step (logn_top depth : Nat) (buf : Array UInt32) :
    Array UInt32 := Id.run do
  let logn := logn_top - depth
  let n := 1 <<< logn
  let hn := n >>> 1
  let slen := MAX_BL_SMALL.getD depth 1
  let tlen := MAX_BL_SMALL.getD (depth + 1) 1

  let mut fs := extractRange buf 0 (n * slen)
  let mut gs := extractRange buf (n * slen) (n * slen)
  let mut fd : Array UInt32 := Array.replicate (hn * tlen) 0
  let mut gd : Array UInt32 := Array.replicate (hn * tlen) 0

  -- Phase 1: first slen primes — compute norms from NTT, then iNTT source
  for i in [:slen] do
    let pr := SmallPrimeNTT.PRIMES.getD i default
    let p := pr.p
    let p0i := pr.p0i
    let r2 := pr.R2

    for j in [:hn] do
      let xf0 := getU32 fs (i * n + 2 * j)
      let xf1 := getU32 fs (i * n + 2 * j + 1)
      let xg0 := getU32 gs (i * n + 2 * j)
      let xg1 := getU32 gs (i * n + 2 * j + 1)
      fd := fd.set! (i * hn + j)
        (SmallPrimeNTT.mp_montymul
          (SmallPrimeNTT.mp_montymul xf0 xf1 p p0i) r2 p p0i)
      gd := gd.set! (i * hn + j)
        (SmallPrimeNTT.mp_montymul
          (SmallPrimeNTT.mp_montymul xg0 xg1 p p0i) r2 p p0i)

    let igm := mkigm logn pr
    let fSlice := SmallPrimeNTT.mp_iNTT logn
      (extractRange fs (i * n) n) igm p p0i
    fs := writeRange fs (i * n) fSlice
    let gSlice := SmallPrimeNTT.mp_iNTT logn
      (extractRange gs (i * n) n) igm p p0i
    gs := writeRange gs (i * n) gSlice

  -- Phase 2: CRT-reconstruct source (f, g) → plain signed integers
  let combined := fs ++ gs
  let crtTmp := Array.replicate slen (0 : UInt32)
  let (combined', _) :=
    BigInt31.zint_rebuild_CRT combined slen n 2 PRIMES_BI true crtTmp
  fs := extractRange combined' 0 (n * slen)
  gs := extractRange combined' (n * slen) (n * slen)

  -- Phase 3: primes slen..tlen-1 — reduce, NTT, compute norms
  for i in [slen:tlen] do
    let pr := SmallPrimeNTT.PRIMES.getD i default
    let p := pr.p
    let p0i := pr.p0i
    let r2 := pr.R2
    let rx := SmallPrimeNTT.mp_Rx31 slen p p0i r2
    let gm := SmallPrimeNTT.mp_mkgm logn pr.g p p0i

    let mut t2 : Array UInt32 := Array.replicate n 0
    for j in [:n] do
      t2 := t2.set! j (zint_mod_small_signed fs slen j n p p0i r2 rx)
    t2 := SmallPrimeNTT.mp_NTT logn t2 gm p p0i
    for j in [:hn] do
      fd := fd.set! (i * hn + j)
        (SmallPrimeNTT.mp_montymul
          (SmallPrimeNTT.mp_montymul (getU32 t2 (2 * j))
            (getU32 t2 (2 * j + 1)) p p0i) r2 p p0i)

    for j in [:n] do
      t2 := t2.set! j (zint_mod_small_signed gs slen j n p p0i r2 rx)
    t2 := SmallPrimeNTT.mp_NTT logn t2 gm p p0i
    for j in [:hn] do
      gd := gd.set! (i * hn + j)
        (SmallPrimeNTT.mp_montymul
          (SmallPrimeNTT.mp_montymul (getU32 t2 (2 * j))
            (getU32 t2 (2 * j + 1)) p p0i) r2 p p0i)

  return fd ++ gd

/-! ## make_fg_intermediate

Compute `(f, g)` at a specified depth by starting from the original
polynomials and applying `depth` field-norm steps. -/

def make_fg_intermediate (logn_top : Nat) (f g : Array Int8)
    (depth : Nat) : Array UInt32 := Id.run do
  let mut buf := make_fg_zero logn_top f g
  for d in [:depth] do
    buf := make_fg_step logn_top d buf
  return buf

/-! ## make_fg_deepest

Compute `(f, g)` at the deepest level (degree 1 = resultants). Also checks
that `f` is invertible modulo the first prime (all NTT coefficients nonzero).
Intermediate `(f, g)` values above the save threshold are stored near the
end of the 6n-word buffer for reuse during the lifting phase.

Returns `(buffer, f_is_invertible)`. -/

def make_fg_deepest (logn_top : Nat) (f g : Array Int8) :
    Array UInt32 × Bool := Id.run do
  let n := 1 <<< logn_top
  let bufSize := 6 * n
  let mut buf := ensureSize (make_fg_zero logn_top f g) bufSize

  -- Invertibility: all NTT coefficients of f must be nonzero (mod p₀)
  let mut b : UInt32 := 0
  for i in [:n] do
    b := b ||| (getU32 buf i - 1)
  let invertible := (b >>> (31 : UInt32)) == 0

  -- Descend through all depths, saving intermediates for the ascent
  let mut savOff := bufSize
  for d in [:logn_top] do
    let result := make_fg_step logn_top d buf
    buf := writeRange buf 0 result
    let d2 := d + 1
    let minSave := MIN_SAVE_FG.getD logn_top 0
    if d2 < logn_top && d2 >= minSave then
      let slen := MAX_BL_SMALL.getD d2 1
      let fglen := slen <<< (logn_top + 1 - d2)
      savOff := savOff - fglen
      let saved := extractRange buf 0 fglen
      buf := writeRange buf savOff saved

  return (buf, invertible)

/-! ## solve_NTRU_deepest

Base case of the NTRU solver. The deepest level reduces to scalar integers:
the resultants `f₀ = Res(f, x^n + 1)` and `g₀ = Res(g, x^n + 1)`.

1. Compute resultants via iterated field norms (`make_fg_deepest`)
2. CRT-reconstruct from RNS to plain big integers
3. Extended binary GCD: `f₀ · G₀ - g₀ · F₀ = 1`
4. Scale: `F₀ ← q · F₀`, `G₀ ← q · G₀`

On success, `F₀` is at `buf[0..len)` and `G₀` at `buf[len..2·len)`. -/

def solve_NTRU_deepest (logn_top : Nat) (f g : Array Int8) :
    Option (Array UInt32) := Id.run do
  let (buf, ok) := make_fg_deepest logn_top f g
  if !ok then return none

  let len := MAX_BL_SMALL.getD logn_top 1

  -- Resultants are at buf[0..2*len) in RNS (n = 1, stride = 1, 2 sets)
  let combined := extractRange buf 0 (2 * len)
  let crtTmp := Array.replicate len (0 : UInt32)
  let (combined', _) :=
    BigInt31.zint_rebuild_CRT combined len 1 2 PRIMES_BI false crtTmp

  let fp := extractRange combined' 0 len
  let gp := extractRange combined' len len

  -- Extended GCD: fp · u - gp · v = 1 ⟹ u = G₀, v = F₀
  let (capG, capF, success) := BigInt31.zint_bezout fp gp len
  if success == 0 then return none

  -- Scale by q to get fp · G₀ - gp · F₀ = q
  let (capF, carryF) := BigInt31.zint_mul_small capF len Q
  if carryF != 0 then return none
  let (capG, carryG) := BigInt31.zint_mul_small capG len Q
  if carryG != 0 then return none

  -- Write F₀, G₀ into the buffer (preserving saved intermediates)
  let mut result := buf
  result := writeRange result 0 capF
  result := writeRange result len capG
  return some result

/-! ## solve_NTRU_intermediate

Lift `(F, G)` from depth `depth + 1` (degree `n/2`) to depth `depth`
(degree `n`).

Given `(F_deep, G_deep)` from the deeper level, compute `(F, G)` at this
level by:

1. **Retrieve (f, g)**: either from saved values in the buffer or by
   recomputing via `make_fg_intermediate`.

2. **Convert to RNS**: Reduce `(F_deep, G_deep)` modulo `llen` small
   primes.

3. **NTT lifting**: For each prime `pᵢ`, compute unreduced `(F, G)`:
   ```
   F[2j]   = g[2j+1] · F_deep[j]
   F[2j+1] = g[2j]   · F_deep[j]
   G[2j]   = f[2j+1] · G_deep[j]
   G[2j+1] = f[2j]   · G_deep[j]
   ```
   with Montgomery correction factors.

4. **CRT reconstruct**: Rebuild unreduced `(F, G)` as plain integers.

5. **Babai reduction** (iterative):
   ```
   k ← round((F·adj(f) + G·adj(g)) / (f·adj(f) + g·adj(g)))
   (F, G) ← (F - k·f, G - k·g)
   ```
   Uses fixed-point (FXR) FFT for the division step, and either
   `poly_sub_scaled` or `poly_sub_scaled_ntt` for the subtraction.
   Iterates until `|F|, |G|` are reduced to the size of `|f|, |g|`.

6. **Verification**: Check `f·G - g·F ≡ q (mod p₀)` in NTT form. -/

/-- Smallest degree exponent at which the Babai subtraction uses
`PolyBigInt.poly_sub_scaled_ntt` instead of the quadratic `PolyBigInt.poly_sub_scaled`
(at depths above 1). -/
private def minLognFgNtt : Nat := 4

/-- Offset, in the `6 · 2^logn_top`-word solver buffer, of the `(f, g)` pair saved by
`make_fg_deepest` for depth `depth` (valid when `MIN_SAVE_FG[logn_top] ≤ depth < logn_top`). -/
private def savedFGOffset (logn_top depth : Nat) : Nat := Id.run do
  let mut off := 6 <<< logn_top
  for d in [MIN_SAVE_FG.getD logn_top 0:depth + 1] do
    off := off - (MAX_BL_SMALL.getD d 1 <<< (logn_top + 1 - d))
  return off

/-- Reduce the `2^logn` signed big integers of `a` (`len` words each, stride `2^logn`)
modulo the small prime `pr`, and convert the result to NTT representation. -/
private def modPrimeNTT (logn : Nat) (a : Array UInt32) (len : Nat)
    (pr : SmallPrimeNTT.SmallPrime) (gm : Array UInt32) : Array UInt32 := Id.run do
  let n := 1 <<< logn
  let rx := SmallPrimeNTT.mp_Rx31 len pr.p pr.p0i pr.R2
  let mut t : Array UInt32 := Array.replicate n 0
  for j in [:n] do
    t := t.set! j (zint_mod_small_signed a len j n pr.p pr.p0i pr.R2 rx)
  return SmallPrimeNTT.mp_NTT logn t gm pr.p pr.p0i

/-- Convert the `2^logn` signed big integers of `a` (`len` words each) to RNS+NTT over the
first `len + 1` small primes (one line of `2^logn` words per prime). -/
private def toRNSNTTExtended (logn : Nat) (a : Array UInt32) (len : Nat) :
    Array UInt32 := Id.run do
  let mut out : Array UInt32 := #[]
  for i in [:len + 1] do
    let pr := SmallPrimeNTT.PRIMES.getD i default
    let gm := SmallPrimeNTT.mp_mkgm logn pr.g pr.p pr.p0i
    out := out ++ modPrimeNTT logn a len pr gm
  return out

/-- Number of bits by which one Babai iteration is assumed to shrink `(F, G)`. -/
private def reduceBits (logn_top : Nat) : UInt32 :=
  match logn_top with
  | 9 => 13
  | 10 => 11
  | _ => 16

/-- Lift `(F, G)` from depth `depth + 1` to depth `depth` of the NTRU solver (for
`1 ≤ depth < logn_top`). The deeper `(F, G)` are read from the start of `buf` (`dlen` words
per coefficient, degree `2^(logn_top - depth - 1)`); on success the new `(F, G)` are written
at the start of the returned buffer (`MAX_BL_SMALL[depth]` words per coefficient), and the
rest of the buffer (in particular the saved intermediate `(f, g)`) is left unchanged.
Returns `none` when the reduced solution fails the modular check of the NTRU equation. -/
def solve_NTRU_intermediate (logn_top : Nat) (f g : Array Int8)
    (depth : Nat) (buf : Array UInt32) : Option (Array UInt32) := Id.run do
  let logn := logn_top - depth
  let n := 1 <<< logn
  let hn := n >>> 1
  let slen := MAX_BL_SMALL.getD depth 1
  let llen := MAX_BL_LARGE.getD depth 1
  let dlen := MAX_BL_SMALL.getD (depth + 1) 1

  -- (F, G) from the deeper level
  let Fd := extractRange buf 0 (dlen * hn)
  let Gd := extractRange buf (dlen * hn) (dlen * hn)

  -- (f, g) at this level, in RNS+NTT (slen words per coefficient)
  let fgt :=
    if depth < MIN_SAVE_FG.getD logn_top 0 then
      extractRange (make_fg_intermediate logn_top f g depth) 0 (2 * slen * n)
    else
      extractRange buf (savedFGOffset logn_top depth) (2 * slen * n)
  let mut ft := extractRange fgt 0 (slen * n)
  let mut gt := extractRange fgt (slen * n) (slen * n)

  -- Deeper (F, G) in RNS, stored in the upper half of each n-word line.
  let mut Ft : Array UInt32 := Array.replicate (llen * n) 0
  let mut Gt : Array UInt32 := Array.replicate (llen * n) 0
  for i in [:llen] do
    let pr := SmallPrimeNTT.PRIMES.getD i default
    let rx := SmallPrimeNTT.mp_Rx31 dlen pr.p pr.p0i pr.R2
    for j in [:hn] do
      Ft := Ft.set! (i * n + hn + j)
        (zint_mod_small_signed Fd dlen j hn pr.p pr.p0i pr.R2 rx)
      Gt := Gt.set! (i * n + hn + j)
        (zint_mod_small_signed Gd dlen j hn pr.p pr.p0i pr.R2 rx)

  -- Unreduced (F, G) modulo each of the llen primes. (f, g) are brought back to RNS as the
  -- first slen primes are processed, then rebuilt into plain integers.
  for i in [:llen] do
    if i == slen then
      let (fg', _) := BigInt31.zint_rebuild_CRT (ft ++ gt) slen n 2 PRIMES_BI true
        (Array.replicate slen 0)
      ft := extractRange fg' 0 (slen * n)
      gt := extractRange fg' (slen * n) (slen * n)
    let pr := SmallPrimeNTT.PRIMES.getD i default
    let p := pr.p
    let p0i := pr.p0i
    let R2 := pr.R2
    let (gm, igm) := SmallPrimeNTT.mp_mkgmigm logn pr.g pr.ig p p0i
    let (fx, gx) :=
      if i < slen then
        (extractRange ft (i * n) n, extractRange gt (i * n) n)
      else
        (modPrimeNTT logn ft slen pr gm, modPrimeNTT logn gt slen pr gm)
    if i < slen then
      ft := writeRange ft (i * n) (SmallPrimeNTT.mp_iNTT logn fx igm p p0i)
      gt := writeRange gt (i * n) (SmallPrimeNTT.mp_iNTT logn gx igm p p0i)
    let Fdn := SmallPrimeNTT.mp_NTT (logn - 1) (extractRange Ft (i * n + hn) hn) gm p p0i
    let Gdn := SmallPrimeNTT.mp_NTT (logn - 1) (extractRange Gt (i * n + hn) hn) gm p p0i
    let mut Fe : Array UInt32 := Array.replicate n 0
    let mut Ge : Array UInt32 := Array.replicate n 0
    for j in [:hn] do
      let fa := getU32 fx (2 * j)
      let fb := getU32 fx (2 * j + 1)
      let ga := getU32 gx (2 * j)
      let gb := getU32 gx (2 * j + 1)
      let mFp := SmallPrimeNTT.mp_montymul (getU32 Fdn j) R2 p p0i
      let mGp := SmallPrimeNTT.mp_montymul (getU32 Gdn j) R2 p p0i
      Fe := Fe.set! (2 * j) (SmallPrimeNTT.mp_montymul gb mFp p p0i)
      Fe := Fe.set! (2 * j + 1) (SmallPrimeNTT.mp_montymul ga mFp p p0i)
      Ge := Ge.set! (2 * j) (SmallPrimeNTT.mp_montymul fb mGp p p0i)
      Ge := Ge.set! (2 * j + 1) (SmallPrimeNTT.mp_montymul fa mGp p p0i)
    Ft := writeRange Ft (i * n) (SmallPrimeNTT.mp_iNTT logn Fe igm p p0i)
    Gt := writeRange Gt (i * n) (SmallPrimeNTT.mp_iNTT logn Ge igm p p0i)

  if slen == llen then
    let (fg', _) := BigInt31.zint_rebuild_CRT (ft ++ gt) slen n 2 PRIMES_BI true
      (Array.replicate slen 0)
    ft := extractRange fg' 0 (slen * n)
    gt := extractRange fg' (slen * n) (slen * n)

  -- Unreduced (F, G) as plain integers.
  let (FG', _) := BigInt31.zint_rebuild_CRT (Ft ++ Gt) llen n 2 PRIMES_BI true
    (Array.replicate llen 0)
  Ft := extractRange FG' 0 (llen * n)
  Gt := extractRange FG' (llen * n) (llen * n)

  -- Babai reduction.
  let useSubNtt := depth > 1 && logn >= minLognFgNtt
  let rlen := min (WORD_WIN.getD depth 1) slen
  let blen := slen - rlen
  let ftb := extractRange ft (blen * n) (rlen * n)
  let gtb := extractRange gt (blen * n) (rlen * n)
  let scaleFg : UInt32 := 31 * blen.toUInt32
  let mut scaleFG : UInt32 := 31 * llen.toUInt32

  let scaleXf := PolyBigInt.poly_max_bitlength logn ftb rlen
  let scaleXg := PolyBigInt.poly_max_bitlength logn gtb rlen
  let scaleX := scaleXf ^^^ ((scaleXf ^^^ scaleXg) &&& BigInt31.tbmask (scaleXf - scaleXg))
  let scaleT0 : UInt32 := 15 - logn.toUInt32
  let scaleT := scaleT0 ^^^ ((scaleT0 ^^^ scaleX) &&& BigInt31.tbmask (scaleX - scaleT0))
  let scdiff := scaleX - scaleT

  -- rt3 <- adj(f)/(f*adj(f) + g*adj(g)), rt4 <- adj(g)/(f*adj(f) + g*adj(g))  (FFT)
  let mut rt3 := vectFFT logn (PolyBigInt.poly_big_to_fixed logn ftb rlen scdiff)
  let mut rt4 := vectFFT logn (PolyBigInt.poly_big_to_fixed logn gtb rlen scdiff)
  let rt1n := vectNormFft logn rt3 rt4
  rt3 := vectMul2e logn rt3 scaleT.toUInt64
  rt4 := vectMul2e logn rt4 scaleT.toUInt64
  for i in [:hn] do
    let d := rt1n.getD i 0
    rt3 := rt3.set! i (fxrDiv (rt3.getD i 0) d)
    rt3 := rt3.set! (i + hn) (fxrDiv (fxrNeg (rt3.getD (i + hn) 0)) d)
    rt4 := rt4.set! i (fxrDiv (rt4.getD i 0) d)
    rt4 := rt4.set! (i + hn) (fxrDiv (fxrNeg (rt4.getD (i + hn) 0)) d)

  -- (f, g) in RNS+NTT over slen + 1 primes, for poly_sub_scaled_ntt.
  let ftN := if useSubNtt then toRNSNTTExtended logn ft slen else #[]
  let gtN := if useSubNtt then toRNSNTTExtended logn gt slen else #[]

  let mut FGlen := llen
  let rb := reduceBits logn_top
  -- `scaleFG` decreases by `rb ≥ 11` per iteration until it reaches `scaleFg`, so
  -- `31 * llen` iterations always suffice.
  for _ in [:31 * llen + 1] do
    let (tlen, toff) := PolyBigInt.divrem31 scaleFG
    let tl := tlen.toNat
    let mut rt1 := PolyBigInt.poly_big_to_fixed logn
      (extractRange Ft (tl * n) ((FGlen - tl) * n)) (FGlen - tl) (scaleX + toff)
    let mut rt2 := PolyBigInt.poly_big_to_fixed logn
      (extractRange Gt (tl * n) ((FGlen - tl) * n)) (FGlen - tl) (scaleX + toff)
    rt1 := vectFFT logn rt1
    rt2 := vectFFT logn rt2
    rt1 := vectMulFft logn rt1 rt3
    rt2 := vectMulFft logn rt2 rt4
    rt2 := vectAdd logn rt2 rt1
    rt2 := vectIFFT logn rt2
    let k : Array Int32 := (Array.range n).map fun i => fxrRound (rt2.getD i 0)

    let scaleK := scaleFG - scaleFg
    if depth == 1 then
      let (F', G') := PolyBigInt.polySubKfgScaledDepth1 logn_top Ft Gt FGlen k scaleK f g
      Ft := F'
      Gt := G'
    else if useSubNtt then
      Ft := PolyBigInt.poly_sub_scaled_ntt logn Ft FGlen ftN slen k scaleK
      Gt := PolyBigInt.poly_sub_scaled_ntt logn Gt FGlen gtN slen k scaleK
    else
      Ft := PolyBigInt.poly_sub_scaled logn Ft FGlen ft slen k scaleK
      Gt := PolyBigInt.poly_sub_scaled logn Gt FGlen gt slen k scaleK

    if scaleFG <= scaleFg then break
    if scaleFG <= scaleFg + rb then
      scaleFG := scaleFg
    else
      scaleFG := scaleFG - rb
    for _ in [:llen] do
      if FGlen > slen && 31 * (FGlen - slen) > (scaleFG - scaleFg + 30).toNat then
        FGlen := FGlen - 1

  -- Output: F then G, slen words per coefficient.
  let capF := extractRange Ft 0 (slen * n)
  let capG := extractRange Gt 0 (slen * n)
  let out := writeRange (writeRange buf 0 capF) (slen * n) capG

  -- At depth 1 (f, g) are not kept; the depth-0 check covers that level.
  if depth == 1 then return some out

  -- Check f*G - g*F = q modulo the first prime (in NTT).
  let pr := SmallPrimeNTT.PRIMES.getD 0 default
  let p := pr.p
  let p0i := pr.p0i
  let gm := SmallPrimeNTT.mp_mkgm logn pr.g p p0i
  let fN := if useSubNtt then extractRange ftN 0 n else modPrimeNTT logn ft slen pr gm
  let gN := if useSubNtt then extractRange gtN 0 n else modPrimeNTT logn gt slen pr gm
  let capGN := modPrimeNTT logn capG slen pr gm
  let capFN := modPrimeNTT logn capF slen pr gm
  let rv := SmallPrimeNTT.mp_montymul Q 1 p p0i
  for i in [:n] do
    let t3 := SmallPrimeNTT.mp_montymul (getU32 fN i) (getU32 capGN i) p p0i
    let x := SmallPrimeNTT.mp_montymul (getU32 gN i) (getU32 capFN i) p p0i
    if SmallPrimeNTT.mp_sub t3 x p != rv then return none
  return some out

/-! ## solve_NTRU_depth0

Specialized top-level solver for depth 0. At this depth all polynomial
coefficients fit in a single 31-bit word, so a single prime modulus
suffices for all modular arithmetic.

1. Load `f, g` into RNS+NTT; load deeper-level `(F, G)` and NTT them.
2. Compute unreduced `(F, G)` at degree `n` via NTT lifting.
3. Compute adjoint products `F·adj(f) + G·adj(g)` and
   `f·adj(f) + g·adj(g)` using NTT, then convert to FFT domain.
4. Divide and round: `k = round(quotient)`, convert `k` to NTT+Montgomery.
5. Subtract: `F ← F - k·f`, `G ← G - k·g` in NTT form.
6. Verify `f·G - g·F ≡ q·R (mod p)` for all NTT slots.
7. Convert back via inverse NTT and normalize. -/

/-- Solve the NTRU equation at the top level (depth 0, degree `2^logn`), given `(F, G)` from
depth 1 at the start of `buf` (one word per coefficient). On success the reduced `(F, G)`
(plain one-word signed coefficients) are written at the start of the returned buffer.
Returns `none` when `f·G - g·F = q` fails modulo the first small prime. -/
def solve_NTRU_depth0 (logn : Nat) (f g : Array Int8)
    (buf : Array UInt32) : Option (Array UInt32) := Id.run do
  let n := 1 <<< logn
  let hn := n >>> 1
  let pr := SmallPrimeNTT.PRIMES.getD 0 default
  let p := pr.p
  let p0i := pr.p0i
  let R2 := pr.R2
  let (gm, igm) := SmallPrimeNTT.mp_mkgmigm logn pr.g pr.ig p p0i

  -- f and g in RNS+NTT
  let ft := SmallPrimeNTT.mp_NTT logn (SmallPrimeNTT.mp_set_small logn f p) gm p p0i
  let gt := SmallPrimeNTT.mp_NTT logn (SmallPrimeNTT.mp_set_small logn g p) gm p p0i

  -- Deeper (F, G) in RNS+NTT
  let Fd := SmallPrimeNTT.mp_NTT (logn - 1)
    (SmallPrimeNTT.poly_mp_set (logn - 1) (extractRange buf 0 hn) p) gm p p0i
  let Gd := SmallPrimeNTT.mp_NTT (logn - 1)
    (SmallPrimeNTT.poly_mp_set (logn - 1) (extractRange buf hn hn) p) gm p p0i

  -- Unreduced (F, G) (RNS+NTT)
  let mut Fp : Array UInt32 := Array.replicate n 0
  let mut Gp : Array UInt32 := Array.replicate n 0
  for i in [:hn] do
    let fa := getU32 ft (2 * i)
    let fb := getU32 ft (2 * i + 1)
    let ga := getU32 gt (2 * i)
    let gb := getU32 gt (2 * i + 1)
    let mFd := SmallPrimeNTT.mp_montymul (getU32 Fd i) R2 p p0i
    let mGd := SmallPrimeNTT.mp_montymul (getU32 Gd i) R2 p p0i
    Fp := Fp.set! (2 * i) (SmallPrimeNTT.mp_montymul gb mFd p p0i)
    Fp := Fp.set! (2 * i + 1) (SmallPrimeNTT.mp_montymul ga mFd p p0i)
    Gp := Gp.set! (2 * i) (SmallPrimeNTT.mp_montymul fb mGd p p0i)
    Gp := Gp.set! (2 * i + 1) (SmallPrimeNTT.mp_montymul fa mGd p p0i)

  -- t1 <- F*adj(f) + G*adj(g), t3 <- f*adj(f) + g*adj(g)  (RNS+NTT)
  let mut t1 : Array UInt32 := Array.replicate n 0
  let mut t3 : Array UInt32 := Array.replicate n 0
  for i in [:n] do
    let w := SmallPrimeNTT.mp_montymul (getU32 ft (n - 1 - i)) R2 p p0i
    t1 := t1.set! i (SmallPrimeNTT.mp_montymul w (getU32 Fp i) p p0i)
    t3 := t3.set! i (SmallPrimeNTT.mp_montymul w (getU32 ft i) p p0i)
  for i in [:n] do
    let w := SmallPrimeNTT.mp_montymul (getU32 gt (n - 1 - i)) R2 p p0i
    t1 := t1.set! i
      (SmallPrimeNTT.mp_add (getU32 t1 i) (SmallPrimeNTT.mp_montymul w (getU32 Gp i) p p0i) p)
    t3 := t3.set! i
      (SmallPrimeNTT.mp_add (getU32 t3 i) (SmallPrimeNTT.mp_montymul w (getU32 gt i) p p0i) p)
  t1 := SmallPrimeNTT.mp_iNTT logn t1 igm p p0i
  t3 := SmallPrimeNTT.mp_iNTT logn t3 igm p p0i

  -- Fixed-point FFT of both (plain values scaled down by 2^10), then divide and round.
  let toFxr (x : UInt32) : FXR :=
    fxrOfScaled32 ((SmallPrimeNTT.mp_norm x p).toInt64.toUInt64 <<< 22)
  let rt2full := vectFFT logn ((Array.range n).map fun i => toFxr (getU32 t3 i))
  let rt2 := rt2full.extract 0 hn
  let mut rt3 := vectFFT logn ((Array.range n).map fun i => toFxr (getU32 t1 i))
  rt3 := vectDivSelfadjFft logn rt3 rt2
  rt3 := vectIFFT logn rt3

  -- k in RNS+NTT+Montgomery
  let mut k : Array UInt32 :=
    (Array.range n).map fun i => SmallPrimeNTT.mp_set (fxrRound (rt3.getD i 0)) p
  k := SmallPrimeNTT.mp_NTT logn k gm p p0i
  k := k.map fun x => SmallPrimeNTT.mp_montymul x R2 p p0i

  -- Subtract k*(f, g) from (F, G) and check f*G - g*F = q.
  let rv := SmallPrimeNTT.mp_montymul Q 1 p p0i
  for i in [:n] do
    let ki := getU32 k i
    let fi := getU32 ft i
    let gi := getU32 gt i
    let Fi := SmallPrimeNTT.mp_sub (getU32 Fp i) (SmallPrimeNTT.mp_montymul ki fi p p0i) p
    let Gi := SmallPrimeNTT.mp_sub (getU32 Gp i) (SmallPrimeNTT.mp_montymul ki gi p p0i) p
    Fp := Fp.set! i Fi
    Gp := Gp.set! i Gi
    let x := SmallPrimeNTT.mp_sub
      (SmallPrimeNTT.mp_montymul fi Gi p p0i) (SmallPrimeNTT.mp_montymul gi Fi p p0i) p
    if x != rv then return none

  -- Back to plain representation.
  Fp := SmallPrimeNTT.poly_mp_norm logn (SmallPrimeNTT.mp_iNTT logn Fp igm p p0i) p
  Gp := SmallPrimeNTT.poly_mp_norm logn (SmallPrimeNTT.mp_iNTT logn Gp igm p p0i) p
  return some (writeRange (writeRange (ensureSize buf (2 * n)) 0 Fp) n Gp)

/-! ## Lifting loop helper -/

/-- Lift `(F, G)` from the deepest level through intermediate depths
`logn - 1` down to depth 1. Returns `none` if any step fails. -/
private def liftIntermediateLevels (logn : Nat) (f g : Array Int8)
    (buf : Array UInt32) : Option (Array UInt32) := Id.run do
  let mut buf := buf
  for d in [1:logn] do
    let depth := logn - d
    match solve_NTRU_intermediate logn f g depth buf with
    | none => return none
    | some buf' => buf := buf'
  return some buf

/-! ## solve_NTRU — Main entry point

Solve the NTRU equation: given `f, g ∈ ℤ[x]/(x^n + 1)` with `n = 2^logn`,
find `F, G` satisfying `f · G - g · F = q`.

The algorithm proceeds in three phases:

1. **Descent + base case**: Iteratively compute field norms to reduce
   `(f, g)` to scalar resultants, then solve the scalar NTRU equation
   `f₀ · G₀ - g₀ · F₀ = q` via extended binary GCD.

2. **Ascent (intermediate)**: Lift `(F, G)` from depth `logn - 1` to
   depth 1. At each level, the degree doubles and Babai's nearest-plane
   reduction keeps `(F, G)` small.

3. **Top level (depth 0)**: Apply the specialized single-prime solver.
   Convert the result from 31-bit limbs to `Int8` representation and
   verify that coefficients are within `[-127, 127]`.

Returns `some (F, G)` on success, or `none` on failure. -/

/-- Solve `f·G - g·F = q` for short `(F, G)` given short `(f, g)` of degree `2^logn`,
returning `none` when the resultants are not coprime, a reduction check fails, or a
coefficient of `F` or `G` falls outside `[-127, 127]`. -/
def solve_NTRU (logn : Nat) (f g : Array Int8) :
    Option (Array Int8 × Array Int8) := do
  let n := 1 <<< logn
  let buf ← solve_NTRU_deepest logn f g
  let buf ← liftIntermediateLevels logn f g buf
  let buf ← solve_NTRU_depth0 logn f g buf
  let (capF, okF) := PolyBigInt.poly_big_to_small logn (extractRange buf 0 n) 127
  guard okF
  let (capG, okG) := PolyBigInt.poly_big_to_small logn (extractRange buf n n) 127
  guard okG
  pure (capF, capG)

/-! ## check_ortho_norm

Verify that the Gram-Schmidt norm `‖b̃₁‖²` of the NTRU lattice basis
`B = [[g, -f], [G, -F]]` is below the Falcon acceptance threshold.

The second Gram-Schmidt vector satisfies (in FFT representation):
```
b̃₁ = q · [adj(f), adj(g)] / (f · adj(f) + g · adj(g))
```

Its squared norm is computed and compared against the threshold constant
`72251709809335` (a 32.32 fixed-point value from Section 3.8.2 of the
Falcon specification). -/

/-- Whether the squared norm of `q · (adj f, adj g) / (f·adj f + g·adj g)`, computed in
32.32 fixed point, is below the Falcon acceptance threshold. -/
def check_ortho_norm (logn : Nat) (f g : Array Int8) : Bool := Id.run do
  let n := 1 <<< logn
  let mut rt1 := vectFFT logn (vectSet logn (f.map Int8.toInt32))
  let mut rt2 := vectFFT logn (vectSet logn (g.map Int8.toInt32))
  let rt3 := vectInvnormFft logn rt1 rt2 0
  rt1 := vectAdjFft logn rt1
  rt2 := vectAdjFft logn rt2
  rt1 := vectMulRealconst logn rt1 (fxrOf 12289)
  rt2 := vectMulRealconst logn rt2 (fxrOf 12289)
  rt1 := vectMulSelfadjFft logn rt1 rt3
  rt2 := vectMulSelfadjFft logn rt2 rt3
  rt1 := vectIFFT logn rt1
  rt2 := vectIFFT logn rt2
  let mut sn : FXR := fxrZero
  for i in [:n] do
    sn := fxrAdd sn (fxrAdd (fxrSqr (rt1.getD i 0)) (fxrSqr (rt2.getD i 0)))
  return fxrLt sn (fxrOfScaled32 72251709809335)

end Falcon.Concrete.NTRUSolver
