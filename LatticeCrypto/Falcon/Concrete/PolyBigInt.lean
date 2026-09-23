/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import LatticeCrypto.Falcon.Concrete.BigInt31
public import LatticeCrypto.Falcon.Concrete.SmallPrimeNTT

/-!
# Polynomial Big-Integer Operations for Falcon Key Generation

Port of polynomial-level big-integer operations from `c-fn-dsa/kgen_poly.c`.

These functions operate on polynomials whose coefficients are multi-word big
integers stored in an interleaved layout: for a polynomial of degree `n = 2^logn`
with `len` words per coefficient, coefficient `i` word `j` is stored at index
`i + j * n`. Functions coordinate between `BigInt31` (multi-precision arithmetic)
and `SmallPrimeNTT` (modular NTT) to implement fast polynomial operations used
in NTRU equation solving.

## Main Functions

- `poly_mp_set_small` — set polynomial from small integers in modular form
- `poly_big_to_small` — convert big-int polynomial to small integers
- `poly_max_bitlength` — find maximum coefficient bit-length
- `poly_big_to_fixed` — convert big-int polynomial to fixed-point representation
- `poly_sub_scaled` — subtract a scaled polynomial (quadratic, general-case)
- `poly_sub_scaled_ntt` — subtract scaled polynomial using NTT
-/

public section


namespace Falcon.Concrete.PolyBigInt

open BigInt31 (tbmask lzcnt getLimb setLimb LIMB_MASK)

/-! ## Helpers -/

/-- Compute `(x / 31, x % 31)` for unsigned `x ≤ 63487`. Constant-time. -/
@[inline] def divrem31 (x : UInt32) : UInt32 × UInt32 :=
  let q := (x * 67651) >>> (21 : UInt32)
  (q, x - 31 * q)

/-- Convert a `SmallPrimeNTT.SmallPrime` to `BigInt31.SmallPrime` (drops `g`/`ig`). -/
@[inline] def toBI31Prime (sp : SmallPrimeNTT.SmallPrime) : BigInt31.SmallPrime :=
  { p := sp.p, p0i := sp.p0i, R2 := sp.R2, s := sp.s }

/-! ## Offset-aware big-integer helpers

The interleaved polynomial layout requires accessing big integers at different
offsets within a flat array. These generalize the stride-based functions in
`BigInt31` to accept explicit starting offsets. -/

/-- Add `k * (2^(31*sch + scl)) * y` to a big integer at offset `xoff` in `arr`.
`y` starts at offset `yoff` in `yarr`. Both use the given `stride`. -/
def zint_add_scaled_mul_small_off (arr : Array UInt32) (xlen : Nat) (xoff : Nat)
    (yarr : Array UInt32) (ylen : Nat) (yoff : Nat) (stride : Nat)
    (k : Int32) (sch scl : UInt32) : Array UInt32 := Id.run do
  if ylen == 0 then return arr
  let ysign :=
    (- (getLimb yarr yoff stride (ylen - 1) >>> (30 : UInt32))) >>> (1 : UInt32)
  let mut tw : UInt32 := 0
  let mut cc : Int32 := 0
  let mut a := arr
  let mut yrem := ylen
  let mut yidx : Nat := 0
  for i in [sch.toNat:xlen] do
    let mut wy : UInt32 := ysign
    if yrem > 0 then
      wy := getLimb yarr yoff stride yidx
      yidx := yidx + 1
      yrem := yrem - 1
    let wys := ((wy <<< scl) &&& LIMB_MASK) ||| tw
    tw := wy >>> (31 - scl)
    let xw := getLimb a xoff stride i
    let z : Int64 :=
      wys.toUInt64.toInt64 * k.toInt64 + xw.toUInt64.toInt64 + cc.toInt64
    a := setLimb a xoff stride i (z.toUInt64.toUInt32 &&& LIMB_MASK)
    cc := (z.toUInt64 >>> (31 : UInt64)).toUInt32.toInt32
  return a

/-- Subtract `(2^(31*sch + scl)) * y` from a big integer at offset `xoff` in `arr`.
`y` starts at offset `yoff` in `yarr`. Both use the given `stride`. -/
def zint_sub_scaled_off (arr : Array UInt32) (xlen : Nat) (xoff : Nat)
    (yarr : Array UInt32) (ylen : Nat) (yoff : Nat) (stride : Nat)
    (sch scl : UInt32) : Array UInt32 := Id.run do
  if ylen == 0 then return arr
  let ysign :=
    (- (getLimb yarr yoff stride (ylen - 1) >>> (30 : UInt32))) >>> (1 : UInt32)
  let mut tw : UInt32 := 0
  let mut cc : UInt32 := 0
  let mut a := arr
  let mut yrem := ylen
  let mut yidx : Nat := 0
  for i in [sch.toNat:xlen] do
    let mut wy : UInt32 := ysign
    if yrem > 0 then
      wy := getLimb yarr yoff stride yidx
      yidx := yidx + 1
      yrem := yrem - 1
    let wys := ((wy <<< scl) &&& LIMB_MASK) ||| tw
    tw := wy >>> (31 - scl)
    let xw := getLimb a xoff stride i
    let w := xw - wys - cc
    a := setLimb a xoff stride i (w &&& LIMB_MASK)
    cc := w >>> (31 : UInt32)
  return a

/-! ## Polynomial conversion functions -/

/-- Set polynomial from small signed integers, reducing each modulo prime `p`. -/
def poly_mp_set_small (logn : Nat) (f : Array Int8) (p : UInt32) :
    Array UInt32 := Id.run do
  let n := 1 <<< logn
  let mut d : Array UInt32 := Array.replicate n 0
  for i in [:n] do
    d := d.set! i (SmallPrimeNTT.mp_set (f.getD i 0).toInt32 p)
  return d

/-- Convert a polynomial from one-word signed representation (31-bit limbs,
sign in bit 30) to small `Int8` values. Returns `(result, success)` where
`success = true` iff every coefficient satisfies `|coeff| ≤ lim`.
Aborts early on failure. -/
def poly_big_to_small (logn : Nat) (s : Array UInt32) (lim : Int32) :
    Array Int8 × Bool := Id.run do
  let n := 1 <<< logn
  let mut d : Array Int8 := Array.replicate n 0
  for i in [:n] do
    let x := s.getD i 0
    let x' := x ||| ((x &&& 0x40000000) <<< (1 : UInt32))
    let z := x'.toInt32
    if z < -lim || z > lim then
      return (d, false)
    d := d.set! i z.toInt8
  return (d, true)

/-- Maximum bit-length of any coefficient in a polynomial with `flen`-word
interleaved big-integer coefficients.

The "bit length" is the length of the minimal two's-complement representation
excluding the sign bit. Constant-time w.r.t. coefficient values and result. -/
def poly_max_bitlength (logn : Nat) (f : Array UInt32) (flen : Nat) :
    UInt32 := Id.run do
  if flen == 0 then return 0
  let n := 1 <<< logn
  let mut t : UInt32 := 0
  let mut tk : UInt32 := 0
  for i in [:n] do
    let m := (- (getLimb f i n (flen - 1) >>> (30 : UInt32))) &&& LIMB_MASK
    let mut c : UInt32 := 0
    let mut ck : UInt32 := 0
    for j in [:flen] do
      let w := getLimb f i n j ^^^ m
      let nz := ((w - 1) >>> (31 : UInt32)) - 1
      c := c ^^^ (nz &&& (c ^^^ w))
      ck := ck ^^^ (nz &&& (ck ^^^ UInt32.ofNat j))
    let rr := tbmask ((tk - ck) ||| (((tk ^^^ ck) - 1) &&& (t - c)))
    t := t ^^^ (rr &&& (t ^^^ c))
    tk := tk ^^^ (rr &&& (tk ^^^ ck))
  31 * tk + 32 - lzcnt t

/-- Convert big-integer polynomial coefficients to 64-bit fixed-point values
representing `x / 2^sc`. Each coefficient has `len` interleaved words with
stride `n = 2^logn`. Assumes `|x| < 2^(30+sc)` and `len < 2^24`. -/
def poly_big_to_fixed (logn : Nat) (f : Array UInt32) (len : Nat)
    (sc : UInt32) : Array UInt64 := Id.run do
  let n := 1 <<< logn
  if len == 0 then return Array.replicate n 0
  let (sch', scl') := divrem31 sc
  let zz := (scl' - 1) >>> (31 : UInt32)
  let sch := sch' - zz
  let scl := scl' ||| (31 &&& (- zz))
  let t0 := (sch - 1) &&& 0xFFFFFF
  let t1 := sch &&& 0xFFFFFF
  let t2 := (sch + 1) &&& 0xFFFFFF
  let len32 := UInt32.ofNat len
  let mut d : Array UInt64 := Array.replicate n 0
  for i in [:n] do
    let mut w0 : UInt32 := 0
    let mut w1 : UInt32 := 0
    let mut w2 : UInt32 := 0
    for j in [:len] do
      let w := getLimb f i n j
      let tj := UInt32.ofNat j &&& 0xFFFFFF
      w0 := w0 ||| (w &&& (- (((tj ^^^ t0) - 1) >>> (31 : UInt32))))
      w1 := w1 ||| (w &&& (- (((tj ^^^ t1) - 1) >>> (31 : UInt32))))
      w2 := w2 ||| (w &&& (- (((tj ^^^ t2) - 1) >>> (31 : UInt32))))
    let ws := (- (getLimb f i n (len - 1) >>> (30 : UInt32))) >>> (1 : UInt32)
    w0 := w0 ||| (ws &&& (- ((len32 - sch) >>> (31 : UInt32))))
    w1 := w1 ||| (ws &&& (- ((len32 - sch - 1) >>> (31 : UInt32))))
    w2 := w2 ||| (ws &&& (- ((len32 - sch - 2) >>> (31 : UInt32))))
    let w2' := w2 ||| ((w2 &&& 0x40000000) <<< (1 : UInt32))
    let xl := (w0 >>> (scl - 1)) ||| (w1 <<< (32 - scl))
    let xh := (w1 >>> scl) ||| (w2' <<< (31 - scl))
    d := d.set! i (xl.toUInt64 ||| (xh.toUInt64 <<< (32 : UInt64)))
  return d

/-! ## Polynomial scaled subtraction -/

/-- Subtract `k * f * 2^sc` from `F`, where `F` and `f` are polynomials with
multi-word big-integer coefficients in interleaved layout, and `k` is a
polynomial with small `Int32` coefficients.

This implements the general-case quadratic algorithm (O(n²) in the polynomial
degree). The C code has optimized unrolled versions for `logn ∈ {1, 2, 3}`
which are omitted here. -/
def poly_sub_scaled (logn : Nat) (F : Array UInt32) (Flen : Nat)
    (f : Array UInt32) (flen : Nat)
    (k : Array Int32) (sc : UInt32) : Array UInt32 := Id.run do
  if flen == 0 then return F
  let n := 1 <<< logn
  let (sch, scl) := divrem31 sc
  if sch.toNat >= Flen then return F
  let Foff := sch.toNat * n
  let Flen' := Flen - sch.toNat
  let mut arr := F
  for i in [:n] do
    let mut kf : Int32 := -(k.getD i (0 : Int32))
    let mut xcoeff := i
    for j in [:n] do
      arr := zint_add_scaled_mul_small_off arr Flen' (Foff + xcoeff)
        f flen j n kf 0 scl
      if i + j == n - 1 then
        xcoeff := 0
        kf := -kf
      else
        xcoeff := xcoeff + 1
  return arr

/-- Subtract `k * f * 2^sc` from `F` using NTT-based polynomial multiplication.

`f` must already be in RNS+NTT form over `flen + 1` words; `F` is in plain
interleaved representation with `Flen` words per coefficient. `k` has small
`Int32` coefficients.

The algorithm:
1. Compute `k * f` using small-prime NTT (for each prime: reduce `k` mod p,
   NTT, pointwise multiply with NTT(f), iNTT)
2. Reconstruct `k * f` from RNS via CRT
3. Subtract the scaled result from `F` -/
def poly_sub_scaled_ntt (logn : Nat) (F : Array UInt32) (Flen : Nat)
    (f : Array UInt32) (flen : Nat)
    (k : Array Int32) (sc : UInt32) : Array UInt32 := Id.run do
  let n := 1 <<< logn
  let tlen := flen + 1
  let (sch, scl) := divrem31 sc
  let mut fk : Array UInt32 := Array.replicate (tlen * n) 0
  for i in [:tlen] do
    if i < SmallPrimeNTT.PRIMES.size then
      let pr := SmallPrimeNTT.PRIMES[i]!
      let p := pr.p
      let p0i := pr.p0i
      let R2 := pr.R2
      let (gm, igm) := SmallPrimeNTT.mp_mkgmigm logn pr.g pr.ig p p0i
      let mut t1 : Array UInt32 := Array.replicate n 0
      for j in [:n] do
        t1 := t1.set! j (SmallPrimeNTT.mp_set (k.getD j (0 : Int32)) p)
      t1 := SmallPrimeNTT.mp_NTT logn t1 gm p p0i
      for j in [:n] do
        let fsj := f.getD (i * n + j) 0
        let v := SmallPrimeNTT.mp_montymul
          (SmallPrimeNTT.mp_montymul (t1.getD j 0) fsj p p0i) R2 p p0i
        fk := fk.set! (i * n + j) v
      let fkSlice := fk.extract (i * n) (i * n + n)
      let fkSlice' := SmallPrimeNTT.mp_iNTT logn fkSlice igm p p0i
      for j in [:n] do
        fk := fk.set! (i * n + j) (fkSlice'.getD j 0)
  let primesBig : Array BigInt31.SmallPrime :=
    SmallPrimeNTT.PRIMES.map toBI31Prime
  let tmp : Array UInt32 := Array.replicate tlen 0
  let (fk', _) := BigInt31.zint_rebuild_CRT fk tlen n 1 primesBig true tmp
  fk := fk'
  let mut arr := F
  for i in [:n] do
    arr := zint_sub_scaled_off arr Flen i fk tlen i n sch scl
  return arr

/-! ## Depth-1 Babai subtraction

At depth 1 of the NTRU solver the reduced `(F, G)` fit on at most two words per
coefficient, so the subtraction of `k * (f', g')` (where `f' = N(f)` and `g' = N(g)` are the
field norms of the top-level polynomials) is carried out entirely in RNS+NTT over the first
`FGlen` small primes, recomputing `(f', g')` on the fly from the top-level `(f, g)`. -/

/-- Signed one-word (31-bit limb) value to its sign-extended `Int32`. -/
@[inline] private def signExt31 (x : UInt32) : Int32 :=
  (x ||| ((x &&& 0x40000000) <<< (1 : UInt32))).toInt32

/-- NTT of `N(h)` modulo one small prime at degree `2^logn`, where `h` is a top-level
polynomial of degree `2^(logn + 1)` given by its small coefficients. Uses
`N(h) = h_e² - X·h_o²` with the NTT of `X` read from the twiddle table `gm`. -/
private def fieldNormNTT (logn : Nat) (h : Array Int8) (gm : Array UInt32)
    (p p0i : UInt32) : Array UInt32 := Id.run do
  let n := 1 <<< logn
  let hn := n >>> 1
  let mut t1 : Array UInt32 := Array.replicate n 0
  let mut t2 : Array UInt32 := Array.replicate n 0
  for j in [:n] do
    t1 := t1.set! j (SmallPrimeNTT.mp_set (h.getD (2 * j) 0).toInt32 p)
    t2 := t2.set! j (SmallPrimeNTT.mp_set (h.getD (2 * j + 1) 0).toInt32 p)
  t1 := SmallPrimeNTT.mp_NTT logn t1 gm p p0i
  t2 := SmallPrimeNTT.mp_NTT logn t2 gm p p0i
  let mut d : Array UInt32 := Array.replicate n 0
  for j in [:hn] do
    let xe0 := t1.getD (2 * j) 0
    let xe1 := t1.getD (2 * j + 1) 0
    let xo0 := t2.getD (2 * j) 0
    let xo1 := t2.getD (2 * j + 1) 0
    let xv0 := gm.getD (hn + j) 0
    let xv1 := p - xv0
    let xe0 := SmallPrimeNTT.mp_montymul xe0 xe0 p p0i
    let xe1 := SmallPrimeNTT.mp_montymul xe1 xe1 p p0i
    let xo0 := SmallPrimeNTT.mp_montymul xo0 xo0 p p0i
    let xo1 := SmallPrimeNTT.mp_montymul xo1 xo1 p p0i
    d := d.set! (2 * j)
      (SmallPrimeNTT.mp_sub xe0 (SmallPrimeNTT.mp_montymul xo0 xv0 p p0i) p)
    d := d.set! (2 * j + 1)
      (SmallPrimeNTT.mp_sub xe1 (SmallPrimeNTT.mp_montymul xo1 xv1 p p0i) p)
  return d

/-- Convert one polynomial of `(F, G)` (one or two words per coefficient, stride `n`) from
plain signed representation to RNS over the first `FGlen ∈ {1, 2}` small primes. -/
private def depth1ToRNS (n : Nat) (F : Array UInt32) (FGlen : Nat) :
    Array UInt32 := Id.run do
  let mut F := F
  if FGlen == 1 then
    let p := (SmallPrimeNTT.PRIMES.getD 0 default).p
    for i in [:n] do
      F := F.set! i (SmallPrimeNTT.mp_set (signExt31 (F.getD i 0)) p)
  else
    let pr0 := SmallPrimeNTT.PRIMES.getD 0 default
    let pr1 := SmallPrimeNTT.PRIMES.getD 1 default
    let p0 := pr0.p
    let p1 := pr1.p
    let z0 := SmallPrimeNTT.mp_half pr0.R2 p0
    let z1 := SmallPrimeNTT.mp_half pr1.R2 p1
    for i in [:n] do
      let xl := F.getD i 0
      let xh := signExt31 (F.getD (i + n) 0)
      let yl0 := xl - (p0 &&& ~~~(tbmask (xl - p0)))
      let yh0 := SmallPrimeNTT.mp_set xh p0
      let r0 := SmallPrimeNTT.mp_add yl0 (SmallPrimeNTT.mp_montymul yh0 z0 p0 pr0.p0i) p0
      let yl1 := xl - (p1 &&& ~~~(tbmask (xl - p1)))
      let yh1 := SmallPrimeNTT.mp_set xh p1
      let r1 := SmallPrimeNTT.mp_add yl1 (SmallPrimeNTT.mp_montymul yh1 z1 p1 pr1.p0i) p1
      F := F.set! i r0
      F := F.set! (i + n) r1
  return F

/-- Convert one polynomial of `(F, G)` from RNS over the first `FGlen ∈ {1, 2}` small primes
back to plain signed representation (31-bit limbs, stride `n`). -/
private def depth1FromRNS (n : Nat) (F : Array UInt32) (FGlen : Nat) :
    Array UInt32 := Id.run do
  let mut F := F
  if FGlen == 1 then
    let p := (SmallPrimeNTT.PRIMES.getD 0 default).p
    for i in [:n] do
      F := F.set! i ((SmallPrimeNTT.mp_norm (F.getD i 0) p).toUInt32 &&& LIMB_MASK)
  else
    let pr1 := SmallPrimeNTT.PRIMES.getD 1 default
    let p0 := (SmallPrimeNTT.PRIMES.getD 0 default).p
    let p1 := pr1.p
    let pp : UInt64 := p0.toUInt64 * p1.toUInt64
    let hpp := pp >>> 1
    for i in [:n] do
      let x0 := F.getD i 0
      let x1 := F.getD (i + n) 0
      let x0m1 := x0 - (p1 &&& ~~~(tbmask (x0 - p1)))
      let y := SmallPrimeNTT.mp_montymul (SmallPrimeNTT.mp_sub x1 x0m1 p1) pr1.s p1 pr1.p0i
      let z : UInt64 := x0.toUInt64 + p0.toUInt64 * y.toUInt64
      let z := z - (pp &&& ((0 : UInt64) - ((hpp - z) >>> 63)))
      F := F.set! i (z.toUInt32 &&& LIMB_MASK)
      F := F.set! (i + n) ((z >>> 31).toUInt32 &&& LIMB_MASK)
  return F

/-- Subtract `k * (2^sc) * (f', g')` from `(F, G)` at depth 1 of the NTRU solver, where
`f' = N(f)` and `g' = N(g)` are the field norms of the top-level polynomials `f, g` (degree
`2^logn_top`), `F` and `G` hold `FGlen ∈ {1, 2}` words per coefficient at degree
`2^(logn_top - 1)`, and `k` holds signed 32-bit coefficients. The subtraction is performed in
RNS+NTT over the first `FGlen` small primes, so the result is exact as long as the output
coefficients fit in the RNS range. -/
def polySubKfgScaledDepth1 (logn_top : Nat) (F G : Array UInt32) (FGlen : Nat)
    (k : Array Int32) (sc : UInt32) (f g : Array Int8) : Array UInt32 × Array UInt32 :=
  Id.run do
  let logn := logn_top - 1
  let n := 1 <<< logn
  let mut F := depth1ToRNS n F FGlen
  let mut G := depth1ToRNS n G FGlen
  let mut kk : Array UInt32 := (Array.range n).map fun j => (k.getD j 0).toUInt32
  for i in [:FGlen] do
    let pr := SmallPrimeNTT.PRIMES.getD i default
    let p := pr.p
    let p0i := pr.p0i
    let R2 := pr.R2
    let R3 := SmallPrimeNTT.mp_montymul R2 R2 p p0i
    let gm := SmallPrimeNTT.mp_mkgm logn pr.g p p0i
    -- k <- (2^sc) * k, into NTT
    let mut scv := SmallPrimeNTT.mp_montymul ((1 : UInt32) <<< (sc &&& 31)) R2 p p0i
    for _ in [:(sc >>> 5).toNat] do
      scv := SmallPrimeNTT.mp_montymul scv R2 p p0i
    for j in [:n] do
      let x := SmallPrimeNTT.mp_set (kk.getD j 0).toInt32 p
      kk := kk.set! j (SmallPrimeNTT.mp_montymul scv x p p0i)
    kk := SmallPrimeNTT.mp_NTT logn kk gm p p0i
    -- F and G lines for this prime, into NTT
    let mut Fu := SmallPrimeNTT.mp_NTT logn (F.extract (i * n) (i * n + n)) gm p p0i
    let mut Gu := SmallPrimeNTT.mp_NTT logn (G.extract (i * n) (i * n + n)) gm p p0i
    let ft := fieldNormNTT logn f gm p p0i
    let gt := fieldNormNTT logn g gm p p0i
    for j in [:n] do
      let kj := kk.getD j 0
      let xkf := SmallPrimeNTT.mp_montymul
        (SmallPrimeNTT.mp_montymul (ft.getD j 0) kj p p0i) R3 p p0i
      Fu := Fu.set! j (SmallPrimeNTT.mp_sub (Fu.getD j 0) xkf p)
      let xkg := SmallPrimeNTT.mp_montymul
        (SmallPrimeNTT.mp_montymul (gt.getD j 0) kj p p0i) R3 p p0i
      Gu := Gu.set! j (SmallPrimeNTT.mp_sub (Gu.getD j 0) xkg p)
    -- back to RNS
    let igm := (SmallPrimeNTT.mp_mkgmigm logn pr.g pr.ig p p0i).2
    Fu := SmallPrimeNTT.mp_iNTT logn Fu igm p p0i
    Gu := SmallPrimeNTT.mp_iNTT logn Gu igm p p0i
    for j in [:n] do
      F := F.set! (i * n + j) (Fu.getD j 0)
      G := G.set! (i * n + j) (Gu.getD j 0)
    -- restore k to its plain value if another prime follows
    if i + 1 < FGlen then
      kk := SmallPrimeNTT.mp_iNTT logn kk igm p p0i
      let mut scv' : UInt32 := (1 : UInt32) <<< (((0 : UInt32) - sc) &&& 31)
      for _ in [:(sc >>> 5).toNat] do
        scv' := SmallPrimeNTT.mp_montymul scv' 1 p p0i
      for j in [:n] do
        kk := kk.set! j
          (SmallPrimeNTT.mp_norm (SmallPrimeNTT.mp_montymul scv' (kk.getD j 0) p p0i) p).toUInt32
  return (depth1FromRNS n F FGlen, depth1FromRNS n G FGlen)

end Falcon.Concrete.PolyBigInt
