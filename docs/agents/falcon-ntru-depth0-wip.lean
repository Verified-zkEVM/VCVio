/-
WIP (s13) — `solve_NTRU_depth0` port attempt. NOT merged: compiles, but END-TO-END
VALIDATION FAILS (see findings below). Preserved for the next session to debug from.
Drop this body back into `LatticeCrypto/Falcon/Concrete/NTRUSolver.lean` (replacing the
`sorry` at `solve_NTRU_depth0`) once the lift/convention bug is found.

Faithful line-by-line port of c-fn-dsa `kgen_ntru.c:1575-1766` (NON-AVX2
`solve_NTRU_depth0`). Every helper signature was verified against live source (s13).

=== STATUS: BUGGY — DO NOT MERGE AS-IS ===

What works:
- Compiles clean (no new sorry); `#print axioms` would be {propext, Quot.sound, sorryAx-from-intermediate-only}.
- `solve_NTRU_deepest` runs and succeeds for 476/2401 small (f,g) at logn=1 (those with
  coprime algebraic norms N(f)=f₀²+f₁², N(g)=g₀²+g₁²) — so deepest is reachable.
- The internal verify gate (`x != rv → none`) makes the whole thing SAFE: no wrong (F,G)
  ever escapes; every tested input ends in `none`. Safe but non-functional.

What fails (the bug):
- Full pipeline `deepest → depth0 → poly_big_to_small` at logn=1 (n=2) yields `solved=0`
  over all 7⁴ small inputs. The C driver (`kgen_ntru.c:2003`, `while (depth-->1)` is empty
  for logn=1) confirms deepest feeds depth0 DIRECTLY with no intermediate — so the logn=1
  test path is faithful and the bug is real.
- Two failure modes observed:
  * `[1,2]/[0,1]`: deepest OK (Fd=49156=4·q, Gd=0) → depth0 returns `none` (verify reject).
  * `[0,1]/[1,2]`: depth0 returns `some` but raw F,G words = #[-2048, 4096, 0, -2049]
    (NOT reduced to ±127) → `poly_big_to_small` rejects (okF=false).
  So the Babai reduction leaves (F,G) un-reduced and/or the deeper (F,G) convention from
  `deepest` is not what depth0's lift expects.

Prime suspects (debug next session — compile the C backend and differential-trace BOTH
functions on identical inputs, comparing intermediate buffers):
1. `solve_NTRU_deepest` output convention. It was NEVER runtime-validated before s13 (the
   whole pipeline was sorry). Fd=4·q, Gd=0 for [1,2]/[0,1] does not satisfy the naive
   scalar `N(f)·G − N(g)·F = q` (5·0 − 1·49156 = −49156 ≠ q). The degree-1 solution's
   convention (sign, scaling, which of F/G, 31-bit-limb vs 32-bit) may mismatch depth0's
   `poly_mp_set` read (which uses `.toInt32`, i.e. 32-bit sign in bit 31, whereas big-int
   limbs carry the sign in bit 30 — a likely mismatch for NEGATIVE deeper values).
2. `mp_NTT (logn-1)` on the degree-hn deeper (F,G) reusing the logn-sized `gm`: confirm the
   Lean `mp_NTT` indexes a larger `gm` the same way C does for a smaller logn (C relies on
   this at :1610-1611). For logn=1 this is `mp_NTT 0` = identity, so NOT the n=2 culprit.
3. The FXR division `<<< 22` downscale + `vect_div_selfadj_fft` arg order — re-derive the
   fixed-point scale end-to-end (numerator t1 / denominator t2, both ×2^22, quotient at 2^32).
4. The verify gate's `x = f·G − g·F` uses the just-updated Fp[i]/Gp[i] (ordering is correct
   in this port) and compares to `rv = q·R mod p` — confirm `rv` and the Montgomery
   conventions of `mp_montymul(k_mont, f_ntt)` match C exactly.

Recommended next step: build the C backend (`csrc/falcon/fndsa.c`, now that the submodule is
initialized), expose `solve_NTRU_deepest`/`solve_NTRU_depth0` via a tiny harness, and compare
buffer contents word-for-word against the Lean versions on a single fixed (f,g) at logn=2.
That localises whether deepest or depth0 (or both) diverges, and at which step.
-/

-- The implementation attempt (s13). Paste over the `sorry` body once fixed.
example : True := trivial  -- placeholder so this file is self-contained/parses
/-
def solve_NTRU_depth0 (logn : Nat) (f g : Array Int8)
    (buf : Array UInt32) : Option (Array UInt32) := Id.run do
  let n := 1 <<< logn
  let hn := n >>> 1
  let pr := SmallPrimeNTT.PRIMES.getD 0 default
  let p := pr.p
  let p0i := pr.p0i
  let R2 := pr.R2
  let gm := SmallPrimeNTT.mp_mkgm logn pr.g p p0i
  let igm := mkigm logn pr

  -- Load f, g into RNS+NTT; grab the deeper (F, G) before overwriting.
  let Fd0 := extractRange buf 0 hn
  let Gd0 := extractRange buf hn hn
  let mut ft := SmallPrimeNTT.mp_NTT logn
    (SmallPrimeNTT.mp_set_small logn f p) gm p p0i
  let mut gt := SmallPrimeNTT.mp_NTT logn
    (SmallPrimeNTT.mp_set_small logn g p) gm p p0i
  -- Deeper (F, G) have degree hn: convert with `logn - 1`, reusing `gm`.
  let Fd := SmallPrimeNTT.mp_NTT (logn - 1)
    (SmallPrimeNTT.poly_mp_set (logn - 1) Fd0 p) gm p p0i
  let Gd := SmallPrimeNTT.mp_NTT (logn - 1)
    (SmallPrimeNTT.poly_mp_set (logn - 1) Gd0 p) gm p p0i

  -- Build the unreduced (F, G) into ft, gt.
  for i in [:hn] do
    let fa := getU32 ft (2 * i)
    let fb := getU32 ft (2 * i + 1)
    let ga := getU32 gt (2 * i)
    let gb := getU32 gt (2 * i + 1)
    let mFd := SmallPrimeNTT.mp_montymul (getU32 Fd i) R2 p p0i
    let mGd := SmallPrimeNTT.mp_montymul (getU32 Gd i) R2 p p0i
    ft := ft.set! (2 * i) (SmallPrimeNTT.mp_montymul gb mFd p p0i)
    ft := ft.set! (2 * i + 1) (SmallPrimeNTT.mp_montymul ga mFd p p0i)
    gt := gt.set! (2 * i) (SmallPrimeNTT.mp_montymul fb mGd p p0i)
    gt := gt.set! (2 * i + 1) (SmallPrimeNTT.mp_montymul fa mGd p p0i)

  let mut Fp := ft
  let mut Gp := gt
  let mut t1 : Array UInt32 := Array.replicate n 0
  let mut t2 : Array UInt32 := Array.replicate n 0
  let mut t3 : Array UInt32 := Array.replicate n 0

  -- t1 ← F·adj(f) + G·adj(g),  t3 ← f·adj(f) + g·adj(g)  (RNS+NTT).
  let mut t4 := SmallPrimeNTT.mp_NTT logn
    (SmallPrimeNTT.mp_set_small logn f p) gm p p0i
  for i in [:n] do
    let w := SmallPrimeNTT.mp_montymul (getU32 t4 (n - 1 - i)) R2 p p0i
    t1 := t1.set! i (SmallPrimeNTT.mp_montymul w (getU32 Fp i) p p0i)
    t3 := t3.set! i (SmallPrimeNTT.mp_montymul w (getU32 t4 i) p p0i)
  t4 := SmallPrimeNTT.mp_NTT logn
    (SmallPrimeNTT.mp_set_small logn g p) gm p p0i
  for i in [:n] do
    let w := SmallPrimeNTT.mp_montymul (getU32 t4 (n - 1 - i)) R2 p p0i
    t1 := t1.set! i (SmallPrimeNTT.mp_add (getU32 t1 i)
      (SmallPrimeNTT.mp_montymul w (getU32 Gp i) p p0i) p)
    t3 := t3.set! i (SmallPrimeNTT.mp_add (getU32 t3 i)
      (SmallPrimeNTT.mp_montymul w (getU32 t4 i) p p0i) p)

  -- Back to plain representation; move f·adj(f) + g·adj(g) into t2.
  t1 := SmallPrimeNTT.mp_iNTT logn t1 igm p p0i
  t3 := SmallPrimeNTT.mp_iNTT logn t3 igm p p0i
  for i in [:n] do
    t1 := t1.set! i (SmallPrimeNTT.mp_norm (getU32 t1 i) p).toUInt32
    t2 := t2.set! i (SmallPrimeNTT.mp_norm (getU32 t3 i) p).toUInt32

  -- FFT-divide t1 by t2 (downscaled by 2^10) and round into t1 (RNS).
  -- t2 is self-adjoint, so its FFT only needs the half-size head.
  let mut rt3 : Array FXR := Array.replicate n 0
  for i in [:n] do
    let x : UInt64 := (getU32 t2 i).toInt32.toInt64.toUInt64 <<< 22
    rt3 := rt3.set! i (fxr_of_scaled32 x)
  rt3 := vect_FFT logn rt3
  let rt2 := rt3.extract 0 hn
  let mut rt3b : Array FXR := Array.replicate n 0
  for i in [:n] do
    let x : UInt64 := (getU32 t1 i).toInt32.toInt64.toUInt64 <<< 22
    rt3b := rt3b.set! i (fxr_of_scaled32 x)
  rt3b := vect_FFT logn rt3b
  rt3b := vect_div_selfadj_fft logn rt3b rt2
  rt3b := vect_iFFT logn rt3b
  for i in [:n] do
    t1 := t1.set! i (SmallPrimeNTT.mp_set (fxr_round (rt3b.getD i 0)) p)

  -- Convert k to RNS+NTT+Montgomery.
  t1 := SmallPrimeNTT.mp_NTT logn t1 gm p p0i
  for i in [:n] do
    t1 := t1.set! i (SmallPrimeNTT.mp_montymul (getU32 t1 i) R2 p p0i)

  -- Subtract k·f from F, k·g from G; verify f·G − g·F ≡ q·R per slot.
  for i in [:n] do
    t2 := t2.set! i (SmallPrimeNTT.mp_set (f.getD i 0).toInt32 p)
    t3 := t3.set! i (SmallPrimeNTT.mp_set (g.getD i 0).toInt32 p)
  t2 := SmallPrimeNTT.mp_NTT logn t2 gm p p0i
  t3 := SmallPrimeNTT.mp_NTT logn t3 gm p p0i
  let rv := SmallPrimeNTT.mp_montymul Q 1 p p0i
  for i in [:n] do
    let kf := SmallPrimeNTT.mp_montymul (getU32 t1 i) (getU32 t2 i) p p0i
    let kg := SmallPrimeNTT.mp_montymul (getU32 t1 i) (getU32 t3 i) p p0i
    Fp := Fp.set! i (SmallPrimeNTT.mp_sub (getU32 Fp i) kf p)
    Gp := Gp.set! i (SmallPrimeNTT.mp_sub (getU32 Gp i) kg p)
    let x := SmallPrimeNTT.mp_sub
      (SmallPrimeNTT.mp_montymul (getU32 t2 i) (getU32 Gp i) p p0i)
      (SmallPrimeNTT.mp_montymul (getU32 t3 i) (getU32 Fp i) p p0i) p
    if x != rv then
      return none

  -- Back to normal representation, normalized.
  Fp := SmallPrimeNTT.mp_iNTT logn Fp igm p p0i
  Gp := SmallPrimeNTT.mp_iNTT logn Gp igm p p0i
  Fp := SmallPrimeNTT.poly_mp_norm logn Fp p
  Gp := SmallPrimeNTT.poly_mp_norm logn Gp p

  let mut result := ensureSize buf (2 * n)
  result := writeRange result 0 Fp
  result := writeRange result n Gp
  return some result
-/
