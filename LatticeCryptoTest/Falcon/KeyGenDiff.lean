/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import LatticeCryptoTest.Falcon.Helpers
public import Extern.Falcon.KeyGen

/-!
# Differential test: Lean Falcon key generation against c-fn-dsa

Runs the pure-Lean seeded key generator `Falcon.Concrete.KeyGen.keyGen` (Gaussian sampling,
NTRU equation solver, public-key computation) and encodes its output exactly as c-fn-dsa's
`keygen_inner` does: the signing key is the header byte `0x50 + logn` followed by the
trimmed encodings of `f`, `g` and `F`, and the verifying key is the header byte `logn`
followed by the 14-bit packing of `h`. Both byte strings are compared with the output of
`fndsa_keygen_seeded`, reached through the FFI bindings `falcon512KeygenSeeded` and
`falcon1024KeygenSeeded`.
-/

public section

namespace Falcon.Test.KeyGenDiff

open Falcon.Concrete

/-- Bit width used for `f` and `g` in the c-fn-dsa signing-key encoding. -/
def fgBits (logn : Nat) : Nat :=
  if logn ≤ 5 then 8 else if logn ≤ 7 then 7 else if logn ≤ 9 then 6 else 5

/-- Pack the low `nbits` bits of each coefficient, most significant bit first, as
c-fn-dsa's `trim_i8_encode` does. -/
def trimI8Encode (f : Array Int8) (nbits : Nat) : ByteArray := Id.run do
  let mask : UInt32 := ((1 : UInt32) <<< nbits.toUInt32) - 1
  let mut out := ByteArray.empty
  let mut acc : UInt32 := 0
  let mut accLen : Nat := 0
  for x in f do
    acc := (acc <<< nbits.toUInt32) ||| (x.toInt32.toUInt32 &&& mask)
    accLen := accLen + nbits
    if accLen ≥ 8 then
      accLen := accLen - 8
      out := out.push (acc >>> accLen.toUInt32).toUInt8
  return out

/-- Pack coefficients in `[0, q)` on 14 bits each, as c-fn-dsa's `mqpoly_encode` does. -/
def mqpolyEncode (h : Array UInt16) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for b in [:h.size / 4] do
    let h0 := (h.getD (4 * b) 0).toUInt32
    let h1 := (h.getD (4 * b + 1) 0).toUInt32
    let h2 := (h.getD (4 * b + 2) 0).toUInt32
    let h3 := (h.getD (4 * b + 3) 0).toUInt32
    out := out.push (h0 >>> 6).toUInt8
    out := out.push ((h0 <<< 2) ||| (h1 >>> 12)).toUInt8
    out := out.push (h1 >>> 4).toUInt8
    out := out.push ((h1 <<< 4) ||| (h2 >>> 10)).toUInt8
    out := out.push (h2 >>> 2).toUInt8
    out := out.push ((h2 <<< 6) ||| (h3 >>> 8)).toUInt8
    out := out.push h3.toUInt8
  return out

/-- Run the Lean key generator from `seed` and encode `(signing key, verifying key)` in the
c-fn-dsa wire format. -/
def leanKeygenSeeded (logn : Nat) (seed : ByteArray) : Option (ByteArray × ByteArray) := do
  let kp ← KeyGen.keyGen logn seed
  let nbits := fgBits logn
  let sk := ByteArray.mk #[(0x50 + logn).toUInt8] ++ trimI8Encode kp.f nbits ++
    trimI8Encode kp.g nbits ++ trimI8Encode kp.capF 8
  let pk := ByteArray.mk #[logn.toUInt8] ++ mqpolyEncode kp.h
  pure (sk, pk)

/-- Index of the first differing byte of two byte arrays (the shorter length if one is a
prefix of the other), or `none` if they are equal. -/
def firstDiff (a b : ByteArray) : Option Nat := Id.run do
  for i in [:min a.size b.size] do
    if a[i]! != b[i]! then return some i
  if a.size != b.size then return some (min a.size b.size)
  return none

/-- A deterministic seed of `len` bytes derived from a label byte. -/
def testSeed (label : UInt8) (len : Nat := 48) : ByteArray :=
  ⟨(Array.range len).map fun i => (i.toUInt8 * 37 + label * 101 + 7)⟩

/-- Compare the Lean and FFI key generators on one seed. -/
def checkSeed (st : IO.Ref TestState) (logn : Nat) (label : UInt8)
    (ffi : ByteArray → ByteArray × ByteArray) : IO Unit := do
  let seed := testSeed label
  let (skC, pkC) := ffi seed
  match leanKeygenSeeded logn seed with
  | none => check st s!"logn={logn} seed#{label}: Lean keygen succeeds" false
  | some (skL, pkL) =>
    check st s!"logn={logn} seed#{label}: signing key byte-identical ({skC.size} bytes)"
      (skL == skC) s!"first diff at byte {firstDiff skL skC}"
    check st s!"logn={logn} seed#{label}: verifying key byte-identical ({pkC.size} bytes)"
      (pkL == pkC) s!"first diff at byte {firstDiff pkL pkC}"

/-- Differential key-generation tests at Falcon-512 and Falcon-1024. -/
def runFalconKeyGenDiffTests (st : IO.Ref TestState) : IO Unit := do
  IO.println "Lean keygen vs c-fn-dsa fndsa_keygen_seeded (byte-exact sk/pk)"
  for label in [0, 1, 2, 3, 4, 5, 6, 7] do
    checkSeed st 9 label FFI.falcon512KeygenSeeded
  for label in [0, 1, 2, 3] do
    checkSeed st 10 label FFI.falcon1024KeygenSeeded
  IO.println ""

end Falcon.Test.KeyGenDiff
