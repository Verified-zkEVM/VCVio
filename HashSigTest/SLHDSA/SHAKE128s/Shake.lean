/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module


/-!
# SHAKE256 (FIPS 202), for running the specification on test vectors

Keccak-f[1600] on 25 unboxed lanes, written out round by round for speed.
-/

@[expose] public section

namespace SlhDsaTest

/-- The 25 lanes; lane `(x, y)` is `a(x + 5y)`. -/
structure State where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  a6 : UInt64
  a7 : UInt64
  a8 : UInt64
  a9 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64

def State.zero : State := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- One round of Keccak-f[1600]. -/
@[inline] def round (s : State) (rc : UInt64) : State :=
  let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))
  let d1 := c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))
  let d2 := c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))
  let d3 := c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))
  let d4 := c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))
  let e0 := s.a0 ^^^ d0
  let e1 := s.a1 ^^^ d1
  let e2 := s.a2 ^^^ d2
  let e3 := s.a3 ^^^ d3
  let e4 := s.a4 ^^^ d4
  let e5 := s.a5 ^^^ d0
  let e6 := s.a6 ^^^ d1
  let e7 := s.a7 ^^^ d2
  let e8 := s.a8 ^^^ d3
  let e9 := s.a9 ^^^ d4
  let e10 := s.a10 ^^^ d0
  let e11 := s.a11 ^^^ d1
  let e12 := s.a12 ^^^ d2
  let e13 := s.a13 ^^^ d3
  let e14 := s.a14 ^^^ d4
  let e15 := s.a15 ^^^ d0
  let e16 := s.a16 ^^^ d1
  let e17 := s.a17 ^^^ d2
  let e18 := s.a18 ^^^ d3
  let e19 := s.a19 ^^^ d4
  let e20 := s.a20 ^^^ d0
  let e21 := s.a21 ^^^ d1
  let e22 := s.a22 ^^^ d2
  let e23 := s.a23 ^^^ d3
  let e24 := s.a24 ^^^ d4
  let b0 := e0
  let b1 := ((e6 <<< 44) ||| (e6 >>> 20))
  let b2 := ((e12 <<< 43) ||| (e12 >>> 21))
  let b3 := ((e18 <<< 21) ||| (e18 >>> 43))
  let b4 := ((e24 <<< 14) ||| (e24 >>> 50))
  let b5 := ((e3 <<< 28) ||| (e3 >>> 36))
  let b6 := ((e9 <<< 20) ||| (e9 >>> 44))
  let b7 := ((e10 <<< 3) ||| (e10 >>> 61))
  let b8 := ((e16 <<< 45) ||| (e16 >>> 19))
  let b9 := ((e22 <<< 61) ||| (e22 >>> 3))
  let b10 := ((e1 <<< 1) ||| (e1 >>> 63))
  let b11 := ((e7 <<< 6) ||| (e7 >>> 58))
  let b12 := ((e13 <<< 25) ||| (e13 >>> 39))
  let b13 := ((e19 <<< 8) ||| (e19 >>> 56))
  let b14 := ((e20 <<< 18) ||| (e20 >>> 46))
  let b15 := ((e4 <<< 27) ||| (e4 >>> 37))
  let b16 := ((e5 <<< 36) ||| (e5 >>> 28))
  let b17 := ((e11 <<< 10) ||| (e11 >>> 54))
  let b18 := ((e17 <<< 15) ||| (e17 >>> 49))
  let b19 := ((e23 <<< 56) ||| (e23 >>> 8))
  let b20 := ((e2 <<< 62) ||| (e2 >>> 2))
  let b21 := ((e8 <<< 55) ||| (e8 >>> 9))
  let b22 := ((e14 <<< 39) ||| (e14 >>> 25))
  let b23 := ((e15 <<< 41) ||| (e15 >>> 23))
  let b24 := ((e21 <<< 2) ||| (e21 >>> 62))
  ⟨(b0 ^^^ ((~~~ b1) &&& b2)) ^^^ rc,
   b1 ^^^ ((~~~ b2) &&& b3),
   b2 ^^^ ((~~~ b3) &&& b4),
   b3 ^^^ ((~~~ b4) &&& b0),
   b4 ^^^ ((~~~ b0) &&& b1),
   b5 ^^^ ((~~~ b6) &&& b7),
   b6 ^^^ ((~~~ b7) &&& b8),
   b7 ^^^ ((~~~ b8) &&& b9),
   b8 ^^^ ((~~~ b9) &&& b5),
   b9 ^^^ ((~~~ b5) &&& b6),
   b10 ^^^ ((~~~ b11) &&& b12),
   b11 ^^^ ((~~~ b12) &&& b13),
   b12 ^^^ ((~~~ b13) &&& b14),
   b13 ^^^ ((~~~ b14) &&& b10),
   b14 ^^^ ((~~~ b10) &&& b11),
   b15 ^^^ ((~~~ b16) &&& b17),
   b16 ^^^ ((~~~ b17) &&& b18),
   b17 ^^^ ((~~~ b18) &&& b19),
   b18 ^^^ ((~~~ b19) &&& b15),
   b19 ^^^ ((~~~ b15) &&& b16),
   b20 ^^^ ((~~~ b21) &&& b22),
   b21 ^^^ ((~~~ b22) &&& b23),
   b22 ^^^ ((~~~ b23) &&& b24),
   b23 ^^^ ((~~~ b24) &&& b20),
   b24 ^^^ ((~~~ b20) &&& b21)⟩

def keccakF (s : State) : State := Id.run do
  let mut s := s
  for rc in roundConstants do
    s := round s rc
  return s

/-- XOR `value` into lane `i`. -/
def State.xorLane (s : State) (i : Nat) (value : UInt64) : State :=
  match i with
  | 0 => { s with a0 := s.a0 ^^^ value }
  | 1 => { s with a1 := s.a1 ^^^ value }
  | 2 => { s with a2 := s.a2 ^^^ value }
  | 3 => { s with a3 := s.a3 ^^^ value }
  | 4 => { s with a4 := s.a4 ^^^ value }
  | 5 => { s with a5 := s.a5 ^^^ value }
  | 6 => { s with a6 := s.a6 ^^^ value }
  | 7 => { s with a7 := s.a7 ^^^ value }
  | 8 => { s with a8 := s.a8 ^^^ value }
  | 9 => { s with a9 := s.a9 ^^^ value }
  | 10 => { s with a10 := s.a10 ^^^ value }
  | 11 => { s with a11 := s.a11 ^^^ value }
  | 12 => { s with a12 := s.a12 ^^^ value }
  | 13 => { s with a13 := s.a13 ^^^ value }
  | 14 => { s with a14 := s.a14 ^^^ value }
  | 15 => { s with a15 := s.a15 ^^^ value }
  | 16 => { s with a16 := s.a16 ^^^ value }
  | 17 => { s with a17 := s.a17 ^^^ value }
  | 18 => { s with a18 := s.a18 ^^^ value }
  | 19 => { s with a19 := s.a19 ^^^ value }
  | 20 => { s with a20 := s.a20 ^^^ value }
  | 21 => { s with a21 := s.a21 ^^^ value }
  | 22 => { s with a22 := s.a22 ^^^ value }
  | 23 => { s with a23 := s.a23 ^^^ value }
  | 24 => { s with a24 := s.a24 ^^^ value }
  | _ => s

def State.lane (s : State) (i : Nat) : UInt64 :=
  match i with
  | 0 => s.a0
  | 1 => s.a1
  | 2 => s.a2
  | 3 => s.a3
  | 4 => s.a4
  | 5 => s.a5
  | 6 => s.a6
  | 7 => s.a7
  | 8 => s.a8
  | 9 => s.a9
  | 10 => s.a10
  | 11 => s.a11
  | 12 => s.a12
  | 13 => s.a13
  | 14 => s.a14
  | 15 => s.a15
  | 16 => s.a16
  | 17 => s.a17
  | 18 => s.a18
  | 19 => s.a19
  | 20 => s.a20
  | 21 => s.a21
  | 22 => s.a22
  | 23 => s.a23
  | 24 => s.a24
  | _ => 0

/-- SHAKE256 with `outputBytes` bytes of output. -/
def shake256 (input : ByteArray) (outputBytes : Nat) : ByteArray := Id.run do
  let rate := 136
  let padLength := rate - input.size % rate
  let mut padded := input
  for i in [0:padLength] do
    let byte : UInt8 :=
      (if i = 0 then 0x1F else 0) ||| (if i = padLength - 1 then 0x80 else 0)
    padded := padded.push byte
  let mut state := State.zero
  for blockIndex in [0:padded.size / rate] do
    for i in [0:rate / 8] do
      let mut lane : UInt64 := 0
      for j in [0:8] do
        lane := lane ||| (padded[blockIndex * rate + 8 * i + j]!.toUInt64 <<< (8 * j).toUInt64)
      state := state.xorLane i lane
    state := keccakF state
  let mut out := ByteArray.empty
  while out.size < outputBytes do
    for i in [0:rate / 8] do
      for j in [0:8] do
        if out.size < outputBytes then
          out := out.push (state.lane i >>> (8 * j).toUInt64).toUInt8
    if out.size < outputBytes then
      state := keccakF state
  return out

end SlhDsaTest
