/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSealBridge
public meta import VCVio.Schemes.PointerChainPuzzle.LeanSealBridge

/-!
# leanSeal over one random oracle: checks

Checks of `route` on the hash input of a typed point of every family, and on byte strings outside
the image of `hashInput`: wrong lengths, an unknown label, a label with the wrong length prefix,
and 52-byte strings whose chain index is out of range or zero (the last one reads as a chain step
when the index is decoded with truncated subtraction, but it is no hash input). Then the mask split
at `b = 7` and at `b = 32`, where the tail is the single byte string of length zero.
-/

public section

open PointerChainPuzzle.LeanSeal

namespace VCVioTest.LeanSealBridge

/-- The byte string of length `k` with every byte `c`. -/
def fill (k : ℕ) (c : UInt8) : Bytes k := ⟨Vector.replicate k c⟩

/-- The bytes `0, 1, …, 31`. -/
def iota32 : Bytes 32 := ⟨Vector.ofFn fun i => i.val.toUInt8⟩

/-! ## `route` on hash inputs -/

/-- A chain start, for `b = 7` and four chains. -/
def startPoint : TypedPoint 7 4 := .start (fill 32 1) 2 (fill 7 2)

/-- A chain step. -/
def stepPoint : TypedPoint 7 4 := .step (fill 16 3) 3 (fill 32 4)

/-- A mask. -/
def maskPoint : TypedPoint 7 4 := .mask (fill 32 5) (fill 32 6)

/-- An accumulator step. -/
def accPoint : TypedPoint 7 4 := .acc (fill 32 7) (fill 32 8)

/-- A key derivation. -/
def keyPoint : TypedPoint 7 4 := .key (fill 32 9) (fill 32 10)

/-- A commitment. -/
def commitPoint : TypedPoint 7 4 := .commit (fill 32 11) (fill 32 12)

-- `route` reads every family back from its hash input.
/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [route (hashInput startPoint) == some startPoint,
  route (hashInput stepPoint) == some stepPoint,
  route (hashInput maskPoint) == some maskPoint,
  route (hashInput accPoint) == some accPoint,
  route (hashInput keyPoint) == some keyPoint,
  route (hashInput commitPoint) == some commitPoint]

/-- Chain steps are exactly 52 bytes. -/
example : (hashInput stepPoint).size = 52 := rfl

-- Labelled inputs are at least 55 bytes (SPEC §3): start, mask, acc, key, commit.
/-- info: [61, 81, 80, 80, 83] -/
#guard_msgs in
#eval [startPoint, maskPoint, accPoint, keyPoint, commitPoint].map fun t => (hashInput t).size

/-- The same for every point, from the general theorem. -/
example (t : TypedPoint 7 4) : route (hashInput t) = some t := route_hashInput (by norm_num) t

/-! ## `route` outside the image -/

-- Wrong lengths: empty, 51 bytes, 53 bytes.
/-- info: [true, true, true] -/
#guard_msgs in
#eval [ByteArray.empty, ⟨Array.replicate 51 0⟩, ⟨Array.replicate 53 0⟩].map fun x =>
  (route (b := 7) (n := 4) x).isNone

-- 52-byte strings with index field `5`, out of range for four chains, and `0`: index fields hold
-- `i + 1`, so the second one is no hash input although it reads as chain `0` under truncated
-- subtraction.
/-- info: [true, true] -/
#guard_msgs in
#eval [5, 0].map fun j =>
  (route (b := 7) (n := 4) ((fill 32 4).toByteArray ++ (fill 16 3).toByteArray ++ be 4 j)).isNone

-- An unknown label, a known label with a field missing, and a known label with the wrong length
-- prefix.
/-- info: [true, true, true] -/
#guard_msgs in
#eval [labelled "leanseal/v1/other" ((fill 32 1).toByteArray ++ (fill 32 2).toByteArray),
  labelled "leanseal/v1/acc" (fill 32 1).toByteArray,
  ByteArray.mk #[14] ++ "leanseal/v1/acc".toUTF8 ++ (fill 32 7).toByteArray ++
    (fill 32 8).toByteArray].map fun x => (route (b := 7) (n := 4) x).isNone

/-- Every byte string that is no hash input routes to `none`, from the general theorem. -/
example (x : ByteArray) (h : ∀ t : TypedPoint 7 4, hashInput t ≠ x) :
    route (b := 7) (n := 4) x = none :=
  (route_eq_none_iff (by norm_num) x).2 h

/-! ## The mask split -/

-- At `b = 7`: the first 7 bytes, and the last 25 as the tail.
/-- info: ([0, 1, 2, 3, 4, 5, 6], [7, 8, 9], [29, 30, 31]) -/
#guard_msgs in
#eval let p := splitMask (b := 7) (by norm_num) iota32
  (p.1.toList, p.2.toList.take 3, p.2.toList.drop 22)

-- At `b = 7` the split is undone by joining.
/-- info: true -/
#guard_msgs in
#eval (splitMask (b := 7) (by norm_num)).symm (splitMask (b := 7) (by norm_num) iota32) == iota32

-- At `b = 32`: the whole value and the empty tail.
/-- info: (true, []) -/
#guard_msgs in
#eval let p := splitMask (b := 32) le_rfl iota32; (p.1 == iota32, p.2.toList)

/-- At `b = 32` the tail of the mask split is the single byte string of length zero. -/
example (u v : Bytes (32 - 32)) : u = v :=
  Bytes.ext_getElem fun _ hi => absurd hi (by omega)

/-- The encoding reads a mask answer as the first `b` bytes of the 32-byte value. -/
example (ctx y w : Bytes 32) :
    (encoding (b := 7) (n := 4) (by norm_num) (by norm_num)).trunc (.mask ctx y) w = w.take :=
  encoding_trunc _ _ _ _

end VCVioTest.LeanSealBridge
