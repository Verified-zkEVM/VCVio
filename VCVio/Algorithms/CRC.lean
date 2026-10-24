/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.BitVec

/-!
# Executable CRC registers

A width-indexed register processes bytes in source order. The generator's leading
coefficient is implicit; `polynomial` stores its lower coefficients. Reflection
reverses bits within each input byte, and final reflection applies after the XOR
mask. Running state is kept separate from the finalized checksum so a finalized
checksum is never fed back into an incremental update.

The append laws follow from the register fold. They make no claim about a source
language implementation or cryptographic security.
-/

public section

namespace VCVio.Algorithms.Crc

/-- Parameters of a CRC register with an implicit monic generator. -/
structure Parameters (width : Nat) where
  /-- Lower coefficients of the degree-`width` generator, in big-endian word order. -/
  polynomial : BitVec width
  /-- Initial, unfinalized register. -/
  initial : BitVec width
  /-- Reverse bits within each input byte before processing it. -/
  reflectInput : Bool
  /-- Reverse the finalized result's bits. -/
  reflectOutput : Bool
  /-- XOR mask applied before output reflection. -/
  xorMask : BitVec width
  deriving DecidableEq, Repr

/-- Update the register with one input bit. -/
@[expose] def step {width : Nat} (polynomial state : BitVec width) (bit : Bool) : BitVec width :=
  (state <<< 1) ^^^ (if state.getMsbD 0 != bit then polynomial else 0)

/-- Update with one byte, retaining the unfinalized register. -/
@[expose] def updateByte {width : Nat} (parameters : Parameters width)
    (state : BitVec width) (byte : BitVec 8) : BitVec width :=
  (List.range 8).foldl (fun state i => step parameters.polynomial state
    (if parameters.reflectInput then byte.getLsbD i else byte.getMsbD i)) state

/-- Update with a byte string, retaining the unfinalized register. -/
@[expose] def update {width : Nat} (parameters : Parameters width)
    (state : BitVec width) (bytes : List (BitVec 8)) : BitVec width :=
  bytes.foldl (updateByte parameters) state

/-- Finalization is an observation of the running state. -/
@[expose] def finalize {width : Nat} (parameters : Parameters width)
    (state : BitVec width) : BitVec width :=
  let masked := state ^^^ parameters.xorMask
  if parameters.reflectOutput then masked.reverse else masked

/-- A source-shaped update result separates the checksum from resumable state. -/
structure Result (width : Nat) where
  /-- Final checksum of the bytes processed so far. -/
  crc : BitVec width
  /-- Register to use for the next chunk. -/
  state : BitVec width
  deriving DecidableEq, Repr

/-- Process one chunk and expose both the checksum and resumable register. -/
@[expose] def updateResult {width : Nat} (parameters : Parameters width)
    (state : BitVec width) (bytes : List (BitVec 8)) : Result width :=
  let state := update parameters state bytes
  ⟨finalize parameters state, state⟩

/-- Compute a checksum from the configured initial register. -/
@[expose] def checksum {width : Nat} (parameters : Parameters width)
    (bytes : List (BitVec 8)) : BitVec width :=
  (updateResult parameters parameters.initial bytes).crc

@[simp] theorem update_nil {width : Nat} (parameters : Parameters width) (state : BitVec width) :
    update parameters state [] = state := rfl

/-- Arbitrary chunking preserves the running register. -/
theorem update_append {width : Nat} (parameters : Parameters width)
    (state : BitVec width) (xs ys : List (BitVec 8)) :
    update parameters state (xs ++ ys) = update parameters (update parameters state xs) ys := by
  exact List.foldl_append

/-- Chunking preserves both observable fields of the update result. -/
theorem updateResult_append {width : Nat} (parameters : Parameters width)
    (state : BitVec width) (xs ys : List (BitVec 8)) :
    updateResult parameters state (xs ++ ys) =
      updateResult parameters (updateResult parameters state xs).state ys := by
  simp only [updateResult, update_append]

/-- Checksum computation from the standard byte container. -/
@[expose] def checksumBytes {width : Nat} (parameters : Parameters width)
    (bytes : ByteArray) : BitVec width :=
  checksum parameters (bytes.data.toList.map UInt8.toBitVec)

end VCVio.Algorithms.Crc
