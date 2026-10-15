/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Polynomial CRC state updates on byte-aligned messages

The equations here transcribe the polynomial component of Foundation's
`shared/CRC/Main.cry` at revision `7d0528bd998682788f4e23661f2829298f9e47db`:
`expandedData = (pack data # zero) ^ (state # zero)` followed by `pmod`.
Big-endian concatenation is multiplication by a power of X followed by addition
over GF(2). Input reflection reverses each byte separately. Message types enforce
byte alignment, which Foundation's reflected profiles require at runtime.

The update theorem covers arbitrary monic generators and initial states, and any
final observation (including XOR and output reflection). It is a theorem about
these explicit polynomial equations, not a checked elaboration certificate for
the imported Cryptol definitions or a bitvector implementation of `pmod`.
-/

public section

namespace Interop.Cryptol.Bridge.CRC

open Polynomial

/-- Binary polynomials model Cryptol's polynomial bitvector arithmetic. -/
abbrev BinaryPolynomial := Polynomial (ZMod 2)

/-- One byte in source bit order. -/
abbrev Byte := Fin 8 → Bool

/-- Interpret a big-endian bit string as a polynomial over GF(2). -/
@[expose] noncomputable def encode : List Bool → BinaryPolynomial
  | [] => 0
  | b :: bs => C (if b then 1 else 0) * X ^ bs.length + encode bs

/-- Concatenation shifts the left polynomial by the length of the right string. -/
theorem encode_append (xs ys : List Bool) :
    encode (xs ++ ys) = encode xs * X ^ ys.length + encode ys := by
  induction xs with
  | nil => simp [encode]
  | cons b bs ih =>
      simp only [List.cons_append, encode, List.length_append, ih, pow_add]
      ring

/-- Pack bytes with optional per-byte reflection, never reversing byte order. -/
@[expose] def pack (reflected : Bool) (bytes : List Byte) : List Bool :=
  bytes.flatMap fun byte =>
    let bits := List.ofFn byte
    if reflected then bits.reverse else bits

/-- Packing preserves byte concatenation in both reflected and ordinary profiles. -/
theorem pack_append (reflected : Bool) (xs ys : List Byte) :
    pack reflected (xs ++ ys) = pack reflected xs ++ pack reflected ys := by
  simp [pack]

/-- Every packed message has exactly eight bits per byte. -/
theorem pack_length (reflected : Bool) (bytes : List Byte) :
    (pack reflected bytes).length = 8 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      simp only [pack, List.flatMap_cons, List.length_append] at *
      cases reflected <;> simp_all [Nat.mul_add, Nat.add_comm]

/-- Polynomial remainder update for a message polynomial and its bit length. -/
@[expose] noncomputable def step (generator : BinaryPolynomial) (width : Nat)
    (state : BinaryPolynomial) (length : Nat) (data : BinaryPolynomial) : BinaryPolynomial :=
  (data * X ^ width + state * X ^ length) %ₘ generator

/-- Remainders can be retained between polynomial message fragments. -/
theorem step_append (generator : BinaryPolynomial) (monic : generator.Monic)
    (width a b : Nat) (state x y : BinaryPolynomial) :
    step generator width (step generator width state a x) b y =
      step generator width state (a + b) (x * X ^ b + y) := by
  unfold step
  apply modByMonic_eq_of_dvd_sub monic
  have h : generator ∣
      (x * X ^ width + state * X ^ a) %ₘ generator -
        (x * X ^ width + state * X ^ a) := by
    rw [modByMonic_eq_sub_mul_div]
    convert dvd_neg.mpr (dvd_mul_right generator
      ((x * X ^ width + state * X ^ a) /ₘ generator)) using 1
    ring
  convert dvd_mul_of_dvd_left h (X ^ b) using 1
  rw [pow_add]
  ring

/-- Update a running state using a byte-aligned message. -/
@[expose] noncomputable def update (generator : BinaryPolynomial) (width : Nat) (reflected : Bool)
    (state : BinaryPolynomial) (bytes : List Byte) : BinaryPolynomial :=
  step generator width state (8 * bytes.length) (encode (pack reflected bytes))

/-- Processing two byte strings incrementally is identical to processing their concatenation. -/
theorem update_append (generator : BinaryPolynomial) (monic : generator.Monic)
    (width : Nat) (reflected : Bool) (state : BinaryPolynomial) (xs ys : List Byte) :
    update generator width reflected (update generator width reflected state xs) ys =
      update generator width reflected state (xs ++ ys) := by
  simp only [update, pack_append, encode_append, pack_length, List.length_append, Nat.mul_add]
  exact step_append generator monic width _ _ state _ _

/-- The incremental CRC law survives any final XOR/reflection observation of the state. -/
theorem finalize_update_append {α : Type*} (finalize : BinaryPolynomial → α)
    (generator : BinaryPolynomial) (monic : generator.Monic)
    (width : Nat) (reflected : Bool) (initial : BinaryPolynomial) (xs ys : List Byte) :
    finalize (update generator width reflected
      (update generator width reflected initial xs) ys) =
      finalize (update generator width reflected initial (xs ++ ys)) := by
  rw [update_append generator monic]

end Interop.Cryptol.Bridge.CRC
