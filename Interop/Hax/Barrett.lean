/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Hax
public import Interop.Rust.RustM
public import Interop.Rust.Triple
public import VCVio.ProgramLogic.Unary.WP.Necessary

/-!
# A Rust Barrett reduction, through `RustM`, in VCVio

hax's `barrett` example: signed Barrett reduction modulo ML-KEM's prime `3329`.

```rust
const BARRETT_SHIFT: i64 = 26;
const BARRETT_R: i64 = 0x4000000; // 2^26
const BARRETT_MULTIPLIER: i64 = 20159;
pub(crate) const FIELD_MODULUS: i32 = 3329;

#[hax::requires((i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R))]
#[hax::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS &&
                   result.rem_euclid(FIELD_MODULUS) == value.rem_euclid(FIELD_MODULUS))]
pub fn barrett_reduce(value: FieldElement) -> FieldElement {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);
    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;
    let sub = quotient * FIELD_MODULUS;
    value - sub
}
```

`barrett_reduce` below is that function in the `RustM` code hax emits today, over Aeneas's
scalars: the widening casts are pure, and the arithmetic and shifts are checked. It is a
transcription: `cargo hax into lean` was not run to produce it. The contract's `rem_euclid` by the
positive modulus is Lean's `%` on `Int`. The contract is proved by `hax_mvcgen` and `scalar_tac`:
every multiplication is by a constant, so the residual conditions are linear, with division by
constants.

## Main results

* `Interop.Hax.Examples.Barrett.barrett_reduce_spec`: the Rust contract, as a triple for `RustM`.
* `Interop.Hax.Examples.Barrett.triple_barrett_reduce_lifted`: the contract for the lifted program,
  as a core `Std.WP` triple.
-/

public section

open Aeneas Aeneas.Std Std.Do

namespace Interop.Hax.Examples.Barrett

/-- `BARRETT_SHIFT`. -/
def BARRETT_SHIFT : I64 := 26#i64

/-- `BARRETT_R`, that is `2 ^ 26`. -/
def BARRETT_R : I64 := 67108864#i64

/-- `BARRETT_MULTIPLIER`, that is `2 ^ 26 / 3329` rounded. -/
def BARRETT_MULTIPLIER : I64 := 20159#i64

/-- `FIELD_MODULUS`, ML-KEM's prime. -/
def FIELD_MODULUS : I32 := 3329#i32

/-- The Rust `barrett_reduce` in `RustM`. -/
def barrett_reduce (value : I32) : RustM I32 := do
  let t ← IScalar.cast .I64 value * BARRETT_MULTIPLIER
  let half ← BARRETT_R >>> 1#i32
  let t ← t + half
  let quotient ← t >>> BARRETT_SHIFT
  let quotient : I32 := IScalar.cast .I32 quotient
  let sub ← quotient * FIELD_MODULUS
  value - sub

/-- A value in `i32`'s range is its own balanced residue modulo `2 ^ 32`: the casts in
`barrett_reduce` change no value. -/
private theorem bmod_two_pow_32 {x : ℤ} (h : -2 ^ 31 ≤ x ∧ x < 2 ^ 31) : x.bmod (2 ^ 32) = x :=
  Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)

private theorem val_20159 : (20159#i64).val = 20159 := by decide
private theorem val_R : (67108864#i64).val = 67108864 := by decide
private theorem val_3329 : (3329#i32).val = 3329 := by decide
private theorem toNat_one : (1#i32).toNat = 1 := by decide
private theorem toNat_26 : (26#i64).toNat = 26 := by decide

/-- The postcondition of the Rust contract. -/
def barrettPost (value r : I32) : Prop :=
  -3329 < r.val ∧ r.val < 3329 ∧ r.val % 3329 = value.val % 3329

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- The Rust contract: on inputs of size at most `2 ^ 26`, the result is smaller than the modulus
in absolute value and congruent to the input. -/
theorem barrett_reduce_spec (value : I32) :
    ⦃⌜-2 ^ 26 ≤ value.val ∧ value.val ≤ 2 ^ 26⌝⦄ barrett_reduce value
      ⦃⇓ r => ⌜barrettPost value r⌝⦄ := by
  unfold barrett_reduce barrettPost BARRETT_SHIFT BARRETT_R BARRETT_MULTIPLIER FIELD_MODULUS
  hax_mvcgen
  all_goals
    obtain ⟨hlo, hhi⟩ := ‹-2 ^ 26 ≤ value.val ∧ value.val ≤ 2 ^ 26›
    simp only [IScalar.cast_val_eq, IScalarTy.I64_numBits_eq, IScalarTy.I32_numBits_eq, val_20159,
      val_R, val_3329, toNat_one, toNat_26, Int.shiftRight_eq_div_pow, Nat.cast_pow, Nat.cast_ofNat,
      Int.reducePow, Int.reduceDiv, show min 64 32 = 32 from rfl, show min 32 64 = 32 from rfl] at *
    -- The second cast's bound depends on the first's, so the casts go in two rounds.
    iterate 2 try simp (disch := omega) only [bmod_two_pow_32] at *
    scalar_tac

variable {ι : Type} {spec : OracleSpec ι}
  [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- The contract for the lifted program: it neither panics nor diverges, and its result is
reduced and congruent to the input. -/
theorem triple_barrett_reduce_lifted (value : I32) :
    Std.WP.Triple (Interop.Rust.liftRustM (barrett_reduce value) :
        Interop.Rust.RustOracleComp spec I32)
      (-2 ^ 26 ≤ value.val ∧ value.val ≤ 2 ^ 26) (barrettPost value)
      (fun _ => False, fun _ => False, ()) :=
  Interop.Rust.triple_liftRustM_of_triple (barrett_reduce_spec value)

end Interop.Hax.Examples.Barrett
