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
# A Rust add-with-carry, through `RustM`, in VCVio

hax's `adc` example, the building block of multi-precision addition:

```rust
#[hax_lib::requires(carry_in <= 1)]
#[hax_lib::ensures(|result| {
    let (sum, carry_out) = result;
    carry_out <= 1
        && (a.to_int() + b.to_int() + carry_in.to_int())
            == (sum.to_int() + carry_out.to_int() * int!(32).pow2())
})]
pub fn adc_u32(a: u32, b: u32, carry_in: u32) -> (u32, u32) {
    let wide: u64 = a as u64 + b as u64 + carry_in as u64;
    let sum: u32 = wide as u32;
    let carry_out: u32 = (wide >> 32u64) as u32;
    (sum, carry_out)
}
```

`adc_u32` below is that function in the `RustM` code hax emits today, over Aeneas's scalars: the
casts are pure, while the additions and the shift are checked. It is a transcription: `cargo hax
into lean` was not run to produce it. The specification is the Rust contract as a `Std.Do` triple,
proved as hax's own proof obligation is, by `hax_mvcgen` and `scalar_tac`. It reaches VCVio's
program logic, under any `Prop`-valued interpretation of oracle computations, by
`Interop.Rust.triple_liftRustM_of_triple`.

## Main results

* `Interop.Hax.Examples.Adc.adc_u32_spec`: the Rust contract, as a triple for `RustM`.
* `Interop.Hax.Examples.Adc.triple_adc_u32_lifted`: the contract for the lifted program, as a core
  `Std.WP` triple.
-/

public section

open Aeneas Aeneas.Std Std.Do

namespace Interop.Hax.Examples.Adc

/-- The Rust `adc_u32` in `RustM`: widen to `u64`, add with checks, and split the sum at bit 32. -/
def adc_u32 (a b carry_in : U32) : RustM (U32 × U32) := do
  let wide ← UScalar.cast .U64 a + UScalar.cast .U64 b
  let wide ← wide + UScalar.cast .U64 carry_in
  let sum : U32 := UScalar.cast .U32 wide
  let s ← wide >>> 32#u64
  let carry_out : U32 := UScalar.cast .U32 s
  pure (sum, carry_out)

/-- The postcondition of the Rust contract. -/
def adcPost (a b carry_in : U32) (r : U32 × U32) : Prop :=
  r.2.val ≤ 1 ∧ a.val + b.val + carry_in.val = r.1.val + r.2.val * 2 ^ 32

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- The Rust contract: with a carry of at most one, the carry out is at most one and the two
outputs represent the wide sum. -/
theorem adc_u32_spec (a b carry_in : U32) :
    ⦃⌜carry_in.val ≤ 1⌝⦄ adc_u32 a b carry_in ⦃⇓ r => ⌜adcPost a b carry_in r⌝⦄ := by
  unfold adc_u32 adcPost
  hax_mvcgen
  all_goals
    simp_all only [UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow]
    scalar_tac

variable {ι : Type} {spec : OracleSpec ι}
  [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- The contract for the lifted program: it neither panics nor diverges, and its outputs satisfy
the Rust postcondition. -/
theorem triple_adc_u32_lifted (a b carry_in : U32) :
    Std.WP.Triple (Interop.Rust.liftRustM (adc_u32 a b carry_in) :
        Interop.Rust.RustOracleComp spec (U32 × U32))
      (carry_in.val ≤ 1) (adcPost a b carry_in) (fun _ => False, fun _ => False, ()) :=
  Interop.Rust.triple_liftRustM_of_triple (adc_u32_spec a b carry_in)

end Interop.Hax.Examples.Adc
