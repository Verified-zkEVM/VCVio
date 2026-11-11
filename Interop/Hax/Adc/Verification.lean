/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Hax
public import Interop.Hax.Adc.Extraction.Specs
public import Interop.Hax.Holds
public import Interop.Rust.RustM
public import Interop.Rust.Triple
public import VCVio.ProgramLogic.Unary.WP.Necessary

/-!
# A Rust add-with-carry, extracted by hax, in VCVio

hax's `adc` example, the building block of multi-precision addition, vendored in the crate next to
this file (`Interop/Hax/Adc/src/lib.rs`):

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

`scripts/regenerate-hax.sh` extracts it with the hax CLI into `Interop.Hax.Adc.Extraction`: the
function `hax_adc.adc_u32`, its `requires` and `ensures` clauses as `adc_u32.pre` and
`adc_u32.post`, and its contract `adc_u32.spec`. The contract is proved by hax's own proof of it,
with `hax_mvcgen` and `scalar_tac`. Its clauses read as plain arithmetic (`adcPost`), and it reaches
VCVio's program logic, under any `Prop`-valued interpretation of oracle computations, through
`Interop.Rust.triple_liftRustM_of_imp`.

## Main results

* `Interop.Hax.Examples.Adc.adc_u32_spec`: the extracted contract holds.
* `Interop.Hax.Examples.Adc.adc_u32_pre_holds_iff`, `adc_u32_post_holds_iff`: its clauses in plain
  arithmetic.
* `Interop.Hax.Examples.Adc.triple_adc_u32_lifted`: the contract for the lifted program, as a core
  `Std.WP` triple.
-/

public section

open Aeneas Aeneas.Std Std.Do hax_adc

namespace Interop.Hax.Examples.Adc

/-- The postcondition of the Rust contract, in plain arithmetic. -/
def adcPost (a b carry_in : U32) (r : U32 × U32) : Prop :=
  r.2.val ≤ 1 ∧ a.val + b.val + carry_in.val = r.1.val + r.2.val * 2 ^ 32

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- hax's proof obligation for `adc_u32`, by hax's own proof: the extracted contract holds. -/
theorem adc_u32_spec (a b carry_in : U32) : adc_u32.spec a b carry_in := by
  unfold adc_u32.spec adc_u32.pre adc_u32.post adc_u32
  hax_mvcgen
  all_goals
    simp_all only [UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow,
      UScalar.le_equiv, Nat.reducePow, Int.natCast_emod, Nat.cast_add, Nat.cast_ofNat,
      UScalar.ofNatCore_val_eq, Int.natCast_ediv, Int.reduceToNat, Int.reducePow, beq_iff_eq]
    scalar_tac

/-- The extracted `requires` clause: the carry in is at most one. -/
theorem adc_u32_pre_holds_iff (a b carry_in : U32) :
    (adc_u32.pre a b carry_in).holds ↔ carry_in.val ≤ 1 := by
  simp only [adc_u32.pre, Interop.Hax.holds_ok, decide_eq_true_eq, UScalar.le_equiv]
  constructor <;> intro h <;> scalar_tac

/-- The extracted `ensures` clause is `adcPost`. -/
theorem adc_u32_post_holds_iff (a b carry_in : U32) (r : U32 × U32) :
    (adc_u32.post a b carry_in r).holds ↔ adcPost a b carry_in r := by
  obtain ⟨sum, carry_out⟩ := r
  by_cases hc : carry_out.val ≤ 1
  · simp [adc_u32.post, adcPost, hc, hax_lib.U32.Insts.Hax_libIntToInt.to_int,
      hax_lib.int.Int.Insts.CoreOpsArithAddIntInt.add,
      hax_lib.int.Int.Insts.CoreOpsArithMulIntInt.mul, hax_lib.int.Int.pow2,
      hax_lib.int.Int.Insts.CoreCmpPartialEqInt, RustM.holds, Std.Do.Triple, WP.wp,
      PredTrans.apply, Functor.map, RustM.match.ok, UScalar.le_equiv, bind_ok]
    norm_cast
  · simp [adc_u32.post, adcPost, hc, RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply,
      Functor.map, RustM.match.ok, UScalar.le_equiv, bind_ok]

variable {ι : Type} {spec : OracleSpec ι}
  [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- The contract for the lifted program: it neither panics nor diverges, and its outputs satisfy
the Rust postcondition. -/
theorem triple_adc_u32_lifted (a b carry_in : U32) :
    Std.WP.Triple (Interop.Rust.liftRustM (adc_u32 a b carry_in) :
        Interop.Rust.RustOracleComp spec (U32 × U32))
      (carry_in.val ≤ 1) (adcPost a b carry_in) (fun _ => False, fun _ => False, ()) :=
  by simpa only [adc_u32_pre_holds_iff, adc_u32_post_holds_iff] using
    Interop.Rust.triple_liftRustM_of_imp (spec := spec) (adc_u32_spec a b carry_in)

end Interop.Hax.Examples.Adc
