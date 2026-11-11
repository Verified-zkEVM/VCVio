/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Hax
public import Interop.Hax.Computation.Extraction.Specs
public import Interop.Rust.Triple
public import VCVio.ProgramLogic.Unary.WP.Necessary

/-!
# A Rust constant function, extracted by hax, in VCVio

`x + x + 1` from hax's Lean test suite, made public with a no-overflow contract in the crate next
to this file (`Interop/Hax/Computation/src/lib.rs`):

```rust
#[hax_lib::requires(x <= 0x7FFF_FFFF)]
#[hax_lib::ensures(|result| result.to_int() == x.to_int() * int!(2) + int!(1))]
pub fn computation(x: u32) -> u32 {
    x + x + 1
}
```

`scripts/regenerate-hax.sh` extracts it with the hax CLI into `Interop.Hax.Computation.Extraction`:
the function `hax_computation.computation`, its `requires` and `ensures` clauses as
`computation.pre` and `computation.post`, and its contract `computation.spec`.

## Main results

* `Interop.Hax.Examples.Computation.computation_spec`: the extracted contract holds.
* `Interop.Hax.Examples.Computation.computation_pre_holds_iff`, `computation_post_holds_iff`: the
  contract's clauses in plain arithmetic.
* `Interop.Hax.Examples.Computation.triple_computation_lifted`: without overflow, the lifted
  program returns `2x + 1` and neither panics nor diverges, as a core `Std.WP` triple.
-/

public section

open Aeneas Aeneas.Std Std.Do hax_computation

namespace Interop.Hax.Examples.Computation

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- hax's proof obligation for `computation`: the extracted contract holds. -/
theorem computation_spec (x : U32) : computation.spec x := by
  unfold computation.spec computation.pre computation.post computation
  hax_mvcgen
  all_goals
    simp_all only [beq_iff_eq, decide_eq_true_eq, UScalar.le_equiv]
    scalar_tac

/-- The extracted `requires` clause: `x` is at most `2 ^ 31 - 1`, so `2x + 1` does not overflow. -/
theorem computation_pre_holds_iff (x : U32) :
    (computation.pre x).holds ↔ x.val ≤ 2 ^ 31 - 1 := by
  simp [computation.pre, RustM.holds, Triple, WP.wp, PredTrans.apply, Functor.map,
    RustM.match.ok]

/-- The extracted `ensures` clause: the result is `2x + 1`. -/
theorem computation_post_holds_iff (x r : U32) :
    (computation.post x r).holds ↔ r.val = x.val * 2 + 1 := by
  simp [computation.post, RustM.holds, Triple, WP.wp, PredTrans.apply, Functor.map,
    RustM.match.ok, hax_lib.U32.Insts.Hax_libIntToInt.to_int,
    hax_lib.int.Int.Insts.CoreOpsArithMulIntInt.mul,
    hax_lib.int.Int.Insts.CoreOpsArithAddIntInt.add, hax_lib.int.Int.Insts.CoreCmpPartialEqInt]
  norm_cast

variable {ι : Type} {spec : OracleSpec ι}
  [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- Without overflow, the lifted program returns `2x + 1`, and neither panics nor diverges. -/
theorem triple_computation_lifted (x : U32) :
    Std.WP.Triple (Interop.Rust.liftRustM (computation x) : Interop.Rust.RustOracleComp spec U32)
      (x.val ≤ 2 ^ 31 - 1) (fun r => r.val = x.val * 2 + 1)
      (fun _ => False, fun _ => False, ()) := by
  simpa only [computation_pre_holds_iff, computation_post_holds_iff] using
    Interop.Rust.triple_liftRustM_of_imp (spec := spec) (computation_spec x)

end Interop.Hax.Examples.Computation
