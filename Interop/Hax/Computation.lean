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
# A Rust constant function, through `RustM`, in VCVio

The function from hax's Lean test suite (`tests/lean-tests/src/constants.rs`):

```rust
const fn computation(x: u32) -> u32 {
    x + x + 1
}
```

`computation` below is that function in the `RustM` code hax emits today, over Aeneas's scalars:
both additions are checked. It is a transcription: `cargo hax into lean` was not run to produce
it. Its specification is proved by `hax_mvcgen` and `scalar_tac`, and reaches VCVio's program logic
by `Interop.Rust.triple_liftRustM_of_triple`.

## Main results

* `Interop.Hax.Examples.Computation.computation_spec`: without overflow, the result is `2x + 1`.
* `Interop.Hax.Examples.Computation.triple_computation_lifted`: the same for the lifted program, as
  a core `Std.WP` triple.
-/

public section

open Aeneas Aeneas.Std Std.Do

namespace Interop.Hax.Examples.Computation

/-- The Rust `computation` in `RustM`: two checked additions. -/
def computation (x : U32) : RustM U32 := do
  let t ← x + x
  t + 1#u32

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- Without overflow, `computation x` returns `2x + 1`. -/
theorem computation_spec (x : U32) :
    ⦃⌜2 * x.val + 1 < 2 ^ 32⌝⦄ computation x ⦃⇓ r => ⌜r.val = 2 * x.val + 1⌝⦄ := by
  unfold computation
  hax_mvcgen
  all_goals scalar_tac

variable {ι : Type} {spec : OracleSpec ι}
  [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- Without overflow, the lifted program returns `2x + 1`, and neither panics nor diverges. -/
theorem triple_computation_lifted (x : U32) :
    Std.WP.Triple (Interop.Rust.liftRustM (computation x) : Interop.Rust.RustOracleComp spec U32)
      (2 * x.val + 1 < 2 ^ 32) (fun r => r.val = 2 * x.val + 1)
      (fun _ => False, fun _ => False, ()) :=
  Interop.Rust.triple_liftRustM_of_triple (computation_spec x)

end Interop.Hax.Examples.Computation
