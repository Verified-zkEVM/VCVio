/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Hax
public import Interop.Rust.RustM
public import Interop.Rust.Triple
public import VCVio.ProgramLogic.Tactics

/-!
# A Rust step after an oracle query

`RustM` has no oracle; `RustOracleComp` does. This example queries an oracle and passes its answer
to a checked Rust addition, so its specification ranges over every possible answer:

* `addOrPanic_spec`: without overflow the Rust addition returns the sum, by `hax_mvcgen`;
* `triple_oracleThenAdd`: if no answer can overflow the addition, the composite never panics and
  returns at least `x`. The query is one step of core's `vcgen` under VCVio's possible-outputs
  reading, and the Rust step is `addOrPanic_spec` carried over by
  `Interop.Rust.triple_liftRustM_of_triple`.

Probabilities of Rust panics are in `Interop.Hax.Division` and `Interop.Hax.CenteredBinomial`.
-/

public section

open Aeneas Aeneas.Std Std.Do Interop.Rust OracleSpec OracleComp

namespace Interop.Hax.Examples.OracleThenAdd

/-- A checked Rust addition on `u32`, in `RustM`. -/
def addOrPanic (x y : U32) : RustM U32 := x + y

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- Without overflow, `addOrPanic` returns the sum. -/
theorem addOrPanic_spec (x y : U32) :
    ⦃⌜x.val + y.val < 2 ^ 32⌝⦄ addOrPanic x y ⦃⇓ r => ⌜r.val = x.val + y.val⌝⦄ := by
  unfold addOrPanic
  hax_mvcgen
  all_goals scalar_tac

variable {ι : Type} {spec : OracleSpec ι}

/-- Query the oracle at `t`, read the answer as a `u32`, and add it to `x` in Rust. -/
def oracleThenAdd (x : U32) (t : ι) (coe : spec.Range t → U32) : RustOracleComp spec U32 := do
  let y ← RustOracleComp.liftOracleComp (query t : OracleComp spec _)
  liftRustM (addOrPanic x (coe y))

open scoped OracleComp.Necessary

/-- If no answer can overflow the addition, every possible output is at least `x`, and the
program neither panics nor diverges. -/
theorem triple_oracleThenAdd (x : U32) (t : ι) (coe : spec.Range t → U32)
    (hbound : ∀ y, x.val + (coe y).val < 2 ^ 32) :
    Std.WP.Triple (oracleThenAdd x t coe) True (fun r => x.val ≤ r.val)
      (fun _ => False, fun _ => False, ()) := by
  unfold oracleThenAdd
  refine Std.WP.Triple.bind _ _ (fun _ => True) ?_ fun y => ?_
  · vcgen
  · refine ⟨Std.WP.Triple.entails_wp_of_pre_post
      (triple_liftRustM_of_triple (spec := spec) (addOrPanic_spec x (coe y)))
      (fun _ => hbound y) (fun r hr => ?_)⟩
    omega

end Interop.Hax.Examples.OracleThenAdd
