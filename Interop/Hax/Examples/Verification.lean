/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Hax
public import Interop.Hax.Examples.Extraction.Specs
public import Interop.Hax.Holds
public import Interop.Rust.RustM
public import Interop.Rust.Triple
public import VCVio.ProgramLogic.Tactics

/-!
# A Rust step after an oracle query

`RustM` has no oracle; `RustOracleComp` does. This example queries an oracle and passes its answer
to a checked Rust addition, so its specification ranges over every possible answer. The addition
is `add_or_panic` in the crate next to this file (`Interop/Hax/Examples/src/lib.rs`), with the
contract `requires(x <= u32::MAX - y)` and `ensures(result.to_int() == x.to_int() + y.to_int())`;
`scripts/regenerate-hax.sh` extracts it with the hax CLI into `Interop.Hax.Examples.Extraction` as
`hax_add_or_panic.add_or_panic`.

* `add_or_panic_spec`: the extracted contract holds, by `hax_mvcgen`, and its clauses read as plain
  arithmetic (`add_or_panic_pre_holds_iff`, `add_or_panic_post_holds_iff`).
* `triple_oracleThenAdd`: if no answer can overflow the addition, the composite never panics and
  returns at least `x`. The query is one step of core's `vcgen` under VCVio's possible-outputs
  reading, and the Rust step is the contract carried over by
  `Interop.Rust.triple_liftRustM_of_imp`.

Probabilities of Rust panics are in `Interop.Hax.Division.Verification` and
`Interop.Hax.CenteredBinomial.Verification`.
-/

public section

open Aeneas Aeneas.Std Std.Do Interop.Rust OracleSpec OracleComp hax_add_or_panic

namespace Interop.Hax.Examples.OracleThenAdd

/-- The value of `u32::MAX`, which the extracted precondition subtracts from. -/
theorem U32_MAX_val : core.num.U32.MAX.val = 2 ^ 32 - 1 := by
  simp [core.num.U32.MAX, UScalar.ofNat, UScalar.ofNatCore_val_eq, U32.rMax]

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- hax's proof obligation for `add_or_panic`: the extracted contract holds. -/
theorem add_or_panic_spec (x y : U32) : add_or_panic.spec x y := by
  unfold add_or_panic.spec add_or_panic.pre add_or_panic.post add_or_panic
  hax_mvcgen
  all_goals
    simp_all only [beq_iff_eq, decide_eq_true_eq, UScalar.le_equiv, U32_MAX_val]
    scalar_tac

/-- The extracted `requires` clause: `x + y` does not overflow. -/
theorem add_or_panic_pre_holds_iff (x y : U32) :
    (add_or_panic.pre x y).holds ↔ x.val + y.val < 2 ^ 32 := by
  obtain ⟨z, hz, hzv, -, -⟩ := WP.spec_imp_exists
    (UScalar.sub_bv_spec (x := core.num.U32.MAX) (y := y) (by rw [U32_MAX_val]; scalar_tac))
  rw [U32_MAX_val] at hzv
  simp only [add_or_panic.pre, hz, bind_ok, Interop.Hax.holds_ok, decide_eq_true_eq,
    UScalar.le_equiv]
  constructor <;> intro h <;> scalar_tac

/-- The extracted `ensures` clause: the result is the sum. -/
theorem add_or_panic_post_holds_iff (x y r : U32) :
    (add_or_panic.post x y r).holds ↔ r.val = x.val + y.val := by
  simp [add_or_panic.post, RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply, Functor.map,
    RustM.match.ok, hax_lib.U32.Insts.Hax_libIntToInt.to_int,
    hax_lib.int.Int.Insts.CoreOpsArithAddIntInt.add, hax_lib.int.Int.Insts.CoreCmpPartialEqInt]
  norm_cast

variable {ι : Type} {spec : OracleSpec ι}

/-- Query the oracle at `t`, read the answer as a `u32`, and add it to `x` in Rust. -/
def oracleThenAdd (x : U32) (t : ι) (coe : spec.Range t → U32) : RustOracleComp spec U32 := do
  let y ← RustOracleComp.liftOracleComp (query t : OracleComp spec _)
  liftRustM (add_or_panic x (coe y))

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
  · have h := triple_liftRustM_of_imp (spec := spec) (add_or_panic_spec x (coe y))
    simp only [add_or_panic_pre_holds_iff, add_or_panic_post_holds_iff] at h
    refine ⟨Std.WP.Triple.entails_wp_of_pre_post h (fun _ => hbound y) (fun r hr => ?_)⟩
    omega

end Interop.Hax.Examples.OracleThenAdd
