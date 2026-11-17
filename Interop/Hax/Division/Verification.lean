/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Hax
public import Interop.Hax.Division.Extraction.Specs
public import Interop.Rust.RustM
public import Interop.Rust.Run
public import Interop.Rust.Triple
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Monad.Basic
public import VCVio.ProgramLogic.Tactics

/-!
# Checked division in Rust, extracted by hax, in VCVio

Rust's `x / y` on `u32` panics when `y` is zero. The crate next to this file
(`Interop/Hax/Division/src/lib.rs`) states the contract

```rust
#[hax_lib::requires(y != 0)]
#[hax_lib::ensures(|result| result == x / y)]
pub fn checked_div(x: u32, y: u32) -> u32 {
    x / y
}
```

and `scripts/regenerate-hax.sh` extracts it with the hax CLI into
`Interop.Hax.Division.Extraction` as `hax_division.checked_div`, Aeneas's checked division, which
fails with `panic` on a zero divisor. This example follows both branches into VCVio:

* `checked_div_spec`: the extracted contract holds, by `hax_mvcgen`. Its clauses read as plain
  arithmetic (`checked_div_pre_holds_iff`, `checked_div_post_holds_iff`), and the lifted triple
  `triple_checked_div_lifted` follows through `Interop.Rust.triple_liftRustM_of_imp`.
* `checked_div_lifted_zero`: with divisor zero the lifted program throws
  `Interop.Rust.Error.panic`.
* `prob_randomDiv_panic`: a program that divides by zero on one of two uniform bits panics with
  probability `1/2`.
-/

public section

open Aeneas Aeneas.Std Std.Do Interop.Rust OracleSpec OracleComp OracleComp.ProgramLogic ENNReal
  hax_division

namespace Interop.Hax.Examples.Division

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- hax's proof obligation for `checked_div`: the extracted contract holds. -/
theorem checked_div_spec (x y : U32) : checked_div.spec x y := by
  unfold checked_div.spec checked_div.pre checked_div.post checked_div
  hax_mvcgen
  all_goals
    simp_all only [bne_iff_ne, ne_eq, decide_eq_true_eq]
    scalar_tac

/-- The extracted `requires` clause: the divisor is nonzero. -/
theorem checked_div_pre_holds_iff (x y : U32) : (checked_div.pre x y).holds ↔ y.val ≠ 0 := by
  simp [checked_div.pre, RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply, Functor.map,
    RustM.match.ok]

/-- The extracted `ensures` clause recomputes `x / y`, so it holds exactly when the divisor is
nonzero and the result is the quotient. -/
theorem checked_div_post_holds_iff (x y r : U32) :
    (checked_div.post x y r).holds ↔ y.val ≠ 0 ∧ r.val = x.val / y.val := by
  by_cases hy : y.val = 0
  · have hy0 : y = 0#u32 := by scalar_tac
    subst hy0
    have hfail : x / (0#u32) = RustM.fail .panic := by
      simp (config := { decide := true }) [HDiv.hDiv, UScalar.div]
    simp [checked_div.post, hfail, RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply, Functor.map]
  · obtain ⟨z, hz, hzv⟩ := UScalar.div_spec x hy
    simp [checked_div.post, hz, hy, RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply, Functor.map,
      RustM.match.ok, ← hzv, UScalar.eq_equiv]

section Lifted

variable {ι : Type} {spec : OracleSpec ι}

/-- With divisor zero, the lifted program throws `panic`. -/
theorem checked_div_lifted_zero (x : U32) :
    (liftRustM (checked_div x 0#u32) : RustOracleComp spec U32) = RustOracleComp.fail .panic := by
  have : checked_div x 0#u32 = RustM.fail .panic := by
    simp (config := { decide := true }) [checked_div, HDiv.hDiv, UScalar.div]
  rw [this, liftRustM_fail, errorOfAeneas_panic]

variable [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- With a nonzero divisor, the lifted program returns the quotient, and neither panics nor
diverges. -/
theorem triple_checked_div_lifted (x y : U32) :
    Std.WP.Triple (liftRustM (checked_div x y) : RustOracleComp spec U32)
      (y.val ≠ 0) (fun r => y.val ≠ 0 ∧ r.val = x.val / y.val)
      (fun _ => False, fun _ => False, ()) := by
  simpa only [checked_div_pre_holds_iff, checked_div_post_holds_iff] using
    triple_liftRustM_of_imp (spec := spec) (checked_div_spec x y)

end Lifted

/-- Draw a uniform bit, divide by zero on `0`, and return `x` on `1`. -/
def randomDiv (x : U32) : RustOracleComp unifSpec U32 := do
  let b ← ($[0..1] : ProbComp (Fin 2))
  if b = 0 then liftRustM (checked_div x 0#u32) else pure x

/-- The draw decides the outcome. -/
theorem randomDiv_run_run (x : U32) :
    (randomDiv x).run.run =
      ((fun b : Fin 2 => some (if b = 0 then Except.error Interop.Rust.Error.panic
          else Except.ok x)) <$> ($[0..1] : ProbComp (Fin 2)) :
        OracleComp unifSpec (Option (Except Interop.Rust.Error U32))) := by
  unfold randomDiv
  simp only [RustOracleComp.run_run_bind_liftM, map_eq_bind_pure_comp]
  refine bind_congr fun b => ?_
  fin_cases b <;> simp [checked_div_lifted_zero]

/-- The program panics with probability `1/2`: exactly on the draw `0`. -/
theorem prob_randomDiv_panic (x : U32) :
    Pr{let r ← (randomDiv x).run.run}[r = some (Except.error Interop.Rust.Error.panic)] = 2⁻¹ := by
  rw [randomDiv_run_run]
  simp only [Functor.map_map, Option.some.injEq]
  pvcgen
  simp only [ProbComp.uniformFin]
  rw [wp_query_uniform, Fin.sum_univ_two, show Fintype.card (unifSpec.Range 1) = 2 from rfl]
  simp

end Interop.Hax.Examples.Division
