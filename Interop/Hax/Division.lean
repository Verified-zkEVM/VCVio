/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Hax
public import Interop.Rust.RustM
public import Interop.Rust.Run
public import Interop.Rust.Triple
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Monad.Basic
public import VCVio.ProgramLogic.Tactics

/-!
# Checked division in Rust, through `RustM`, in VCVio

Rust's `x / y` on `u32` panics when `y` is zero, and hax emits it as Aeneas's checked division,
which fails with `panic`. This example follows both branches into VCVio:

* `checkedDiv_spec`: with a nonzero divisor the result is the quotient, by `hax_mvcgen`; the lifted
  triple follows by `Interop.Rust.triple_liftRustM_of_triple`.
* `checkedDiv_lifted_zero`: with divisor zero the lifted program throws `Interop.Rust.Error.panic`.
* `prob_randomDiv_panic`: a program that divides by zero on one of two uniform bits panics with
  probability `1/2`.

The division is written as hax emits it; `cargo hax into lean` was not run.
-/

public section

open Aeneas Aeneas.Std Std.Do Interop.Rust OracleSpec OracleComp OracleComp.ProgramLogic ENNReal

namespace Interop.Hax.Examples.Division

/-- The Rust `x / y` on `u32`, in `RustM`. -/
def checkedDiv (x y : U32) : RustM U32 := x / y

set_option mvcgen.warning false in
set_option hax_mvcgen.warnings false in
/-- With a nonzero divisor, `checkedDiv` returns the quotient. -/
theorem checkedDiv_spec (x y : U32) :
    ⦃⌜y.val ≠ 0⌝⦄ checkedDiv x y ⦃⇓ r => ⌜r.val = x.val / y.val⌝⦄ := by
  unfold checkedDiv
  hax_mvcgen

section Lifted

variable {ι : Type} {spec : OracleSpec ι}

/-- With divisor zero, the lifted program throws `panic`. -/
theorem checkedDiv_lifted_zero (x : U32) :
    (liftRustM (checkedDiv x 0#u32) : RustOracleComp spec U32) = RustOracleComp.fail .panic := by
  have : checkedDiv x 0#u32 = RustM.fail .panic := by
    simp (config := { decide := true }) [checkedDiv, HDiv.hDiv, UScalar.div]
  rw [this, liftRustM_fail, errorOfAeneas_panic]

variable [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- With a nonzero divisor, the lifted program returns the quotient, and neither panics nor
diverges. -/
theorem triple_checkedDiv_lifted (x y : U32) :
    Std.WP.Triple (liftRustM (checkedDiv x y) : RustOracleComp spec U32)
      (y.val ≠ 0) (fun r => r.val = x.val / y.val) (fun _ => False, fun _ => False, ()) :=
  triple_liftRustM_of_triple (checkedDiv_spec x y)

end Lifted

/-- Draw a uniform bit, divide by zero on `0`, and return `x` on `1`. -/
def randomDiv (x : U32) : RustOracleComp unifSpec U32 := do
  let b ← ($[0..1] : ProbComp (Fin 2))
  if b = 0 then liftRustM (checkedDiv x 0#u32) else pure x

/-- The draw decides the outcome. -/
theorem randomDiv_run_run (x : U32) :
    (randomDiv x).run.run =
      ((fun b : Fin 2 => some (if b = 0 then Except.error Interop.Rust.Error.panic
          else Except.ok x)) <$> ($[0..1] : ProbComp (Fin 2)) :
        OracleComp unifSpec (Option (Except Interop.Rust.Error U32))) := by
  unfold randomDiv
  simp only [RustOracleComp.run_run_bind_liftM, map_eq_bind_pure_comp]
  refine bind_congr fun b => ?_
  fin_cases b <;> simp [checkedDiv_lifted_zero]

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
