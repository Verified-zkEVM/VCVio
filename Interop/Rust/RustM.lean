/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module

public import Aeneas.Std.Primitives
public import Interop.Rust.Common
public import PolyFun.Control.Monad.Hom

/-!
# Aeneas's `RustM` in `RustOracleComp`

Aeneas and hax now share one target monad: hax's Lean library builds on Aeneas's, and both emit
code in `Aeneas.Std.RustM`, an interaction tree over the effect `RustEffect` whose only event is
`fail e`, which has no answer. A `RustM` computation therefore unfolds in one step to a returned
value, a failure, or divergence (`Aeneas.Std.RustM.match`), and this file lifts it into VCVio's
`Interop.Rust.RustOracleComp spec`, where failure is the `ExceptT` layer and divergence the
`OptionT` layer.

The lift preserves `pure` and `bind` (`Interop.Rust.liftRustM_bind`), so it is a lawful monad
lift and a bundled monad morphism `RustM →ᵐ RustOracleComp spec`.

## Main definitions

* `Interop.Rust.errorOfAeneas`: Aeneas's errors among `Interop.Rust.Error`.
* `Interop.Rust.liftRustM`: the lift, and `Interop.Rust.liftRustMHom` bundled.

## Main results

* `Interop.Rust.liftRustM_ok`, `Interop.Rust.liftRustM_fail`, `Interop.Rust.liftRustM_div`.
* `Interop.Rust.liftRustM_bind`: the lift commutes with `bind`.
-/

public section

open Aeneas.Std

namespace Interop.Rust

/-- Aeneas's two errors, among the mirrored Rust errors. -/
@[expose] def errorOfAeneas : Aeneas.Std.Error → Error
  | .panic => .panic
  | .undef => .undef

@[simp] theorem errorOfAeneas_panic : errorOfAeneas .panic = .panic := rfl

@[simp] theorem errorOfAeneas_undef : errorOfAeneas .undef = .undef := rfl

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- Lift a `RustM` computation into `RustOracleComp spec`: a returned value is returned, a failure
is thrown with its error, and divergence is `RustOracleComp.div`. It makes no oracle query. -/
def liftRustM (x : RustM α) : RustOracleComp spec α :=
  match x.match with
  | .ok v => pure v
  | .vis (.fail e) _ => throw (errorOfAeneas e)
  | .div => RustOracleComp.div

instance : MonadLift RustM (RustOracleComp spec) where
  monadLift := liftRustM

@[simp]
theorem liftRustM_ok (v : α) :
    (liftRustM (RustM.ok v) : RustOracleComp spec α) = RustOracleComp.ok v := by
  simp [liftRustM, RustOracleComp.ok]

@[simp]
theorem liftRustM_fail (e : Aeneas.Std.Error) :
    (liftRustM (RustM.fail e) : RustOracleComp spec α) =
      RustOracleComp.fail (errorOfAeneas e) := by
  simp [liftRustM, RustOracleComp.fail]

@[simp]
theorem liftRustM_div :
    (liftRustM (RustM.div : RustM α) : RustOracleComp spec α) = RustOracleComp.div := by
  simp [liftRustM]

@[simp]
theorem liftRustM_pure (v : α) :
    (liftRustM (pure v : RustM α) : RustOracleComp spec α) = pure v :=
  liftRustM_ok v

/-- An event of `RustEffect` is a failure, and a continuation from its empty answer type is
`PEmpty.elim`, so every `vis` node is `RustM.fail`. -/
theorem RustM.vis_eq_fail (i : RustEffect.Input) (k : RustEffect.Output i → RustM α) :
    ∃ e, RustM.vis i k = RustM.fail e := by
  cases i with
  | fail e =>
    refine ⟨e, ?_⟩
    rw [RustM.fail_eq_vis]
    congr
    funext o
    exact o.elim

/-- The lift commutes with `bind`: the failure and divergence branches short-circuit on both
sides. -/
@[simp]
theorem liftRustM_bind {β : Type} (x : RustM α) (k : α → RustM β) :
    (liftRustM (x >>= k) : RustOracleComp spec β) =
      liftRustM x >>= fun a => liftRustM (k a) := by
  cases x using RustM.cases with
  | ret v => simp [RustOracleComp.ok]
  | vis i k' =>
    obtain ⟨e, he⟩ := RustM.vis_eq_fail i k'
    rw [he, bind_tc_fail, liftRustM_fail, liftRustM_fail]
    rfl
  | div =>
    rw [bind_tc_div, liftRustM_div, liftRustM_div]
    rfl

instance instLawfulMonadLiftRustM : LawfulMonadLift RustM (RustOracleComp spec) where
  monadLift_pure v := liftRustM_pure v
  monadLift_bind x k := liftRustM_bind x k

/-- The lift as a bundled monad morphism. -/
@[expose] def liftRustMHom : RustM →ᵐ RustOracleComp spec :=
  MonadHom.ofLift _ _

@[simp]
theorem liftRustMHom_apply (x : RustM α) : (liftRustMHom (spec := spec)) x = liftRustM x := rfl

end Interop.Rust
