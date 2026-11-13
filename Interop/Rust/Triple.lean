/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Aeneas.Std.WP
public import Interop.Rust.RustM
public import Std.WP
public import VCVio.ProgramLogic.Unary.WP.Necessary

/-!
# Aeneas's specifications in VCVio's program logic

Aeneas states the correctness of a `RustM` program in three ways:
* `Aeneas.Std.WP.spec x p` (total correctness: `x` returns a value satisfying `p`);
* `Aeneas.Std.WP.dspec x p` (partial correctness: `x` returns such a value or diverges);
* `Std.Do` triples against Aeneas's `Std.Do.WP RustM` instance, which `mvcgen` and hax's
  `hax_mvcgen` produce.

This file carries each across `Interop.Rust.liftRustM` into `RustOracleComp spec`, in core's
`Std.WP` program logic. Core has deprecated the `Std.Do` proof mode, so the `Std.Do` triples that
Aeneas and hax produce are carried into `Std.WP` too.

VCVio reads `OracleComp` through PolyFun's interpretations: the expectation reading
(`MAlgOrdered.toWPMonad` at `ℝ≥0∞`) and the demonic support reading
(`MonadAttach.toWPMonadDemonic` at `Prop`), which also underlies VCVio's `Std.Do` instance. Core
lifts any `Std.WP` interpretation of `OracleComp spec` through `ExceptT Error` and `OptionT`, adding
an exception postcondition for a panic and one for divergence. The `Std.WP` transports below hold
for every such interpretation, so they serve both readings.

## Main definitions

* `Interop.Rust.rustPre`: what the lift of a `RustM` program needs of its postconditions, by the
  program's one-step case.

## Main results

* `Interop.Rust.Spec.liftRustM`: the `vcgen` rule for the lift, with precondition `rustPre`.
* `triple_liftRustM_of_spec`, `triple_liftRustM_of_dspec`: Aeneas's `spec` and `dspec` as
  `Std.WP` triples for the lifted program.
* `triple_liftRustM_of_triple`: an Aeneas `Std.Do` triple as a `Std.WP` triple for the lifted
  program, under any `Prop`-valued interpretation.
-/

public section

open Aeneas.Std

namespace Interop.Rust

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

section StdWP

open Lean.Order

variable {Pred : Type}

/-- What the lift of `x` needs of its postconditions: `post v` if `x` returns `v`, the panic
postcondition if it fails, and the divergence postcondition if it diverges. -/
@[expose]
def rustPre (x : RustM α) (post : α → Pred)
    (epost : (Error → Pred) × (Unit → Pred) × Std.WP.EStackEnd) : Pred :=
  match x.match with
  | .ok v => post v
  | .vis (.fail e) _ => epost.1 (errorOfAeneas e)
  | .div => epost.2.1 ()

variable {post : α → Pred} {epost : (Error → Pred) × (Unit → Pred) × Std.WP.EStackEnd}

@[simp]
theorem rustPre_ok (v : α) : rustPre (RustM.ok v) post epost = post v := by
  simp [rustPre]

@[simp]
theorem rustPre_fail (e : Aeneas.Std.Error) :
    rustPre (RustM.fail e : RustM α) post epost = epost.1 (errorOfAeneas e) := by
  simp [rustPre]

@[simp]
theorem rustPre_div : rustPre (RustM.div : RustM α) post epost = epost.2.1 () := by
  simp [rustPre]

variable [Std.WP.Assertion Pred]

/-- A total-correctness Aeneas specification discharges `rustPre`. -/
theorem le_rustPre_of_spec {x : RustM α} {p : α → Prop} (h : Aeneas.Std.WP.spec x p)
    {pre : Pred} (hpost : ∀ v, p v → pre ⊑ post v) : pre ⊑ rustPre x post epost := by
  cases x using RustM.cases with
  | ret v => simpa using hpost v ((Aeneas.Std.WP.spec_ok v).1 h)
  | vis i k =>
    obtain ⟨e, he⟩ := RustM.vis_eq_fail i k
    rw [he] at h
    exact ((Aeneas.Std.WP.spec_fail e).1 h).elim
  | div => exact (Aeneas.Std.WP.spec_div.1 h).elim

/-- A partial-correctness Aeneas specification discharges `rustPre` when the precondition also
entails the divergence postcondition. -/
theorem le_rustPre_of_dspec {x : RustM α} {p : α → Prop} (h : Aeneas.Std.WP.dspec x p)
    {pre : Pred} (hpost : ∀ v, p v → pre ⊑ post v) (hdiv : pre ⊑ epost.2.1 ()) :
    pre ⊑ rustPre x post epost := by
  cases x using RustM.cases with
  | ret v => simpa using hpost v ((Aeneas.Std.WP.dspec_ok v).1 h)
  | vis i k =>
    obtain ⟨e, he⟩ := RustM.vis_eq_fail i k
    rw [he] at h
    exact ((Aeneas.Std.WP.dspec_fail e).1 h).elim
  | div => simpa using hdiv

variable [Std.WP.WPMonad (OracleComp spec) Pred Std.WP.EStackEnd]

/-- The `vcgen` rule for the lift, under any interpretation of `OracleComp spec`: the lifted
program meets its postconditions from `rustPre`. -/
@[spec]
theorem Spec.liftRustM (x : RustM α) (post : α → Pred)
    (epost : (Error → Pred) × (Unit → Pred) × Std.WP.EStackEnd) :
    Std.WP.Triple (liftRustM x : RustOracleComp spec α) (rustPre x post epost) post epost := by
  cases x using RustM.cases with
  | ret v =>
    rw [liftRustM_ok, rustPre_ok]
    exact Std.WP.Triple.pure v PartialOrder.rel_refl
  | vis i k =>
    obtain ⟨e, he⟩ := RustM.vis_eq_fail i k
    rw [he, liftRustM_fail, rustPre_fail]
    exact Std.WP.Spec.throw_ExceptT (m := OptionT (OracleComp spec)) (errorOfAeneas e) post epost
  | div =>
    rw [liftRustM_div, rustPre_div]
    exact ⟨Std.WP.WPMonad.pure_le_wp_pure (m := OracleComp spec)
      (none : Option (Except Error α)) (pushOption (pushExcept post epost.1) epost.2.1) epost.2.2⟩

/-- A total-correctness Aeneas specification is a triple for the lifted program, whatever the
exception postconditions. -/
theorem triple_liftRustM_of_spec {x : RustM α} {p : α → Prop} (h : Aeneas.Std.WP.spec x p)
    {pre : Pred} (hpost : ∀ v, p v → pre ⊑ post v) :
    Std.WP.Triple (liftRustM x : RustOracleComp spec α) pre post epost :=
  ⟨PartialOrder.rel_trans (le_rustPre_of_spec h hpost) (Spec.liftRustM x post epost).le_wp⟩

/-- A partial-correctness Aeneas specification is a triple for the lifted program when the
precondition also entails the divergence postcondition. -/
theorem triple_liftRustM_of_dspec {x : RustM α} {p : α → Prop} (h : Aeneas.Std.WP.dspec x p)
    {pre : Pred} (hpost : ∀ v, p v → pre ⊑ post v) (hdiv : pre ⊑ epost.2.1 ()) :
    Std.WP.Triple (liftRustM x : RustOracleComp spec α) pre post epost :=
  ⟨PartialOrder.rel_trans (le_rustPre_of_dspec h hpost hdiv) (Spec.liftRustM x post epost).le_wp⟩

end StdWP

section StdDo

open Std.Do

variable [Std.WP.WPMonad (OracleComp spec) Prop Std.WP.EStackEnd]

/-- An Aeneas `Std.Do` triple with pure assertions, the form `mvcgen` and hax's `hax_mvcgen`
produce, is a `Std.WP` triple for the lifted program under any `Prop`-valued interpretation of
`OracleComp spec`. Aeneas's instance has an exception layer for effects other than failure, which
`RustEffect` does not have, so the hypothesis may put any condition `R` there. -/
theorem triple_liftRustM_of_triple {x : RustM α} {pre : Prop} {post : α → Prop}
    {perr : Error → Prop} {pdiv : Prop} {R : PUnit → Assertion (.except PUnit .pure)}
    (h : Std.Do.Triple
      (ps := .except (ULift Aeneas.Std.Error) (.except PUnit (.except PUnit .pure))) x ⌜pre⌝
      (fun v => ⌜post v⌝, fun e => ⌜perr (errorOfAeneas e.down)⌝, R, fun _ => ⌜pdiv⌝, ())) :
    Std.WP.Triple (liftRustM x : RustOracleComp spec α) pre post (perr, fun _ => pdiv, ()) := by
  simp only [Std.Do.Triple, WP.wp, PredTrans.apply] at h
  cases x using RustM.cases with
  | ret v =>
    simp only [RustM.match.ok] at h
    rw [liftRustM_ok]
    exact Std.WP.Triple.pure v (fun hpre => (h hpre))
  | vis i k =>
    obtain ⟨e, he⟩ := RustM.vis_eq_fail i k
    rw [he] at h ⊢
    simp only [RustM.match.fail] at h
    rw [liftRustM_fail]
    exact ⟨fun hpre => (Std.WP.Spec.throw_ExceptT (m := OptionT (OracleComp spec)) (α := α)
      (errorOfAeneas e) post (perr, fun _ => pdiv, ())).le_wp (h hpre)⟩
  | div =>
    simp only [RustM.match.div] at h
    rw [liftRustM_div]
    exact ⟨fun hpre => Std.WP.WPMonad.pure_le_wp_pure (m := OracleComp spec)
      (none : Option (Except Error α))
      (Lean.Order.pushOption (Lean.Order.pushExcept post perr) fun _ => pdiv) ()
      (h hpre)⟩

/-- A triple whose precondition is a hypothesis, `pre → ⦃⌜True⌝⦄ x ⦃⇓ v => ⌜post v⌝⦄`, is a
`Std.WP` triple for the lifted program with precondition `pre`, which neither panics nor diverges.
This is the form of the contract `f.spec` that hax extracts from `#[requires]` and `#[ensures]`,
with `pre` and `post` the `holds` readings of the extracted `f.pre` and `f.post`. -/
theorem triple_liftRustM_of_imp {x : RustM α} {pre : Prop} {post : α → Prop}
    (h : pre → ⦃⌜True⌝⦄ x ⦃⇓v => ⌜post v⌝⦄) :
    Std.WP.Triple (liftRustM x : RustOracleComp spec α) pre post
      (fun _ => False, fun _ => False, ()) := by
  refine triple_liftRustM_of_triple (perr := fun _ => False) (pdiv := False)
    (R := fun _ => ⌜False⌝) ?_
  simp only [Std.Do.Triple, WP.wp, PredTrans.apply] at h ⊢
  exact fun hpre => h hpre trivial

end StdDo

end Interop.Rust
