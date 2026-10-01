/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Algebra
public import ToMathlib.Control.Except
public import ToMathlib.Control.OptionT
public import ToMathlib.Control.StateT
public import ToMathlib.Control.WriterT
public import VCVio.ProgramLogic.Unary.WP.Measure
public import VCVio.OracleComp.EvalDist.MeasureSpec
public import PolyFun.Control.Monad.Algebra.WP
public import PolyFun.Control.Do.Spec

/-!
# Quantitative weakest preconditions

The expectation algebra on `OracleComp spec` is a core `WPMonad` interpretation with `ℝ≥0∞`
assertions, selected by `open scoped OracleComp.Quantitative`: under it, `wp oa post ⊥`, core
triples and `vcgen` read expectations, with lower-bound triples `pre ≤ wp⟦oa⟧ post`. The
notations `Pr{…}[…]`, `𝔼{…}[…]` and `wp⟦oa⟧ g` name this interpretation explicitly, so they mean
the expectation in every scope. The algebra-to-WP bridge and lattice instances come from PolyFun.
The transformer lemmas describe expectation after running state, reader, option, exception, and
writer layers.

Core selects one interpretation per program type, since its assertion carriers are output
parameters: the global reading of `OracleComp` is the structural one
(`OracleComp.Qualitative`), and this scope, like `OracleComp.Upper` and
`OracleComp.Probabilistic`, takes precedence while it is open.
-/

@[expose] public section

open ENNReal MeasureTheory
open Lean.Order
open Std.WP
open scoped WriterT.MonoidWP

universe u v

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [OracleSpec.IsMeasureSpec spec]
variable {α β : Type}

/-! ## The expectation algebra -/

/-- The nonnegative expectation algebra under the configured oracle answer measures. -/
noncomputable instance instMAlgOrdered : MAlgOrdered (OracleComp spec) ℝ≥0∞ :=
  ExpectationWP.algebra (OracleComp spec)

/-- The expectation of the identity under the configured oracle answer measures. -/
noncomputable def μ (oa : OracleComp spec ℝ≥0∞) : ℝ≥0∞ :=
  MAlgOrdered.μ oa

end OracleComp.ProgramLogic

namespace OracleComp.Quantitative

/-! ## `Std.WP.WP` instance for `OracleComp` -/

variable {ι : Type u} {spec : OracleSpec ι}
variable [OracleSpec.IsMeasureSpec spec]
variable {α β : Type}

/-- Core weakest preconditions under the configured oracle answer measures: the expectation
interpretation `ExpectationWP.wpMonad`, so `wp oa post ⊥` is `wp⟦oa⟧ post`. Opening the
scope selects it over the structural reading. -/
noncomputable scoped instance (priority := 1100) instWP :
    Std.WP.WPMonad (OracleComp spec) ℝ≥0∞ EStack⟨⟩ :=
  ExpectationWP.wpMonad (OracleComp spec)

/-- The expectation reading as a direct `WP` instance on programs, at the scope's priority, so
that no direct instance of another scope outranks it while this one is open. -/
noncomputable scoped instance (priority := 1100) wpInst :
    Std.WP.WP (OracleComp spec α) α ℝ≥0∞ EStack⟨⟩ :=
  (instWP (spec := spec)).toWP α

/-! ## `StateT (OracleComp spec)` WP normalization -/

@[simp]
theorem wp_StateT_bind {σ : Type} (x : StateT σ (OracleComp spec) α)
    (f : α → StateT σ (OracleComp spec) β) (post : β → σ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (StateT.bind x f) post epost =
      fun s => Std.WP.wp x (fun a s' => Std.WP.wp (f a) post epost s')
        epost s := by
  funext s
  simp only [StateT.wp_apply_eq, ← StateT.monad_bind_def, StateT.run_bind,
    ExactWPMonad.wp_bind]

theorem wp_StateT_bind' {σ : Type} (x : StateT σ (OracleComp spec) α)
    (f : α → StateT σ (OracleComp spec) β) (post : β → σ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (x >>= f) post epost =
      fun s => Std.WP.wp x (fun a s' => Std.WP.wp (f a) post epost s')
        epost s :=
  wp_StateT_bind x f post epost

theorem wp_StateT_pure {σ : Type} (x : α) (post : α → σ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (pure x : StateT σ (OracleComp spec) α) post epost =
      fun s => post x s := by
  funext s
  exact ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞) (epost := epost) (x, s)
    (fun p : α × σ => post p.1 p.2)

theorem wp_StateT_get {σ : Type} (post : σ → σ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (MonadStateOf.get : StateT σ (OracleComp spec) σ) post epost =
      fun s => post s s := by
  funext s
  exact ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞) (epost := epost) (s, s)
    (fun p : σ × σ => post p.1 p.2)

@[simp]
theorem wp_StateT_set {σ : Type} (s' : σ) (post : PUnit → σ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (MonadStateOf.set s' : StateT σ (OracleComp spec) PUnit) post
      epost = fun _ => post ⟨⟩ s' := by
  funext s
  exact ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞)
      (epost := epost) (PUnit.unit, s')
    (fun p : PUnit × σ => post p.1 p.2)

theorem wp_StateT_modifyGet {σ : Type} (f : σ → α × σ) (post : α → σ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (MonadStateOf.modifyGet f : StateT σ (OracleComp spec) α) post
      epost = fun s => post (f s).1 (f s).2 := by
  funext s
  exact ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞) (epost := epost) (f s)
    (fun p : α × σ => post p.1 p.2)

@[simp]
theorem wp_StateT_monadLift {σ : Type} (oa : OracleComp spec α)
    (post : α → σ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (MonadLift.monadLift oa : StateT σ (OracleComp spec) α) post
      epost = fun s => Std.WP.wp oa (fun a => post a s) epost := by
  funext s
  simp only [StateT.wp_apply_eq, StateT.run_core_monadLift,
    ExactWPMonad.wp_bind, ExactWPMonad.wp_pure]

/-! ## `OptionT (OracleComp spec)` WP normalization -/

theorem wp_OptionT_bind (x : OptionT (OracleComp spec) α)
    (f : α → OptionT (OracleComp spec) β) (post : β → ℝ≥0∞)
    (epost : EStack⟨Unit → ℝ≥0∞⟩) :
    Std.WP.wp (x >>= f) post epost =
      Std.WP.wp x (fun a => Std.WP.wp (f a) post epost) epost :=
  ExactWPMonad.wp_bind x f post epost

theorem wp_OptionT_pure (x : α) (post : α → ℝ≥0∞)
    (epost : EStack⟨Unit → ℝ≥0∞⟩) :
    Std.WP.wp (pure x : OptionT (OracleComp spec) α) post epost = post x :=
  ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞) (epost := epost.snd)
    (some x) (Lean.Order.pushOption post epost.fst)

theorem wp_OptionT_failure (post : α → ℝ≥0∞)
    (epost : EStack⟨Unit → ℝ≥0∞⟩) :
    Std.WP.wp (failure : OptionT (OracleComp spec) α) post epost = epost.fst () :=
  ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞) (epost := epost.snd)
    none (Lean.Order.pushOption post epost.fst)

theorem wp_OptionT_monadLift (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (epost : EStack⟨Unit → ℝ≥0∞⟩) :
    Std.WP.wp (MonadLift.monadLift oa : OptionT (OracleComp spec) α) post epost =
      Std.WP.wp oa post Lean.Order.bot := by
  simp only [OptionT.wp_apply_eq, OptionT.run_core_monadLift,
    ExactWPMonad.wp_bind, ExactWPMonad.wp_pure, Lean.Order.pushOption]

theorem wp_OptionT_lift (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (epost : EStack⟨Unit → ℝ≥0∞⟩) :
    Std.WP.wp (OptionT.lift oa : OptionT (OracleComp spec) α) post epost =
      Std.WP.wp oa post Lean.Order.bot :=
  wp_OptionT_monadLift oa post epost

theorem wp_OptionT_map (f : α → β) (x : OptionT (OracleComp spec) α)
    (post : β → ℝ≥0∞) (epost : EStack⟨Unit → ℝ≥0∞⟩) :
    Std.WP.wp (f <$> x) post epost = Std.WP.wp x (fun a => post (f a)) epost :=
  ExactWPMonad.wp_map f x post epost

/-! ## `ExceptT (OracleComp spec)` WP normalization -/

theorem wp_ExceptT_bind {ε : Type} (x : ExceptT ε (OracleComp spec) α)
    (f : α → ExceptT ε (OracleComp spec) β) (post : β → ℝ≥0∞)
    (epost : EStack⟨ε → ℝ≥0∞⟩) :
    Std.WP.wp (x >>= f) post epost =
      Std.WP.wp x (fun a => Std.WP.wp (f a) post epost) epost :=
  ExactWPMonad.wp_bind x f post epost

theorem wp_ExceptT_pure {ε : Type} (x : α) (post : α → ℝ≥0∞)
    (epost : EStack⟨ε → ℝ≥0∞⟩) :
    Std.WP.wp (pure x : ExceptT ε (OracleComp spec) α) post epost = post x :=
  ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞) (epost := epost.snd)
    (Except.ok x) (Lean.Order.pushExcept post epost.fst)

theorem wp_ExceptT_throw {ε : Type} (e : ε) (post : α → ℝ≥0∞)
    (epost : EStack⟨ε → ℝ≥0∞⟩) :
    Std.WP.wp (throw e : ExceptT ε (OracleComp spec) α) post epost = epost.fst e :=
  ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞) (epost := epost.snd)
    (Except.error e) (Lean.Order.pushExcept post epost.fst)

theorem wp_ExceptT_monadLift {ε : Type} (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (epost : EStack⟨ε → ℝ≥0∞⟩) :
    Std.WP.wp (MonadLift.monadLift oa : ExceptT ε (OracleComp spec) α) post epost =
      Std.WP.wp oa post Lean.Order.bot := by
  simp only [ExceptT.wp_apply_eq, ExceptT.run_core_monadLift,
    ExactWPMonad.wp_map, Lean.Order.pushExcept]

/-! ## `ReaderT (OracleComp spec)` WP normalization -/

theorem wp_ReaderT_bind {ρ : Type} (x : ReaderT ρ (OracleComp spec) α)
    (f : α → ReaderT ρ (OracleComp spec) β) (post : β → ρ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (x >>= f) post epost =
      fun r => Std.WP.wp x (fun a r' => Std.WP.wp (f a) post epost r')
        epost r := by
  funext r
  simp only [ReaderT.wp_apply_eq, ReaderT.run_bind,
    ExactWPMonad.wp_bind]

theorem wp_ReaderT_pure {ρ : Type} (x : α) (post : α → ρ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (pure x : ReaderT ρ (OracleComp spec) α) post epost =
      fun r => post x r :=
  funext fun r => ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞)
      (epost := epost)
    x (fun a => post a r)

@[simp]
theorem wp_ReaderT_read {ρ : Type} (post : ρ → ρ → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (MonadReaderOf.read : ReaderT ρ (OracleComp spec) ρ) post epost =
      fun r => post r r :=
  funext fun r => ExactWPMonad.wp_pure (m := OracleComp spec) (Pred := ℝ≥0∞)
      (epost := epost)
    r (fun a => post a r)

end OracleComp.Quantitative

namespace OracleComp.Quantitative

variable {ι : Type u} {spec : OracleSpec ι}
variable [OracleSpec.IsMeasureSpec spec]
variable {α β : Type}

namespace WriterT

@[simp]
theorem wp_bind {ω : Type} [Monoid ω] (x : _root_.WriterT ω (OracleComp spec) α)
    (f : α → _root_.WriterT ω (OracleComp spec) β) (post : β → ω → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (x >>= f) post epost =
      fun w => Std.WP.wp x
        (fun a w' => Std.WP.wp (f a) post epost w') epost w := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq,
    _root_.WriterT.run_bind, ExactWPMonad.wp_bind, ExactWPMonad.wp_map, mul_assoc]

@[simp]
theorem wp_pure {ω : Type} [Monoid ω] (x : α) (post : α → ω → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (pure x : _root_.WriterT ω (OracleComp spec) α) post epost =
      fun w => post x w := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq,
    _root_.WriterT.run_pure, ExactWPMonad.wp_pure, mul_one]

@[simp]
theorem wp_tell {ω : Type} [Monoid ω] (out : ω) (post : PUnit → ω → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (MonadWriter.tell out : _root_.WriterT ω (OracleComp spec) PUnit) post
      epost = fun w => post ⟨⟩ (w * out) := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq,
    _root_.WriterT.run_tell, ExactWPMonad.wp_pure]

@[simp]
theorem wp_monadLift {ω : Type} [Monoid ω] (oa : OracleComp spec α)
    (post : α → ω → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (MonadLift.monadLift oa : _root_.WriterT ω (OracleComp spec) α) post
      epost = fun w => Std.WP.wp oa (fun a => post a w) epost := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq,
    _root_.WriterT.run_core_monadLift, ExactWPMonad.wp_map, mul_one]

@[simp]
theorem wp_map {ω : Type} [Monoid ω] (f : α → β)
    (x : _root_.WriterT ω (OracleComp spec) α) (post : β → ω → ℝ≥0∞) (epost : EStack⟨⟩) :
    Std.WP.wp (f <$> x) post epost =
      Std.WP.wp x (fun a w => post (f a) w) epost := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq,
    _root_.WriterT.run_map, ExactWPMonad.wp_map]

end WriterT

end OracleComp.Quantitative
