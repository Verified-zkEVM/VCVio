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

The expectation algebra on `OracleComp spec` gives a core `WPMonad` interpretation
with `ℝ≥0∞` assertions. Enable it with `open scoped OracleComp.Quantitative`.
The algebra-to-WP bridge and lattice instances come from PolyFun. The transformer
lemmas describe expectation after running state, reader, option, exception, and writer layers.

This interpretation is quantitative. Structural reachability and its qualitative
interpretation are independent of the choice of probability semantics.
-/

@[expose] public section

open ENNReal MeasureTheory
open Lean.Order
open Std.Internal.Do
open scoped WriterT.MonoidWP

universe u v

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
variable {α β : Type}

/-! ## Expectation algebra and the `MAlgOrdered` instance -/

/-- The nonnegative expectation algebra under the configured oracle answer measures. -/
noncomputable instance instMAlgOrdered : MAlgOrdered (OracleComp spec) ℝ≥0∞ :=
  MeasureProgramLogic.toMAlgOrdered (OracleComp spec)

/-- The expectation of the identity under the configured oracle answer measures. -/
noncomputable def μ (oa : OracleComp spec ℝ≥0∞) : ℝ≥0∞ :=
  MAlgOrdered.μ oa

end OracleComp.ProgramLogic

namespace OracleComp.Quantitative

/-! ## `Std.Internal.Do.WP` instance for `OracleComp` -/

variable {ι : Type u} {spec : OracleSpec ι}
variable [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
variable {α β : Type}

/-- Core weakest preconditions from the quantitative expectation algebra.
Enable with `open scoped OracleComp.Quantitative`. -/
noncomputable scoped instance instWP :
    Std.Internal.Do.WPMonad (OracleComp spec) ℝ≥0∞ Std.Internal.Do.EPost.Nil :=
  MAlgOrdered.toWPMonad

/-! ## Definitional alignment with `MAlgOrdered.wp`

The keystone lemma confirms `Std.Internal.Do.wp` agrees with `MAlgOrdered.wp`
on the nose, so every existing quantitative `wp_*` theorem in
`HoareTriple.lean` transports for free when the user rewrites
`Std.Internal.Do.wp _ _ _ ↦ MAlgOrdered.wp _ _`.

The epost argument is `⊥` to match core's `⦃ _ ⦄ _ ⦃ _ ⦄` notation in
`Std.Internal.Do.Triple.Basic`. The `WP` instance for `OracleComp` ignores the
epost argument entirely, so any element of `EPost.Nil` would yield the
same value. -/

theorem wp_eq_mAlgOrdered_wp
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Std.Internal.Do.wp oa post Lean.Order.bot =
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post := rfl

theorem wp_eq_mAlgOrdered_wp_epost
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) (epost : Std.Internal.Do.EPost.Nil) :
    Std.Internal.Do.wp oa post epost =
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post := rfl

/-! ## `StateT (OracleComp spec)` WP normalization -/

@[simp]
theorem wp_StateT_bind {σ : Type} (x : StateT σ (OracleComp spec) α)
    (f : α → StateT σ (OracleComp spec) β) (post : β → σ → ℝ≥0∞) :
    Std.Internal.Do.wp (StateT.bind x f) post Lean.Order.bot =
      fun s => Std.Internal.Do.wp x (fun a s' => Std.Internal.Do.wp (f a) post Lean.Order.bot s')
        Lean.Order.bot s := by
  funext s
  simp only [StateT.wp_apply_eq, ← StateT.monad_bind_def, StateT.run_bind, MAlgOrdered.toWPMonad_wp,
    MAlgOrdered.wp_bind]

@[simp]
theorem wp_StateT_bind' {σ : Type} (x : StateT σ (OracleComp spec) α)
    (f : α → StateT σ (OracleComp spec) β) (post : β → σ → ℝ≥0∞) :
    Std.Internal.Do.wp (x >>= f) post Lean.Order.bot =
      fun s => Std.Internal.Do.wp x (fun a s' => Std.Internal.Do.wp (f a) post Lean.Order.bot s')
        Lean.Order.bot s :=
  wp_StateT_bind x f post

@[simp]
theorem wp_StateT_pure {σ : Type} (x : α) (post : α → σ → ℝ≥0∞) :
    Std.Internal.Do.wp (pure x : StateT σ (OracleComp spec) α) post Lean.Order.bot =
      fun s => post x s := by
  funext s
  exact MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) (x, s)
    (fun p : α × σ => post p.1 p.2)

theorem wp_StateT_get {σ : Type} (post : σ → σ → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadStateOf.get : StateT σ (OracleComp spec) σ) post Lean.Order.bot =
      fun s => post s s := by
  funext s
  exact MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) (s, s)
    (fun p : σ × σ => post p.1 p.2)

@[simp]
theorem wp_StateT_set {σ : Type} (s' : σ) (post : PUnit → σ → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadStateOf.set s' : StateT σ (OracleComp spec) PUnit) post
      Lean.Order.bot = fun _ => post ⟨⟩ s' := by
  funext s
  exact MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) (PUnit.unit, s')
    (fun p : PUnit × σ => post p.1 p.2)

theorem wp_StateT_modifyGet {σ : Type} (f : σ → α × σ) (post : α → σ → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadStateOf.modifyGet f : StateT σ (OracleComp spec) α) post
      Lean.Order.bot = fun s => post (f s).1 (f s).2 := by
  funext s
  exact MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) (f s)
    (fun p : α × σ => post p.1 p.2)

@[simp]
theorem wp_StateT_monadLift {σ : Type} (oa : OracleComp spec α)
    (post : α → σ → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadLift.monadLift oa : StateT σ (OracleComp spec) α) post
      Lean.Order.bot = fun s => Std.Internal.Do.wp oa (fun a => post a s) Lean.Order.bot := by
  funext s
  simp only [StateT.wp_apply_eq, StateT.run_core_monadLift, MAlgOrdered.toWPMonad_wp,
    MAlgOrdered.wp_bind, MAlgOrdered.wp_pure]

/-! ## `OptionT (OracleComp spec)` WP normalization -/

theorem wp_OptionT_bind (x : OptionT (OracleComp spec) α)
    (f : α → OptionT (OracleComp spec) β) (post : β → ℝ≥0∞)
    (epost : EPost.Cons ℝ≥0∞ EPost.Nil) :
    Std.Internal.Do.wp (x >>= f) post epost =
      Std.Internal.Do.wp x (fun a => Std.Internal.Do.wp (f a) post epost) epost := by
  simp only [OptionT.wp_apply_eq, MAlgOrdered.toWPMonad_wp, OptionT.run_bind,
    Option.elimM, MAlgOrdered.wp_bind]
  congr 1 with o
  cases o <;> simp [EPost.Cons.pushOption]

theorem wp_OptionT_pure (x : α) (post : α → ℝ≥0∞)
    (epost : EPost.Cons ℝ≥0∞ EPost.Nil) :
    Std.Internal.Do.wp (pure x : OptionT (OracleComp spec) α) post epost = post x :=
  MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) (some x) (epost.pushOption post)

theorem wp_OptionT_failure (post : α → ℝ≥0∞)
    (epost : EPost.Cons ℝ≥0∞ EPost.Nil) :
    Std.Internal.Do.wp (failure : OptionT (OracleComp spec) α) post epost = epost.head :=
  MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) none (epost.pushOption post)

theorem wp_OptionT_monadLift (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (epost : EPost.Cons ℝ≥0∞ EPost.Nil) :
    Std.Internal.Do.wp (MonadLift.monadLift oa : OptionT (OracleComp spec) α) post epost =
      Std.Internal.Do.wp oa post Lean.Order.bot := by
  simp only [OptionT.wp_apply_eq, MAlgOrdered.toWPMonad_wp, OptionT.run_core_monadLift,
    MAlgOrdered.wp_bind, MAlgOrdered.wp_pure, EPost.Cons.pushOption]

theorem wp_OptionT_lift (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (epost : EPost.Cons ℝ≥0∞ EPost.Nil) :
    Std.Internal.Do.wp (OptionT.lift oa : OptionT (OracleComp spec) α) post epost =
      Std.Internal.Do.wp oa post Lean.Order.bot :=
  wp_OptionT_monadLift oa post epost

theorem wp_OptionT_map (f : α → β) (x : OptionT (OracleComp spec) α)
    (post : β → ℝ≥0∞) (epost : EPost.Cons ℝ≥0∞ EPost.Nil) :
    Std.Internal.Do.wp (f <$> x) post epost = Std.Internal.Do.wp x (fun a => post (f a)) epost := by
  simp only [OptionT.wp_apply_eq, MAlgOrdered.toWPMonad_wp, OptionT.run_map,
    MAlgOrdered.wp_map]
  congr 1 with o
  cases o <;> rfl

/-! ## `ExceptT (OracleComp spec)` WP normalization -/

theorem wp_ExceptT_bind {ε : Type} (x : ExceptT ε (OracleComp spec) α)
    (f : α → ExceptT ε (OracleComp spec) β) (post : β → ℝ≥0∞)
    (epost : EPost.Cons (ε → ℝ≥0∞) EPost.Nil) :
    Std.Internal.Do.wp (x >>= f) post epost =
      Std.Internal.Do.wp x (fun a => Std.Internal.Do.wp (f a) post epost) epost := by
  simp only [ExceptT.wp_apply_eq, MAlgOrdered.toWPMonad_wp, ExceptT.run_bind,
    MAlgOrdered.wp_bind]
  congr 1 with ea
  cases ea <;> simp [EPost.Cons.pushExcept, MAlgOrdered.wp_pure]

theorem wp_ExceptT_pure {ε : Type} (x : α) (post : α → ℝ≥0∞)
    (epost : EPost.Cons (ε → ℝ≥0∞) EPost.Nil) :
    Std.Internal.Do.wp (pure x : ExceptT ε (OracleComp spec) α) post epost = post x :=
  MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) (Except.ok x) (epost.pushExcept post)

theorem wp_ExceptT_throw {ε : Type} (e : ε) (post : α → ℝ≥0∞)
    (epost : EPost.Cons (ε → ℝ≥0∞) EPost.Nil) :
    Std.Internal.Do.wp (throw e : ExceptT ε (OracleComp spec) α) post epost = epost.head e :=
  MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) (Except.error e) (epost.pushExcept post)

theorem wp_ExceptT_monadLift {ε : Type} (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (epost : EPost.Cons (ε → ℝ≥0∞) EPost.Nil) :
    Std.Internal.Do.wp (MonadLift.monadLift oa : ExceptT ε (OracleComp spec) α) post epost =
      Std.Internal.Do.wp oa post Lean.Order.bot := by
  simp only [ExceptT.wp_apply_eq, MAlgOrdered.toWPMonad_wp, ExceptT.run_core_monadLift,
    MAlgOrdered.wp_map, EPost.Cons.pushExcept]

/-! ## `ReaderT (OracleComp spec)` WP normalization -/

@[simp]
theorem wp_ReaderT_bind {ρ : Type} (x : ReaderT ρ (OracleComp spec) α)
    (f : α → ReaderT ρ (OracleComp spec) β) (post : β → ρ → ℝ≥0∞) :
    Std.Internal.Do.wp (x >>= f) post Lean.Order.bot =
      fun r => Std.Internal.Do.wp x (fun a r' => Std.Internal.Do.wp (f a) post Lean.Order.bot r')
        Lean.Order.bot r := by
  funext r
  simp only [ReaderT.wp_apply_eq, ReaderT.run_bind, MAlgOrdered.toWPMonad_wp,
    MAlgOrdered.wp_bind]

@[simp]
theorem wp_ReaderT_pure {ρ : Type} (x : α) (post : α → ρ → ℝ≥0∞) :
    Std.Internal.Do.wp (pure x : ReaderT ρ (OracleComp spec) α) post Lean.Order.bot =
      fun r => post x r :=
  funext fun r => MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) x (fun a => post a r)

@[simp]
theorem wp_ReaderT_read {ρ : Type} (post : ρ → ρ → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadReaderOf.read : ReaderT ρ (OracleComp spec) ρ) post Lean.Order.bot =
      fun r => post r r :=
  funext fun r => MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞) r (fun a => post a r)

@[simp]
theorem wp_ReaderT_monadLift {ρ : Type} (oa : OracleComp spec α)
    (post : α → ρ → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadLift.monadLift oa : ReaderT ρ (OracleComp spec) α) post
      Lean.Order.bot = fun r => Std.Internal.Do.wp oa (fun a => post a r) Lean.Order.bot :=
  rfl

end OracleComp.Quantitative

namespace OracleComp.Quantitative

variable {ι : Type u} {spec : OracleSpec ι}
variable [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
variable {α β : Type}

namespace WriterT

@[simp]
theorem wp_bind {ω : Type} [Monoid ω] (x : _root_.WriterT ω (OracleComp spec) α)
    (f : α → _root_.WriterT ω (OracleComp spec) β) (post : β → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (x >>= f) post Lean.Order.bot =
      fun w => Std.Internal.Do.wp x
        (fun a w' => Std.Internal.Do.wp (f a) post Lean.Order.bot w') Lean.Order.bot w := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq, MAlgOrdered.toWPMonad_wp,
    _root_.WriterT.run_bind, MAlgOrdered.wp_bind, MAlgOrdered.wp_map, mul_assoc]

@[simp]
theorem wp_pure {ω : Type} [Monoid ω] (x : α) (post : α → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (pure x : _root_.WriterT ω (OracleComp spec) α) post Lean.Order.bot =
      fun w => post x w := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq, MAlgOrdered.toWPMonad_wp,
    _root_.WriterT.run_pure, MAlgOrdered.wp_pure, mul_one]

@[simp]
theorem wp_tell {ω : Type} [Monoid ω] (out : ω) (post : PUnit → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadWriter.tell out : _root_.WriterT ω (OracleComp spec) PUnit) post
      Lean.Order.bot = fun w => post ⟨⟩ (w * out) := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq, MAlgOrdered.toWPMonad_wp,
    _root_.WriterT.run_tell, MAlgOrdered.wp_pure]

@[simp]
theorem wp_monadLift {ω : Type} [Monoid ω] (oa : OracleComp spec α)
    (post : α → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadLift.monadLift oa : _root_.WriterT ω (OracleComp spec) α) post
      Lean.Order.bot = fun w => Std.Internal.Do.wp oa (fun a => post a w) Lean.Order.bot := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq, MAlgOrdered.toWPMonad_wp,
    _root_.WriterT.run_core_monadLift, MAlgOrdered.wp_map, mul_one]

@[simp]
theorem wp_map {ω : Type} [Monoid ω] (f : α → β)
    (x : _root_.WriterT ω (OracleComp spec) α) (post : β → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (f <$> x) post Lean.Order.bot =
      Std.Internal.Do.wp x (fun a w => post (f a) w) Lean.Order.bot := by
  funext w
  simp only [_root_.WriterT.wp_apply_eq, MAlgOrdered.toWPMonad_wp,
    _root_.WriterT.run_map, MAlgOrdered.wp_map]

end WriterT

/-- `Std.Internal.Do.Triple` agrees with `MAlgOrdered.Triple` propositionally.

Use as a forward iff: `triple_iff_mAlgOrdered_triple.mp` extracts
`pre ≤ MAlgOrdered.wp …` from a `Std.Internal.Do.Triple`, and `.mpr` packages
it back. The two are *not* definitionally equal because `Std.Internal.Do.Triple`
is an inductive wrapper rather than a `def` over `≤`. -/
theorem triple_iff_mAlgOrdered_triple
    (pre : ℝ≥0∞) (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Std.Internal.Do.Triple oa pre post Lean.Order.bot ↔
      MAlgOrdered.Triple (m := OracleComp spec) (l := ℝ≥0∞) pre oa post :=
  Std.Internal.Do.Triple.iff

end OracleComp.Quantitative
