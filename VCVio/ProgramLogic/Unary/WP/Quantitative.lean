/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Control.Monad.Algebra
public import ToMathlib.Control.OptionT
public import ToMathlib.Control.StateT
public import ToMathlib.Control.WriterT
public import VCVio.EvalDist.Expectation
public import VCVio.EvalDist.Monad.Basic
public import VCVio.OracleComp.EvalDist
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

open ENNReal
open Lean.Order
open Std.Internal.Do
open scoped WriterT.MonoidWP

universe u v

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [IsUniformSpec spec]
variable {α β : Type}

/-! ## Expectation algebra and the `MAlgOrdered` instance -/

/-- Expectation-style algebra for oracle computations returning `ℝ≥0∞`: the expectation
(`OracleComp.EvalDist.expectedValue`) of the identity functional. -/
noncomputable def μ (oa : OracleComp spec ℝ≥0∞) : ℝ≥0∞ :=
  OracleComp.EvalDist.expectedValue oa fun x => x

lemma μ_bind_eq_tsum {α : Type}
    (oa : OracleComp spec α) (ob : α → OracleComp spec ℝ≥0∞) :
    μ (oa >>= ob) = ∑' x, Pr[= x | oa] * μ (ob x) := by
  unfold μ
  rw [OracleComp.EvalDist.expectedValue_bind, OracleComp.EvalDist.expectedValue_def]

noncomputable instance instMAlgOrdered : MAlgOrdered (OracleComp spec) ℝ≥0∞ where
  μ := μ (spec := spec)
  μ_pure x := by simp [μ]
  μ_bind_mono f g hfg x := by
    simp_rw [μ_bind_eq_tsum]
    gcongr with a
    exact hfg a

end OracleComp.ProgramLogic

namespace OracleComp.Quantitative

/-! ## `Std.Internal.Do.WP` instance for `OracleComp` -/

variable {ι : Type u} {spec : OracleSpec ι}
variable [IsUniformSpec spec]
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
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) ((x >>= f).run s)
    (fun p : β × σ => post p.1 p.2) = _
  rw [StateT.run_bind]
  exact MAlgOrdered.wp_bind (m := OracleComp spec) (l := ℝ≥0∞) (x.run s)
    (fun p => (f p.1).run p.2) (fun p : β × σ => post p.1 p.2)

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
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (oa >>= fun a => pure (a, s))
      (fun p : α × σ => post p.1 p.2) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa (fun a => post a s)
  simp only [MAlgOrdered.wp_bind, MAlgOrdered.wp_pure]

/-! ## `OptionT (OracleComp spec)` WP normalization -/

theorem wp_OptionT_bind (x : OptionT (OracleComp spec) α)
    (f : α → OptionT (OracleComp spec) β) (post : β → ℝ≥0∞)
    (epost : EPost.Cons ℝ≥0∞ EPost.Nil) :
    Std.Internal.Do.wp (x >>= f) post epost =
      Std.Internal.Do.wp x (fun a => Std.Internal.Do.wp (f a) post epost) epost := by
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) ((x >>= f).run)
      (epost.pushOption post) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) x.run
      (epost.pushOption fun a =>
        MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (f a).run
          (epost.pushOption post))
  simp only [OptionT.run_bind, Option.elimM, MAlgOrdered.wp_bind]
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
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (oa >>= fun a => pure (some a)) (epost.pushOption post) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post
  simp only [MAlgOrdered.wp_bind, MAlgOrdered.wp_pure]

theorem wp_OptionT_lift (oa : OracleComp spec α) (post : α → ℝ≥0∞)
    (epost : EPost.Cons ℝ≥0∞ EPost.Nil) :
    Std.Internal.Do.wp (OptionT.lift oa : OptionT (OracleComp spec) α) post epost =
      Std.Internal.Do.wp oa post Lean.Order.bot :=
  wp_OptionT_monadLift oa post epost

theorem wp_OptionT_map (f : α → β) (x : OptionT (OracleComp spec) α)
    (post : β → ℝ≥0∞) (epost : EPost.Cons ℝ≥0∞ EPost.Nil) :
    Std.Internal.Do.wp (f <$> x) post epost = Std.Internal.Do.wp x (fun a => post (f a)) epost := by
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) ((f <$> x).run)
      (epost.pushOption post) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) x.run
      (epost.pushOption fun a => post (f a))
  rw [OptionT.run_map, MAlgOrdered.wp_map]
  congr 1 with o
  cases o <;> rfl

/-! ## `ExceptT (OracleComp spec)` WP normalization -/

theorem wp_ExceptT_bind {ε : Type} (x : ExceptT ε (OracleComp spec) α)
    (f : α → ExceptT ε (OracleComp spec) β) (post : β → ℝ≥0∞)
    (epost : EPost.Cons (ε → ℝ≥0∞) EPost.Nil) :
    Std.Internal.Do.wp (x >>= f) post epost =
      Std.Internal.Do.wp x (fun a => Std.Internal.Do.wp (f a) post epost) epost := by
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) ((x >>= f).run)
      (epost.pushExcept post) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) x.run
      (epost.pushExcept fun a =>
        MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (f a).run
          (epost.pushExcept post))
  rw [ExceptT.run_bind, MAlgOrdered.wp_bind]
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
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (Except.ok <$> oa) (epost.pushExcept post) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post
  rw [map_eq_bind_pure_comp]
  rw [MAlgOrdered.wp_bind]
  congr 1
  funext a
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (pure (Except.ok a)) (epost.pushExcept post) = post a
  exact MAlgOrdered.wp_pure (m := OracleComp spec) (l := ℝ≥0∞)
    (Except.ok a) (epost.pushExcept post)

/-! ## `ReaderT (OracleComp spec)` WP normalization -/

@[simp]
theorem wp_ReaderT_bind {ρ : Type} (x : ReaderT ρ (OracleComp spec) α)
    (f : α → ReaderT ρ (OracleComp spec) β) (post : β → ρ → ℝ≥0∞) :
    Std.Internal.Do.wp (x >>= f) post Lean.Order.bot =
      fun r => Std.Internal.Do.wp x (fun a r' => Std.Internal.Do.wp (f a) post Lean.Order.bot r')
        Lean.Order.bot r := by
  funext r
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) ((x >>= f).run r)
      (fun b => post b r) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (x.run r)
      (fun a => MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) ((f a).run r)
        (fun b => post b r))
  rw [ReaderT.run_bind, MAlgOrdered.wp_bind]

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
variable [IsUniformSpec spec]
variable {α β : Type}

namespace WriterT

@[simp]
theorem wp_bind {ω : Type} [Monoid ω] (x : _root_.WriterT ω (OracleComp spec) α)
    (f : α → _root_.WriterT ω (OracleComp spec) β) (post : β → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (x >>= f) post Lean.Order.bot =
      fun w => Std.Internal.Do.wp x
        (fun a w' => Std.Internal.Do.wp (f a) post Lean.Order.bot w') Lean.Order.bot w := by
  funext w
  change Std.Internal.Do.wp ((x >>= f).run) (fun p : β × ω => post p.1 (w * p.2))
      Lean.Order.bot =
    Std.Internal.Do.wp x.run
      (fun p : α × ω =>
        Std.Internal.Do.wp (f p.1).run (fun q : β × ω => post q.1 ((w * p.2) * q.2))
          Lean.Order.bot)
      Lean.Order.bot
  rw [_root_.WriterT.run_bind]
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (x.run >>= fun p : α × ω =>
        (fun q : β × ω => (q.1, p.2 * q.2)) <$> (f p.1).run)
      (fun p : β × ω => post p.1 (w * p.2)) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) x.run
      (fun p : α × ω =>
        MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) (f p.1).run
          (fun q : β × ω => post q.1 ((w * p.2) * q.2)))
  simp only [MAlgOrdered.wp_bind, MAlgOrdered.wp_map, mul_assoc]

@[simp]
theorem wp_pure {ω : Type} [Monoid ω] (x : α) (post : α → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (pure x : _root_.WriterT ω (OracleComp spec) α) post Lean.Order.bot =
      fun w => post x w := by
  funext w
  change Std.Internal.Do.wp ((pure x : _root_.WriterT ω (OracleComp spec) α).run)
      (fun p : α × ω => post p.1 (w * p.2)) Lean.Order.bot = post x w
  rw [_root_.WriterT.run_pure]
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (pure (x, 1) : OracleComp spec (α × ω))
      (fun p : α × ω => post p.1 (w * p.2)) = post x w
  rw [MAlgOrdered.wp_pure, mul_one]

@[simp]
theorem wp_tell {ω : Type} [Monoid ω] (out : ω) (post : PUnit → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadWriter.tell out : _root_.WriterT ω (OracleComp spec) PUnit) post
      Lean.Order.bot = fun w => post ⟨⟩ (w * out) := by
  funext w
  change Std.Internal.Do.wp
    (_root_.WriterT.run (MonadWriter.tell out : _root_.WriterT ω (OracleComp spec) PUnit))
      (fun p : PUnit × ω => post p.1 (w * p.2)) Lean.Order.bot = post ⟨⟩ (w * out)
  rw [_root_.WriterT.run_tell]
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      (pure (⟨⟩, out) : OracleComp spec (PUnit × ω))
      (fun p : PUnit × ω => post p.1 (w * p.2)) = post ⟨⟩ (w * out)
  rw [MAlgOrdered.wp_pure]

@[simp]
theorem wp_monadLift {ω : Type} [Monoid ω] (oa : OracleComp spec α)
    (post : α → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (MonadLift.monadLift oa : _root_.WriterT ω (OracleComp spec) α) post
      Lean.Order.bot = fun w => Std.Internal.Do.wp oa (fun a => post a w) Lean.Order.bot := by
  funext w
  change Std.Internal.Do.wp ((MonadLift.monadLift oa : _root_.WriterT ω (OracleComp spec) α).run)
      (fun p : α × ω => post p.1 (w * p.2)) Lean.Order.bot =
    Std.Internal.Do.wp oa (fun a => post a w) Lean.Order.bot
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) ((fun a => (a, 1)) <$> oa)
      (fun p : α × ω => post p.1 (w * p.2)) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa (fun a => post a w)
  simp only [MAlgOrdered.wp_map, mul_one]

@[simp]
theorem wp_map {ω : Type} [Monoid ω] (f : α → β)
    (x : _root_.WriterT ω (OracleComp spec) α) (post : β → ω → ℝ≥0∞) :
    Std.Internal.Do.wp (f <$> x) post Lean.Order.bot =
      Std.Internal.Do.wp x (fun a w => post (f a) w) Lean.Order.bot := by
  funext w
  change Std.Internal.Do.wp (_root_.WriterT.run (f <$> x))
      (fun p : β × ω => post p.1 (w * p.2))
      Lean.Order.bot =
    Std.Internal.Do.wp (WriterT.run x) (fun p : α × ω => post (f p.1) (w * p.2))
      Lean.Order.bot
  rw [_root_.WriterT.run_map]
  change MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞)
      ((fun p : α × ω => (f p.1, p.2)) <$> x.run)
      (fun p : β × ω => post p.1 (w * p.2)) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) x.run
      (fun p : α × ω => post (f p.1) (w * p.2))
  rw [MAlgOrdered.wp_map]

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
