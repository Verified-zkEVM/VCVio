/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import VCVio.ProgramLogic.Tactics.Common
public import VCVio.ProgramLogic.Relational.Basic
public meta import VCVio.ProgramLogic.Tactics.Relational.Internals
public import PolyFun.Control.Do.Spec

/-!
# Unary VCGen structural rules
-/

public meta section

open Lean Elab Tactic Meta
open scoped WriterT.MonoidWP Lean.Order

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Unary

universe u v

/-- Cached raw-`wp` structural leaf for `pure`.

The equality theorem `wp_pure` remains the canonical rewrite rule.
This lower-bound form lets raw `wp` goals use the cached `@[vcspec]`
backward-rule path before falling back to `@[wpStep]`. -/
theorem wp_pure_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α : Type} (x : α)
    (post : α → ENNReal) :
    post x ≤ wp⟦(pure x : OracleComp spec α)⟧ post := by
  rw [OracleComp.ProgramLogic.wp_pure]

/-- Cached raw-`wp` structural leaf for functorial map. -/
theorem wp_map_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec]
    {α β : Type}
    (f : α → β) (oa : OracleComp spec α) (post : β → ENNReal) :
    wp⟦oa⟧ (post ∘ f) ≤ wp⟦f <$> oa⟧ post := by
  rw [OracleComp.ProgramLogic.wp_map]

/-- Cached raw-`wp` structural leaf for conditionals. -/
theorem wp_ite_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec]
    {α : Type} (c : Prop) [Decidable c]
    (oa ob : OracleComp spec α) (post : α → ENNReal) :
    (if c then wp⟦oa⟧ post else wp⟦ob⟧ post) ≤ wp⟦if c then oa else ob⟧ post := by
  rw [OracleComp.ProgramLogic.wp_ite]

/-- Cached raw-`wp` structural leaf for dependent conditionals. -/
theorem wp_dite_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec]
    {α : Type} (c : Prop) [Decidable c]
    (oa : c → OracleComp spec α) (ob : ¬c → OracleComp spec α) (post : α → ENNReal) :
    (if h : c then wp⟦oa h⟧ post else wp⟦ob h⟧ post) ≤ wp⟦dite c oa ob⟧ post := by
  rw [OracleComp.ProgramLogic.wp_dite]

/-- Cached raw-`wp` structural leaf for `replicate (n + 1)`. -/
theorem wp_replicate_succ_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α : Type}
    (oa : OracleComp spec α) (n : Nat) (post : List α → ENNReal) :
    wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs))) ≤
      wp⟦oa.replicate (n + 1)⟧ post := by
  rw [OracleComp.ProgramLogic.wp_replicate_succ]

/-- Cached raw-`wp` structural leaf for `List.mapM` on `x :: xs`. -/
theorem wp_list_mapM_cons_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec]
    {α β : Type}
    (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ENNReal) :
    wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys))) ≤
      wp⟦(x :: xs).mapM f⟧ post := by
  rw [OracleComp.ProgramLogic.wp_list_mapM_cons]

/-- Cached raw-`wp` structural leaf for `List.foldlM` on `x :: xs`. -/
theorem wp_list_foldlM_cons_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α σ : Type}
    (x : α) (xs : List α) (f : σ → α → OracleComp spec σ)
    (init : σ) (post : σ → ENNReal) :
    wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post) ≤
      wp⟦(x :: xs).foldlM f init⟧ post := by
  rw [OracleComp.ProgramLogic.wp_list_foldlM_cons]

/-- Cached raw-`wp` structural leaf for oracle queries. -/
theorem wp_query_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec]
    (t : spec.Domain) (post : spec.Range t → ENNReal) :
    (∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t) ≤
      wp⟦(query t : OracleComp spec (spec.Range t))⟧ post := by
  simpa using le_of_eq (OracleComp.ProgramLogic.wp_HasQuery_query (spec := spec) t post).symm

/-- Cached raw-`wp` structural leaf for `HasQuery.query`. -/
theorem wp_HasQuery_query_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec]
    (t : spec.Domain) (post : spec.Range t → ENNReal) :
    (∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t) ≤
      wp⟦(HasQuery.query t : OracleComp spec (spec.Range t))⟧ post := by
  simpa using le_of_eq (OracleComp.ProgramLogic.wp_HasQuery_query (spec := spec) t post).symm

/-- Cached raw-`wp` structural leaf for uniform sampling. -/
theorem wp_uniformSample_le_vcspec {α : Type} [SampleableType α] (post : α → ENNReal) :
    (∫⁻ y, y ∂𝒟[post <$> ($ᵗ α : ProbComp α)]) ≤
      wp⟦($ᵗ α : ProbComp α)⟧ post := by
  rw [OracleComp.ProgramLogic.wp_uniformSample]

/-- Generic core triple bind step with the intermediate postcondition fixed to
the weakest precondition of the continuation. This is the monad-generic
counterpart of `OracleComp.ProgramLogic.triple_bind_wp`, and lets unary
automation walk transformer-stack `do` blocks without guessing a user cut. -/
theorem stdDoTriple_bind_wp {m : Type u → Type v}
    {Pred EPred : Type u} {α β : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {pre : Pred} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    Std.WP.Triple x pre (fun a => Std.WP.wp (f a) post epost) epost →
      Std.WP.Triple (x >>= f) pre post epost := by
  intro h
  exact Std.WP.Triple.bind x f (fun a => Std.WP.wp (f a) post epost) h
    (fun _ => ⟨Lean.Order.PartialOrder.rel_refl⟩)

theorem wp_StateT_get_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {σ : Type u} (post : σ → σ → Pred) (epost : EPred) :
    Std.WP.wp (MonadStateOf.get : StateT σ m σ) post epost =
      fun s => Std.WP.wp (pure (s, s) : m (σ × σ))
        (fun p : σ × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_get_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {σ : Type u} (post : σ → σ → Pred) (epost : EPred) :
    Std.WP.wp (StateT.get : StateT σ m σ) post epost =
      fun s => Std.WP.wp (pure (s, s) : m (σ × σ))
        (fun p : σ × σ => post p.1 p.2) epost :=
  rfl

theorem stdDoTriple_StateT_get_of_rel {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {σ : Type u} (pre : σ → Pred) (post : σ → σ → Pred) (epost : EPred)
    (h : ∀ s, pre s ⊑ post s s) :
    Std.WP.Triple (StateT.get : StateT σ m σ) pre post epost :=
  ⟨fun s => Lean.Order.PartialOrder.rel_trans (h s)
    (Std.WP.WPMonad.le_wp_get_StateT_apply post epost s)⟩

theorem wp_StateT_set_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {σ : Type u} (s' : σ) (post : PUnit → σ → Pred) (epost : EPred) :
    Std.WP.wp (MonadStateOf.set s' : StateT σ m PUnit) post epost =
      fun _ => Std.WP.wp (pure (PUnit.unit, s') : m (PUnit × σ))
        (fun p : PUnit × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_run_get_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {σ : Type u} (s : σ) (post : σ → σ → Pred) (epost : EPred) :
    Std.WP.wp ((MonadStateOf.get : StateT σ m σ).run s)
        (fun p : σ × σ => post p.1 p.2) epost =
      Std.WP.wp (pure (s, s) : m (σ × σ)) (fun p : σ × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_run_get_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {σ : Type u} (s : σ) (post : σ → σ → Pred) (epost : EPred) :
    Std.WP.wp ((StateT.get : StateT σ m σ).run s)
        (fun p : σ × σ => post p.1 p.2) epost =
      Std.WP.wp (pure (s, s) : m (σ × σ)) (fun p : σ × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_run_set_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {σ : Type u} (s s' : σ) (post : PUnit → σ → Pred) (epost : EPred) :
    Std.WP.wp ((MonadStateOf.set s' : StateT σ m PUnit).run s)
        (fun p : PUnit × σ => post p.1 p.2) epost =
      Std.WP.wp (pure (PUnit.unit, s') : m (PUnit × σ))
        (fun p : PUnit × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_run_set_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {σ : Type u} (s s' : σ) (post : PUnit → σ → Pred) (epost : EPred) :
    Std.WP.wp ((StateT.set s' : StateT σ m PUnit).run s)
        (fun p : PUnit × σ => post p.1 p.2) epost =
      Std.WP.wp (pure (PUnit.unit, s') : m (PUnit × σ))
        (fun p : PUnit × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_map_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {σ α β : Type u} (f : α → β) (x : StateT σ m α) (post : β → σ → Pred)
    (epost : EPred) :
    Std.WP.wp (f <$> x) post epost =
      fun s => Std.WP.wp ((f <$> x).run s)
        (fun p : β × σ => post p.1 p.2) epost :=
  rfl

theorem wp_ReaderT_read_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {ρ : Type u} (post : ρ → ρ → Pred) (epost : EPred) :
    Std.WP.wp (MonadReaderOf.read : ReaderT ρ m ρ) post epost =
      fun r => Std.WP.wp (pure r : m ρ) (fun a => post a r) epost :=
  rfl

theorem wp_ReaderT_read_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {ρ : Type u} (post : ρ → ρ → Pred) (epost : EPred) :
    Std.WP.wp (ReaderT.read : ReaderT ρ m ρ) post epost =
      fun r => Std.WP.wp (pure r : m ρ) (fun a => post a r) epost :=
  rfl

theorem stdDoTriple_ReaderT_read_of_rel {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {ρ : Type u} (pre : ρ → Pred) (post : ρ → ρ → Pred) (epost : EPred)
    (h : ∀ r, pre r ⊑ post r r) :
    Std.WP.Triple (MonadReaderOf.read : ReaderT ρ m ρ) pre post epost :=
  ⟨fun r => Lean.Order.PartialOrder.rel_trans (h r)
    (Std.WP.WPMonad.le_wp_read_ReaderT_apply post epost r)⟩

theorem wp_ReaderT_run_read_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {ρ : Type u} (r : ρ) (post : ρ → ρ → Pred) (epost : EPred) :
    Std.WP.wp ((MonadReaderOf.read : ReaderT ρ m ρ).run r) (fun a : ρ => post a r)
        epost =
      Std.WP.wp (pure r : m ρ) (fun a : ρ => post a r) epost :=
  rfl

theorem wp_ReaderT_run_read_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {ρ : Type u} (r : ρ) (post : ρ → ρ → Pred) (epost : EPred) :
    Std.WP.wp ((ReaderT.read : ReaderT ρ m ρ).run r) (fun a : ρ => post a r)
        epost =
      Std.WP.wp (pure r : m ρ) (fun a : ρ => post a r) epost :=
  rfl

theorem wp_OptionT_run_StateT_get {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {σ : Type} (s : σ)
    (post : σ → σ → ENNReal)
    (epost : EStack⟨Unit → ENNReal⟩) :
    wp⟦((StateT.get : StateT σ (OptionT (OracleComp spec)) σ).run s).run⟧
      (Lean.Order.pushOption (fun p : σ × σ => post p.1 p.2) epost.fst) = post s s := by
  change wp⟦(pure (some (s, s)) : OracleComp spec (Option (σ × σ)))⟧
      (Lean.Order.pushOption (fun p : σ × σ => post p.1 p.2) epost.fst) = post s s
  rw [OracleComp.ProgramLogic.wp_pure, Lean.Order.pushOption_some]

theorem wp_OptionT_run_StateT_set {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec]
    {σ : Type} (s s' : σ)
    (post : PUnit → σ → ENNReal)
    (epost : EStack⟨Unit → ENNReal⟩) :
    wp⟦((StateT.set s' : StateT σ (OptionT (OracleComp spec)) PUnit).run s).run⟧
      (Lean.Order.pushOption (fun p : PUnit × σ => post p.1 p.2) epost.fst) =
        post PUnit.unit s' := by
  change wp⟦(pure (some (PUnit.unit, s')) : OracleComp spec (Option (PUnit × σ)))⟧
      (Lean.Order.pushOption (fun p : PUnit × σ => post p.1 p.2) epost.fst) =
        post PUnit.unit s'
  rw [OracleComp.ProgramLogic.wp_pure, Lean.Order.pushOption_some]

theorem wp_OptionT_run_lift {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α : Type}
    (oa : OracleComp spec α) (post : α → ENNReal)
    (epost : EStack⟨Unit → ENNReal⟩) :
    wp⟦(OptionT.lift oa).run⟧
      (Lean.Order.pushOption post epost.fst) =
        wp⟦oa⟧ post := by
  change wp⟦(oa >>= fun a => pure (some a) : OracleComp spec (Option α))⟧
      (Lean.Order.pushOption post epost.fst) =
    wp⟦oa⟧ post
  rw [OracleComp.ProgramLogic.wp_bind]
  refine congrArg (wp⟦oa⟧) ?_
  funext a
  rw [OracleComp.ProgramLogic.wp_pure, Lean.Order.pushOption_some]

theorem wp_OptionT_run_StateT_monadLift_lift {ι : Type u}
    {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec]
    {σ α : Type} (oa : OracleComp spec α) (s : σ) (post : α → σ → ENNReal)
    (epost : EStack⟨Unit → ENNReal⟩) :
    wp⟦((MonadLift.monadLift (OptionT.lift oa) :
        StateT σ (OptionT (OracleComp spec)) α).run s).run⟧
      (Lean.Order.pushOption (fun p : α × σ => post p.1 p.2) epost.fst) =
        wp⟦oa⟧ (fun a => post a s) := by
  simp [MonadLift.monadLift, OptionT.run_lift,
    Lean.Order.pushOption]

theorem wp_StateT_OptionT_monadLift_lift {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {σ α : Type}
    (oa : OracleComp spec α) (post : α → σ → ENNReal)
    (epost : EStack⟨Unit → ENNReal⟩) :
    Std.WP.wp
      (MonadLift.monadLift (OptionT.lift oa) : StateT σ (OptionT (OracleComp spec)) α)
      post epost =
        fun s => wp⟦oa⟧
          (fun a => post a s) := by
  funext s
  change wp⟦((MonadLift.monadLift (OptionT.lift oa) :
        StateT σ (OptionT (OracleComp spec)) α).run s).run⟧
      (Lean.Order.pushOption (fun p : α × σ => post p.1 p.2) epost.fst) =
        wp⟦oa⟧ (fun a => post a s)
  exact wp_OptionT_run_StateT_monadLift_lift (spec := spec) oa s post epost

theorem wp_OptionT_run_StateT_monadLift_lift_map {ι : Type u}
    {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec]
    {σ α β : Type} (oa : OracleComp spec α) (s : σ) (f : α × σ → β)
    (post : β → ENNReal) (nonePost : ENNReal) :
    wp⟦((MonadLift.monadLift (OptionT.lift oa) :
        StateT σ (OptionT (OracleComp spec)) α).run s).run⟧
      (fun o => match Option.map f o with | some b => post b | none => nonePost) =
        wp⟦oa⟧
          (fun a => post (f (a, s))) := by
  simp [MonadLift.monadLift, OptionT.run_lift]

theorem wp_ReaderT_map_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.WP.Assertion Pred] [Std.WP.Assertion EPred]
    [Std.WP.WPMonad m Pred EPred]
    {ρ α β : Type u} (f : α → β) (x : ReaderT ρ m α) (post : β → ρ → Pred)
    (epost : EPred) :
    Std.WP.wp (f <$> x) post epost =
      fun r => Std.WP.wp ((f <$> x).run r) (fun b : β => post b r) epost :=
  rfl

attribute [vcspec]
  Std.WP.Spec.pure
  wp_pure_le_vcspec
  wp_map_le_vcspec
  wp_ite_le_vcspec
  wp_dite_le_vcspec
  wp_replicate_succ_le_vcspec
  wp_list_mapM_cons_le_vcspec
  wp_list_foldlM_cons_le_vcspec
  wp_query_le_vcspec
  wp_HasQuery_query_le_vcspec
  wp_uniformSample_le_vcspec
  -- StateT
  Std.WP.Spec.get_StateT
  Std.WP.Spec.set_StateT
  Std.WP.Spec.modifyGet_StateT
  Std.WP.Spec.monadLift_StateT
  -- ReaderT
  Std.WP.Spec.read_ReaderT
  Std.WP.Spec.monadLift_ReaderT
  Std.WP.Spec.adapt_ReaderT
  Std.WP.Spec.withReader_ReaderT
  -- WriterT
  Std.WP.Spec.tell_WriterT
  Std.WP.Spec.monadLift_WriterT
  Std.WP.Spec.mk_WriterT
  WriterT.le_wp_tell
  WriterT.le_wp_monadLift
  -- OptionT
  Std.WP.Spec.run_OptionT
  Std.WP.Spec.throw_OptionT
  Std.WP.Spec.tryCatch_OptionT
  Std.WP.Spec.orElse_OptionT
  Std.WP.Spec.monadLift_OptionT
  -- ExceptT
  Std.WP.Spec.run_ExceptT
  Std.WP.Spec.throw_ExceptT
  Std.WP.Spec.tryCatch_ExceptT
  Std.WP.Spec.orElse_ExceptT
  Std.WP.Spec.adapt_ExceptT
  Std.WP.Spec.monadLift_ExceptT
  -- Lifted MonadExceptOf
  Std.WP.Spec.throw_MonadExcept
  Std.WP.Spec.tryCatch_MonadExcept
  Std.WP.Spec.throw_ReaderT
  Std.WP.Spec.throw_StateT
  Std.WP.Spec.throw_ExceptT_lift
  Std.WP.Spec.throw_Option_lift
  Std.WP.Spec.tryCatch_ReaderT
  Std.WP.Spec.tryCatch_StateT
  Std.WP.Spec.tryCatch_ExceptT_lift
  Std.WP.Spec.tryCatch_OptionT_lift
  -- Generic monad-transformer hooks
  Std.WP.Spec.monadMap_StateT
  Std.WP.Spec.monadMap_ReaderT
  Std.WP.Spec.monadMap_ExceptT
  Std.WP.Spec.monadMap_OptionT
  Std.WP.Spec.monadMap_refl
  Std.WP.Spec.monadMap_trans
  Std.WP.Spec.liftWith_StateT
  Std.WP.Spec.liftWith_ReaderT
  Std.WP.Spec.liftWith_ExceptT
  Std.WP.Spec.liftWith_OptionT
  Std.WP.Spec.liftWith_refl
  Std.WP.Spec.liftWith_trans
  Std.WP.Spec.restoreM_StateT
  Std.WP.Spec.restoreM_ReaderT
  Std.WP.Spec.restoreM_ExceptT
  Std.WP.Spec.restoreM_OptionT
  Std.WP.Spec.restoreM_refl

end Unary
end TacticInternals
end OracleComp.ProgramLogic
