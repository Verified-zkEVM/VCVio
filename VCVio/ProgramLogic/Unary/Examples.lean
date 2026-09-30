/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Examples for quantitative `OracleComp` triples
-/

@[expose] public section

open ENNReal MeasureTheory

universe u

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [OracleSpec.IsMeasureSpec spec]
variable {α β : Type}

example (x : α) (post : α → ℝ≥0∞) :
    wp⟦(pure x : OracleComp spec α)⟧ post = post x :=
  wp_pure (spec := spec) x post

example (pre : ℝ≥0∞) (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (cut : α → ℝ≥0∞) (post : β → ℝ≥0∞)
    (hoa : Triple pre oa cut)
    (hob : ∀ x, Triple (cut x) (ob x) post) :
    Triple pre (oa >>= ob) post :=
  triple_bind (spec := spec) hoa hob

example (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp⟦(query t : OracleComp spec (spec.Range t))⟧ post =
      ∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t :=
  wp_query (spec := spec) t post

end OracleComp.ProgramLogic

section ExactTransformers

/-! Core's transformer interpretations over an exact base are exact, so `wp` distributes over
their `bind` with equality. -/

open Std.Internal.Do

universe v

variable {m : Type u → Type v} {L : Type u}
variable [Monad m] [Assertion L] [WPMonad m L EPost.Nil] [ExactWPMonad m L EPost.Nil]
variable {α β σ ρ ε : Type u}

example (x : StateT σ m α) (f : α → StateT σ m β) (post : β → σ → L) (e : EPost.Nil) :
    wp (x >>= f) post e = wp x (fun a => wp (f a) post e) e :=
  ExactWPMonad.wp_bind x f post e

example (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) (post : β → ρ → L) (e : EPost.Nil) :
    wp (x >>= f) post e = wp x (fun a => wp (f a) post e) e :=
  ExactWPMonad.wp_bind x f post e

example (x : ExceptT ε m α) (f : α → ExceptT ε m β) (post : β → L)
    (e : EPost.Cons (ε → L) EPost.Nil) :
    wp (x >>= f) post e = wp x (fun a => wp (f a) post e) e :=
  ExactWPMonad.wp_bind x f post e

example (x : OptionT m α) (f : α → OptionT m β) (post : β → L) (e : EPost.Cons L EPost.Nil) :
    wp (x >>= f) post e = wp x (fun a => wp (f a) post e) e :=
  ExactWPMonad.wp_bind x f post e

end ExactTransformers
