/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import ToMathlib.Control.WriterT
public import PolyFun.Control.Monad.Hom.Writer
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Monad morphisms of accumulated writer outputs

A monoid homomorphism maps accumulated outputs while retaining the original base computation
and its returned value. Additive costs use the same transformation through Multiplicative.
-/

public section

universe u v w

namespace AddWriterT

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
variable {C D α : Type u} [AddMonoid C] [AddMonoid D]

/-- Map additive costs without requiring commutative addition. -/
@[expose] def mapCostHom (f : C →+ D) : AddWriterT C m →ᵐ AddWriterT D m :=
  WriterT.mapOutputHom f.toMultiplicative

/-- The additive output is exactly the homomorphic image of the original accumulated cost. -/
@[simp] theorem runAdd_mapCostHom (f : C →+ D) (body : AddWriterT C m α) :
    (mapCostHom f body).runAdd = Prod.map id f <$> body.runAdd := by
  simp only [mapCostHom, runAdd, WriterT.run_mapOutputHom, Functor.map_map]
  rfl

end AddWriterT


/-- A base monad morphism leaves the append writer's returned value and log unchanged. -/
@[expose] def WriterT.mapBaseAppendHom
    {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
    [LawfulMonad m] [LawfulMonad n] {ω : Type u} [EmptyCollection ω] [Append ω]
    (morphism : m →ᵐ n) : WriterT ω m →ᵐ WriterT ω n where
  toFun {_α} body := WriterT.mk (morphism body.run)
  toFun_pure' value := by
    apply WriterT.ext
    simp only [WriterT.run_mk, WriterT.run_pure', MonadHom.mmap_pure]
  toFun_bind' body next := by
    apply WriterT.ext
    simp only [WriterT.run_bind', WriterT.run_mk, MonadHom.mmap_bind]
    exact bind_congr fun output => by simp only [MonadHom.mmap_map]

/-- The append-writer transformation acts on exactly the underlying base computation. -/
@[simp] theorem WriterT.run_mapBaseAppendHom
    {m : Type u → Type v} {n : Type u → Type w} [Monad m] [Monad n]
    [LawfulMonad m] [LawfulMonad n] {ω α : Type u} [EmptyCollection ω] [Append ω]
    (morphism : m →ᵐ n) (body : WriterT ω m α) :
    (WriterT.mapBaseAppendHom morphism body).run = morphism body.run := rfl
