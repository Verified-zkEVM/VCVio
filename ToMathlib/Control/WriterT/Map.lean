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

universe u v

namespace WriterT

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
variable {ω τ α : Type u} [Monoid ω] [Monoid τ]

/-- Change the output monoid while preserving the complete base computation. -/
@[expose] def mapOutputHom (f : ω →* τ) : WriterT ω m →ᵐ WriterT τ m where
  toFun {_α} body := WriterT.mk (Prod.map id f <$> body.run)
  toFun_pure' value := by
    apply WriterT.ext
    simp
  toFun_bind' body next := by
    apply WriterT.ext
    simp only [WriterT.run_bind, WriterT.run_mk, map_bind, bind_map_left, Functor.map_map]
    apply bind_congr
    intro result
    simp

/-- The output transformation changes no returned value or base-monad effect. -/
@[simp] theorem run_mapOutputHom (f : ω →* τ) (body : WriterT ω m α) :
    (mapOutputHom f body).run = Prod.map id f <$> body.run := rfl

end WriterT

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
