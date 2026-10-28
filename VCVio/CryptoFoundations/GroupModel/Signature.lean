/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.OracleComp
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Prod

/-!
# Sorted group signatures and models
-/

public section

open OracleComp OracleSpec

namespace GroupModel

/-- A handle is a position in the table of its sort. -/
abbrev Handle := ℕ

/-- A signature over sorts `S`: the names of the linear and bilinear structure maps and their
sorts. -/
structure Sig (S : Type) where
  Lin : Type
  lsrc : Lin → S
  ltgt : Lin → S
  Bil : Type
  src₁ : Bil → S
  src₂ : Bil → S
  tgt : Bil → S

/-- Queries: the module operations and equality in each sort, and each structure map. -/
inductive Query (F : Type) {S : Type} (σ : Sig S) : Type
  | add (s : S) (a b : Handle)
  | smul (s : S) (c : F) (a : Handle)
  | eq (s : S) (a b : Handle)
  | lin (o : σ.Lin) (a : Handle)
  | bil (o : σ.Bil) (a b : Handle)

/-- Answer types for the sorted group queries. -/
@[expose] def spec (F : Type) {S : Type} (σ : Sig S) : OracleSpec (Query F σ)
  | .add _ _ _ => Handle
  | .smul _ _ _ => Handle
  | .eq _ _ _ => Bool
  | .lin _ _ => Handle
  | .bil _ _ _ => Handle

/-- A model of a signature: a module per sort and a map per structure map. -/
structure Model (F : Type) [CommSemiring F] {S : Type} (σ : Sig S) (V : S → Type)
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] where
  lin : (o : σ.Lin) → V (σ.lsrc o) →ₗ[F] V (σ.ltgt o)
  bil : (o : σ.Bil) → V (σ.src₁ o) →ₗ[F] V (σ.src₂ o) →ₗ[F] V (σ.tgt o)

/-- A morphism of models: a linear map per sort that commutes with the structure maps. -/
structure Model.Hom {F : Type} [CommSemiring F] {S : Type} {σ : Sig S} {V W : S → Type}
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, AddCommMonoid (W s)] [∀ s, Module F (W s)]
    (M : Model F σ V) (N : Model F σ W) where
  toFun : (s : S) → V s →ₗ[F] W s
  map_lin : ∀ o x, toFun (σ.ltgt o) (M.lin o x) = N.lin o (toFun _ x)
  map_bil : ∀ o x y, toFun (σ.tgt o) (M.bil o x y) = N.bil o (toFun _ x) (toFun _ y)

section Models

variable {F : Type} [CommSemiring F] {S : Type} {σ : Sig S} {V W X : S → Type}
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, AddCommMonoid (W s)] [∀ s, Module F (W s)]
    [∀ s, AddCommMonoid (X s)] [∀ s, Module F (X s)]

/-- Identity morphism of a model. -/
@[expose] def Model.Hom.id (M : Model F σ V) : M.Hom M where
  toFun _ := LinearMap.id
  map_lin _ _ := rfl
  map_bil _ _ _ := rfl

/-- Composition of model morphisms. -/
@[expose] def Model.Hom.comp {L : Model F σ V} {M : Model F σ W} {N : Model F σ X}
    (ψ : M.Hom N) (φ : L.Hom M) : L.Hom N where
  toFun s := (ψ.toFun s).comp (φ.toFun s)
  map_lin o x := by simp [φ.map_lin, ψ.map_lin]
  map_bil o x y := by simp [φ.map_bil, ψ.map_bil]

/-- Componentwise product of two models. -/
@[expose] def Model.prod (M : Model F σ V) (N : Model F σ W) :
    Model F σ (fun s => V s × W s) where
  lin o := (M.lin o).prodMap (N.lin o)
  bil o :=
    { toFun := fun x => ((M.bil o x.1).comp (LinearMap.fst F _ _)).prod
        ((N.bil o x.2).comp (LinearMap.snd F _ _))
      map_add' := by intros; ext <;> simp
      map_smul' := by intros; ext <;> simp }

/-- First projection from a product model. -/
@[expose] def Model.Hom.fst (M : Model F σ V) (N : Model F σ W) : (M.prod N).Hom M where
  toFun _ := LinearMap.fst F _ _
  map_lin _ _ := rfl
  map_bil _ _ _ := rfl

/-- Second projection from a product model. -/
@[expose] def Model.Hom.snd (M : Model F σ V) (N : Model F σ W) : (M.prod N).Hom N where
  toFun _ := LinearMap.snd F _ _
  map_lin _ _ := rfl
  map_bil _ _ _ := rfl

/-- The identity morphism acts as the identity at each sort. -/
@[simp] theorem Model.Hom.id_apply (M : Model F σ V) (s : S) (x : V s) :
    (Model.Hom.id M).toFun s x = x := rfl

/-- Composition acts by composing the component maps. -/
@[simp] theorem Model.Hom.comp_apply {L : Model F σ V} {M : Model F σ W}
    {N : Model F σ X} (ψ : M.Hom N) (φ : L.Hom M) (s : S) (x : V s) :
    (ψ.comp φ).toFun s x = ψ.toFun s (φ.toFun s x) := rfl

/-- The first projection selects the first component at each sort. -/
@[simp] theorem Model.Hom.fst_apply (M : Model F σ V) (N : Model F σ W)
    (s : S) (x : V s × W s) : (Model.Hom.fst M N).toFun s x = x.1 := rfl

/-- The second projection selects the second component at each sort. -/
@[simp] theorem Model.Hom.snd_apply (M : Model F σ V) (N : Model F σ W)
    (s : S) (x : V s × W s) : (Model.Hom.snd M N).toFun s x = x.2 := rfl

/-- Linear structure maps act componentwise in a product model. -/
@[simp] theorem Model.prod_lin_apply (M : Model F σ V) (N : Model F σ W)
    (o : σ.Lin) (x : V (σ.lsrc o) × W (σ.lsrc o)) :
    (M.prod N).lin o x = (M.lin o x.1, N.lin o x.2) := rfl

/-- Bilinear structure maps act componentwise in a product model. -/
@[simp] theorem Model.prod_bil_apply (M : Model F σ V) (N : Model F σ W)
    (o : σ.Bil) (x : V (σ.src₁ o) × W (σ.src₁ o))
    (y : V (σ.src₂ o) × W (σ.src₂ o)) :
    (M.prod N).bil o x y = (M.bil o x.1 y.1, N.bil o x.2 y.2) := rfl

end Models

/-- One group: one sort, no structure map. -/
@[expose] def groupSig : Sig Unit :=
  ⟨Empty, Empty.elim, Empty.elim, Empty, Empty.elim, Empty.elim, Empty.elim⟩

/-- The sorts of a pairing group. -/
inductive PSort
  | g₁ | g₂ | gₜ
  deriving DecidableEq

/-- Asymmetric pairing without a map between the source groups (Type 3). -/
@[expose] def pairingSig : Sig PSort :=
  ⟨Empty, Empty.elim, Empty.elim, Unit, fun _ => .g₁, fun _ => .g₂, fun _ => .gₜ⟩

/-- Asymmetric pairing with a map from the second source group to the first (Type 2). -/
@[expose] def pairingIsoSig : Sig PSort :=
  ⟨Unit, fun _ => .g₂, fun _ => .g₁, Unit, fun _ => .g₁, fun _ => .g₂, fun _ => .gₜ⟩

/-- Symmetric pairing (Type 1): one source sort paired with itself. -/
@[expose] def symmPairingSig : Sig Bool :=
  ⟨Empty, Empty.elim, Empty.elim, Unit, fun _ => false, fun _ => false, fun _ => true⟩

/-- Independent sorts with no structure maps. -/
@[expose] def discreteSig (S : Type) : Sig S :=
  ⟨Empty, Empty.elim, Empty.elim, Empty, Empty.elim, Empty.elim, Empty.elim⟩

end GroupModel
