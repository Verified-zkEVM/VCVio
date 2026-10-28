/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Oracle
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Transport of group-model runs along morphisms
-/

public section

open OracleComp OracleSpec

namespace GroupModel

section Projection

variable {F : Type} [CommSemiring F] {S : Type} [DecidableEq S] {σ : Sig S} {V W U : S → Type}
  [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
  [∀ s, AddCommMonoid (W s)] [∀ s, Module F (W s)]

/-- Model morphisms transport runs when the game handlers transport the shared table. -/
theorem run_map [∀ s, DecidableEq (U s)] {M : Model F σ V} {N : Model F σ W} (φ : M.Hom N)
    (obs : (s : S) → W s → U s)
    {m : Type → Type} [Monad m] [LawfulMonad m] {ι : Type} {Γ : OracleSpec ι}
    (game₁ : QueryImpl Γ (StateT (Tbl V) m))
    (game₂ : QueryImpl Γ (StateT (Tbl W) m))
    (hgame : ∀ t tbl, Prod.map id (mapTbl fun s => φ.toFun s) <$> (game₁ t).run tbl =
      (game₂ t).run (mapTbl (fun s => φ.toFun s) tbl))
    {α : Type} (oa : OracleComp (spec F σ + Γ) α) (tbl : Tbl V) :
    Prod.map id (mapTbl fun s => φ.toFun s) <$> run M (fun s => obs s ∘ φ.toFun s) game₁ oa tbl =
      run N obs game₂ oa (mapTbl (fun s => φ.toFun s) tbl) := by
  unfold run
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (mapTbl fun s => φ.toFun s) ?_ oa tbl
  intro t s
  rcases t with (⟨s', a, b⟩ | ⟨s', c, a⟩ | ⟨s', a, b⟩ | ⟨o, a⟩ | ⟨o, a, b⟩) | n
  · simp only [QueryImpl.add_apply_inl, impl, push, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run]
    erw [map_pure]
    simp [Prod.map, mapTbl_append, lookup_mapTbl, mapTbl]
    rfl
  · simp only [QueryImpl.add_apply_inl, impl, push, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run]
    erw [map_pure]
    simp [Prod.map, mapTbl_append, lookup_mapTbl, mapTbl]
    rfl
  · simp only [QueryImpl.add_apply_inl, impl, Function.comp_apply, StateT.run_bind,
      StateT.run_get, pure_bind, lookup_mapTbl]
    erw [StateT.run_pure, StateT.run_pure]
    simp
    rfl
  · simp only [QueryImpl.add_apply_inl, impl, push, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run]
    erw [map_pure]
    simp [Prod.map, mapTbl_append, lookup_mapTbl, φ.map_lin, mapTbl]
    rfl
  · simp only [QueryImpl.add_apply_inl, impl, push, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, StateT.run]
    erw [map_pure]
    simp [Prod.map, mapTbl_append, lookup_mapTbl, φ.map_bil, mapTbl]
    rfl
  · exact hgame n s

/-- Projection of a generic run along a model morphism. -/
theorem runGen_map [∀ s, DecidableEq (U s)] {M : Model F σ V} {N : Model F σ W}
    (φ : M.Hom N) (obs : (s : S) → W s → U s) {α : Type}
    (oa : OracleComp (genSpec F σ) α) (tbl : Tbl V) :
    Prod.map id (mapTbl fun s => φ.toFun s) <$> runGen M (fun s => obs s ∘ φ.toFun s) oa tbl =
      runGen N obs oa (mapTbl (fun s => φ.toFun s) tbl) := by
  apply run_map
  intro t tbl
  simp

/-- The handler depends on the observation only through the equalities it induces. Two
observations with the same equalities give the same handler, hence the same run. -/
theorem impl_congr {U' : S → Type} [∀ s, DecidableEq (U s)] [∀ s, DecidableEq (U' s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s) (obs' : (s : S) → V s → U' s)
    (h : ∀ s x y, obs s x = obs s y ↔ obs' s x = obs' s y) (m : Type → Type) [Monad m] :
    impl M obs m = impl M obs' m := by
  funext t
  cases t with
  | eq s a b => simp [impl, h]
  | _ => rfl

/-- The kernel lemma. If two tables are the images of one table under morphisms that identify
the same pairs of elements, the two generic runs have the same output distribution.
Uniform sampling does not touch the table; this statement concerns `runGen`. -/
theorem run_fst_eq_of_kernel_eq {K : S → Type} [∀ s, AddCommMonoid (K s)] [∀ s, Module F (K s)]
    [∀ s, DecidableEq (V s)] [∀ s, DecidableEq (W s)]
    {L : Model F σ K} {M : Model F σ V} {N : Model F σ W} (φ : L.Hom M) (ψ : L.Hom N)
    (h : ∀ s x y, φ.toFun s x = φ.toFun s y ↔ ψ.toFun s x = ψ.toFun s y)
    {α : Type} (oa : OracleComp (genSpec F σ) α) (tbl : Tbl K) :
    Prod.fst <$> runGen M (fun _ => id) oa (mapTbl (fun s => φ.toFun s) tbl) =
      Prod.fst <$> runGen N (fun _ => id) oa (mapTbl (fun s => ψ.toFun s) tbl) := by
  rw [← runGen_map φ (fun _ => id), ← runGen_map ψ (fun _ => id)]
  simp only [Functor.map_map]
  unfold runGen run
  rw [impl_congr L (fun s => id ∘ φ.toFun s) (fun s => id ∘ ψ.toFun s) (by simpa using h)]
  rfl

end Projection

end GroupModel
