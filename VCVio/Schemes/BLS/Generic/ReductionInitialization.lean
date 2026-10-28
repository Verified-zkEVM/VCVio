/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.ReductionPoints
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Initialization of the BLS reduction execution relation

The adversary receives two source entries per sort. Private zero handles and extra reduction
allocations stay outside its virtual tables.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace BLS.Generic

variable {F M T : Type} {G : Bool → Type}

attribute [local implicit_reducible] spec PFam

/-- The real extraction state starts with the generator and public key as separate receipts. -/
@[expose] def initialRealReductionState [Zero F] [One F]
    (g pk : (b : Bool) → G b) : RealReductionState F M G T :=
  (((fun _ => [0, 1], trackInputs (fun b => [g b, pk b])), []), [])

/-- Initial scalar metadata erases the values of the two real source bases. -/
theorem initialReductionState_metadata [Zero F] [One F]
    (g pk : (b : Bool) → G b) (pk₁ pk₂ : Handle) :
    (initialReductionState (F := F) (M := M) pk₁ pk₂).metadata =
      Pairing.eraseValues (initialRealReductionState (F := F) (M := M) (T := T) g pk).1 := by
  simp only [initialReductionState, initialRealReductionState, Pairing.eraseValues,
    Pairing.eraseSourceValues, List.map_nil]
  congr 2

/-- Valid visible handles with the prescribed source values initialize the execution relation. -/
theorem reductionRelated_initial [Zero F] [One F]
    [∀ b, AddCommMonoid (G b)] [AddCommMonoid T]
    (g pk : (b : Bool) → G b) (pk₁ pk₂ : Handle)
    (root tbl : Tbl (PFam (G false) (G true) T)) (z : PSort → Handle)
    (hp : ∀ s, root s <+: tbl s)
    (hw : WellFormed z (initialReductionState (F := F) (M := M) pk₁ pk₂).handles tbl)
    (hg₁ : lookup tbl .g₁ 0 = g false) (hg₂ : lookup tbl .g₂ 0 = g true)
    (hpk₁ : lookup tbl .g₁ pk₁ = pk false) (hpk₂ : lookup tbl .g₂ pk₂ = pk true) :
    ReductionRelated root z (initialReductionState pk₁ pk₂) tbl
      (initialRealReductionState (F := F) (M := M) g pk) := by
  refine ⟨hp, hw, initialReductionState_metadata g pk pk₁ pk₂, ?_, rfl⟩
  funext s
  cases s <;>
    simp [readBack, initialReductionState, initialRealReductionState, Pairing.table,
      trackInputs, List.mapIdx_cons, hg₁, hg₂, hpk₁, hpk₂]

/-- The common-exponent challenge contains two points in each source and no target points. -/
@[expose] def sourceChallengeTable (g x : (b : Bool) → G b) :
    Tbl (PFam (G false) (G true) T)
  | .g₁ => [g false, x false]
  | .g₂ => [g true, x true]
  | .gₜ => []

/-- The three private zero handles allocated after a two-source challenge. -/
@[expose] def sourceZeroHandles : PSort → Handle
  | .g₁ => 2
  | .g₂ => 2
  | .gₜ => 0

/-- Allocating zero handles appends one zero in each sort and leaves all source inputs intact. -/
theorem runGen_reductionZeros [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)]
    [AddCommMonoid T] [Module F T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T) (g x : (b : Bool) → G b) :
    runGen (pairingReal e) (fun _ => id) reductionZeros (sourceChallengeTable (T := T) g x) =
      pure (sourceZeroHandles, fun s => sourceChallengeTable (T := T) g x s ++ [0]) := by
  simp only [reductionZeros, runGen, run, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query, StateT.run_bind, StateT.run_pure]
  simp only [add_apply_inl, StateT.run, QueryImpl.ofLift_eq_id', QueryImpl.add_apply_inl,
    impl, push, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    sourceChallengeTable, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    append, zero_smul, List.cons_append, List.nil_append, bind_pure_comp, map_pure,
    ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne,
    PFunctor.FreeM.pure_inj, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext s
  cases s <;> simp

/-- Zero allocation initializes the good branch with the challenge points as its public key. -/
theorem reductionRelated_good [Zero F] [One F]
    [∀ b, AddCommMonoid (G b)] [AddCommMonoid T] (g x : (b : Bool) → G b) :
    ReductionRelated (sourceChallengeTable (T := T) g x) sourceZeroHandles
      (initialReductionState (F := F) (M := M) 1 1)
      (fun s => sourceChallengeTable (T := T) g x s ++ [0])
      (initialRealReductionState g x) := by
  apply reductionRelated_initial
  · intro s
    exact List.prefix_append _ _
  · intro s
    cases s <;> simp [sourceZeroHandles, initialReductionState, sourceChallengeTable, lookup]
  all_goals simp [sourceChallengeTable, lookup]

/-- Installing a sampled public key initializes the bad branch after the private zero entries. -/
theorem reductionRelated_bad [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [AddCommMonoid T]
    (g x : (b : Bool) → G b) (κ : F) :
    ReductionRelated (sourceChallengeTable (T := T) g x) sourceZeroHandles
      (initialReductionState (F := F) (M := M) 3 3)
      (fun | .g₁ => [g false, x false, 0, κ • g false]
           | .g₂ => [g true, x true, 0, κ • g true]
           | .gₜ => [0])
      (initialRealReductionState g (fun b => κ • g b)) := by
  apply reductionRelated_initial
  · intro s
    cases s <;> simp [sourceChallengeTable]
  · intro s
    cases s <;> simp [sourceZeroHandles, initialReductionState, lookup]
  all_goals simp [lookup]

end BLS.Generic
