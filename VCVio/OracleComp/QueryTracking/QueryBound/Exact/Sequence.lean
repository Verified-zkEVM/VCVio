/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound.Exact
public import ToMathlib.Control.Monad.Fold
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact query counts for finite sequencing and folds

Finite sequencing adds its per-index counts. A monadic list fold with a uniform step count
charges every executed step, including repeated inputs, at independent item and state universes.
-/

public section
open scoped BigOperators
open OracleComp.QueryBound (ExactQueryCount)

namespace OracleComp.QueryBound.ExactQueryCount

/-- Sequencing a finite family adds its branch-uniform structural query counts. -/
theorem fin_mOfFn.{i, a, r} {ι : Type i} {spec : OracleSpec.{i, a} ι} {α : Type r} {size : Nat} :
    ∀ (f : Fin size → OracleComp spec α) (count : Fin size → Nat),
      (∀ index, ExactQueryCount (f index) (count index)) →
      ExactQueryCount (Fin.mOfFn size f) (∑ index, count index) := by
  induction size with
  | zero =>
      intro f count hcount
      simpa only [Fin.mOfFn_zero, Fin.sum_univ_zero] using
        ExactQueryCount.pure (Fin.elim0 : Fin 0 → α)
  | succ size ih =>
      intro f count hcount
      rw [Fin.mOfFn_succ, Fin.sum_univ_succ]
      have htail := ih (fun index => f index.succ) (fun index => count index.succ)
        (fun index => hcount index.succ)
      have hmap (first : α) : ExactQueryCount
          (Fin.mOfFn size (fun index => f index.succ) >>= fun rest =>
            Pure.pure (Fin.cons first rest : Fin (size + 1) → α))
          (∑ index : Fin size, count index.succ) := by
        simpa only [OracleComp.ofFreeM, OracleComp.toFreeM,
          PFunctor.FreeM.map_eq_map, map_eq_bind_pure_comp, Function.comp_def] using
          ExactQueryCount.map htail
            (fun rest => (Fin.cons first rest : Fin (size + 1) → α))
      simpa only [OracleComp.ofFreeM, OracleComp.toFreeM,
        PFunctor.FreeM.bind_eq_bind] using
        ExactQueryCount.bind (hcount 0)
          (fun first => Fin.mOfFn size (fun index => f index.succ) >>= fun rest =>
            Pure.pure (Fin.cons first rest : Fin (size + 1) → α))
          (∑ index : Fin size, count index.succ) hmap

/-- A uniform step count is charged once for each item of a monadic list fold. -/
theorem foldlM.{i, a, r, t} {ι : Type i} {spec : OracleSpec.{i, a} ι}
    {Item : Type t} {State : Type r} (items : List Item)
    (f : State → Item → OracleComp spec State) (count : Nat) :
    (∀ state item, ExactQueryCount (f state item) count) → ∀ initial : State,
      ExactQueryCount (items.foldlM f initial) (items.length * count) := by
  intro hcount
  induction items with
  | nil =>
      intro initial
      simpa only [List.foldlM_nil, List.length_nil, Nat.zero_mul] using
        ExactQueryCount.pure initial
  | cons item items ih =>
      intro initial
      simpa only [List.foldlM_cons, List.length_cons, Nat.add_mul, Nat.one_mul,
        Nat.add_comm, OracleComp.ofFreeM, OracleComp.toFreeM,
        PFunctor.FreeM.bind_eq_bind] using
        ExactQueryCount.bind (hcount initial item)
          (fun state => items.foldlM f state) (items.length * count) ih


end OracleComp.QueryBound.ExactQueryCount
