/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.EvalDist.List
public import Mathlib.Data.List.InsertIdx

/-!
# Independent list sampling at a chosen position

A chosen draw can be performed before the remaining draws without changing their joint law.
Continuations may inspect that entry and the list with its position removed directly.
-/

public section

namespace OracleComp

/-- A chosen independent list draw may be performed first, then reinserted at its original
position, without changing the joint law of the list of results. -/
theorem mapM_draw_first {C X : Type} (child : C → ProbComp X)
    (pool : List C) (i : ℕ) (hi : i < pool.length) :
    (do
      let x ← child pool[i]
      let xs ← (pool.eraseIdx i).mapM child
      pure (xs.insertIdx i x)) =ᵈ pool.mapM child := by
  induction pool generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < cs.length := by simpa using hi
          simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.mapM_cons,
            bind_assoc, pure_bind, List.insertIdx_succ_cons]
          refine (OracleComp.EvalDistEq.bind_bind_swap (child cs[i]) (child c)
            (fun x y => do let xs ← (cs.eraseIdx i).mapM child
                           pure (y :: xs.insertIdx i x))).trans ?_
          apply EvalDistEq.bind_right
          intro y
          simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def] using
            (ih i hi').map (List.cons y)

/-- A continuation of a sampled entry and the remaining table can sample the chosen entry
first, then independently sample the positions that remain. -/
theorem mapM_bind_eraseIdx {C X Y : Type} (child : C → ProbComp X)
    (pool : List C) (i : ℕ) (hi : i < pool.length) (fallback : X)
    (next : X → List X → ProbComp Y) :
    (do
      let x ← child pool[i]
      let xs ← (pool.eraseIdx i).mapM child
      next x xs) =ᵈ
    (do
      let table ← pool.mapM child
      next (table[i]?.getD fallback) (table.eraseIdx i)) := by
  have hfirst := (mapM_draw_first child pool i hi).bind_left
    (fun table => next (table[i]?.getD fallback) (table.eraseIdx i))
  simp only [bind_assoc, pure_bind] at hfirst
  refine EvalDistEq.trans ?_ hfirst
  apply EvalDistEq.bind_right
  intro x
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro xs hx
  have hlen := List.length_of_mem_support_mapM child (pool.eraseIdx i) xs hx
  rw [List.length_eraseIdx_of_lt hi] at hlen
  rw [List.getElem?_insertIdx_self]
  simp only [show i ≤ xs.length by omega, ↓reduceIte,
    Option.getD_some, List.eraseIdx_insertIdx_self]
  exact .rfl

end OracleComp
