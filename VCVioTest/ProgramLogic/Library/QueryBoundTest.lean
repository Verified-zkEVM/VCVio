/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.QueryBoundBudget
public meta import VCVio.ProgramLogic.Tactics

/-!
# Query bounds: usage tests

Recursive and traversal-shaped programs, bounded by the structural rules or through the budget
reading and `vcgen`.
-/

@[expose] public section

open OracleSpec OracleComp

set_option experimental.vcgen true

namespace VCVioTest.ProgramLogic.Library.QueryBound

/-- Two queries per level, then recurse. -/
def walk : ℕ → OracleComp coinSpec Bool
  | 0 => pure true
  | n + 1 => do
    let a ← coinSpec.query ()
    let b ← coinSpec.query ()
    let r ← walk n
    pure (a && b && r)

/-- A binary tree of queries: two recursive calls and one query per level. -/
def tree : ℕ → OracleComp coinSpec Bool
  | 0 => coinSpec.query ()
  | n + 1 => do
    let l ← tree n
    let r ← tree n
    let b ← coinSpec.query ()
    pure (if b then l else r)

section budget

open scoped OracleComp.Budget
open OracleComp.Budget

/-- The linear recursion, through the budget reading: `vcgen` walks the two queries and enters
the recursive call through its bound. -/
theorem walk_bound (n : ℕ) : IsTotalQueryBound (walk n) (2 * n) := by
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    rw [isTotalQueryBound_iff_triple]
    vcgen [walk, Spec.ofBound ih]
    all_goals omega

/-- The tree recursion, through the budget reading. -/
example (n : ℕ) : IsTotalQueryBound (tree n) (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simp [tree]
  | succ n ih =>
    rw [isTotalQueryBound_iff_triple, show 2 ^ (n + 1 + 1) - 1 = 2 * (2 ^ (n + 1) - 1) + 1 by
      rw [pow_succ]; have := Nat.one_le_two_pow (n := n + 1); omega]
    generalize 2 ^ (n + 1) - 1 = B at ih ⊢
    vcgen [tree, Spec.ofBound ih]
    all_goals omega

end budget

/-- The tree recursion, by the structural bind rule. -/
example (n : ℕ) : IsTotalQueryBound (tree n) (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simp [tree]
  | succ n ih =>
    refine isTotalQueryBound_bind_le ih (fun _ _ => isTotalQueryBound_bind_le ih
      (fun _ _ => isTotalQueryBound_bind_le (n₁ := 1) (n₂ := 0) (by simp) (by simp) le_rfl)
      le_rfl) ?_
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := n + 1)
    omega

/-- A `List.mapM` of queries. -/
example (xs : List ℕ) :
    IsTotalQueryBound (xs.mapM fun _ => (coinSpec.query () : OracleComp coinSpec Bool))
      xs.length := by
  simpa using isTotalQueryBound_list_mapM xs (n := 1) fun _ _ => by simp

/-- A `List.foldlM` that queries once per element. -/
example (xs : List ℕ) :
    IsTotalQueryBound (xs.foldlM (fun acc _ => do
      let b ← (coinSpec.query () : OracleComp coinSpec Bool)
      pure (acc && b)) true) xs.length := by
  simpa using isTotalQueryBound_list_foldlM xs (n := 1) (fun _ _ _ => by simp) true

/-- `replicate` and a lift into a larger specification. -/
example (k n : ℕ) :
    IsTotalQueryBound (liftComp ((walk n).replicate k) (coinSpec + unifSpec)) (k * (2 * n)) :=
  isTotalQueryBound_liftComp (isTotalQueryBound_replicate (walk_bound n) k)

/-- A handler making two queries per source query. -/
def doubleCoin : QueryImpl coinSpec (StateT ℕ (OracleComp coinSpec)) := fun _ =>
  StateT.mk fun n => do
    let a ← coinSpec.query ()
    let b ← coinSpec.query ()
    pure (a ^^ b, n + 1)

/-- A simulation through a handler with a per-query bound. -/
example {α : Type} (oa : OracleComp coinSpec α) (n : ℕ) (hn : IsTotalQueryBound oa n) (s : ℕ) :
    IsTotalQueryBound ((simulateQ doubleCoin oa).run' s) (n * 2) := by
  apply hn.simulateQ_run'_of_step_le
  intro _ s
  rw [doubleCoin, StateT.run_mk, OracleComp.Budget.isTotalQueryBound_iff_triple]
  -- A bare `vcgen` is routed to VCVio's `ℝ≥0∞` pipeline here; naming a rule or asking for
  -- `errorOnMissingSpec` reaches core's.
  open scoped OracleComp.Budget in vcgen (errorOnMissingSpec := true)
  all_goals omega

/-- A predicate-targeted bound: only the left oracle is charged. -/
example (xs : List ℕ) :
    IsQueryBoundP (do
      let a ← ((coinSpec + coinSpec).query (Sum.inl ()) : OracleComp (coinSpec + coinSpec) Bool)
      let bs ← xs.mapM fun _ => ((coinSpec + coinSpec).query (Sum.inr ()) :
        OracleComp (coinSpec + coinSpec) Bool)
      pure (a :: bs)) (·.isLeft) 1 :=
  isQueryBoundP_bind_le (n₁ := 1) (by simp) (fun _ _ => isQueryBoundP_bind_le (n₂ := 0)
    (by simpa using isQueryBoundP_list_mapM xs (n := 0) fun _ _ => by simp) (by simp) le_rfl)
    le_rfl

end VCVioTest.ProgramLogic.Library.QueryBound
