/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.SlotRenaming

/-! # Slot-renaming regression tests

Runs at and past the slot budget: the first labels take slots in order and read the table, later
labels take the overflow branch, and a repeated label keeps its answer in either case.
-/

public section

open OracleComp OracleSpec OracleComp.SlotRenaming

namespace SlotRenamingTest

variable {R : Type} [SampleableType R]

/-- Two hash queries. -/
def twoQueries (k l : Bool) : OracleComp (unifSpec + (Bool →ₒ R)) (R × R) := do
  let a ← (unifSpec + (Bool →ₒ R)).query (.inr k)
  let b ← (unifSpec + (Bool →ₒ R)).query (.inr l)
  return (a, b)

variable {q : ℕ}

private theorem hash_slot (g : Fin q → R) (l : Bool) (s : State Bool R q) (i : Fin q)
    (h : s.slotOf l = some i) :
    (((unifFwdAnswerImpl ⟨g⟩).mapStateTBase route) (.inr l)).run s =
      pure (g i, record s l (g i)) := by
  rw [tableHandler_apply]; simp [h]

private theorem hash_overflow (g : Fin q → R) (l : Bool) (s : State Bool R q) (r : R)
    (h : s.slotOf l = none) (ho : s.overflow l = some r) :
    (((unifFwdAnswerImpl ⟨g⟩).mapStateTBase route) (.inr l)).run s = pure (r, record s l r) := by
  rw [tableHandler_apply]; simp [h, ho]

private theorem hash_assign (g : Fin q → R) (l : Bool) (s : State Bool R q)
    (h : s.slotOf l = none) (ho : s.overflow l = none) (hn : s.next < q) :
    (((unifFwdAnswerImpl ⟨g⟩).mapStateTBase route) (.inr l)).run s =
      pure (g ⟨s.next, hn⟩, assign s l hn (g ⟨s.next, hn⟩)) := by
  rw [tableHandler_apply]; simp [h, ho, hn]

private theorem hash_spill (g : Fin q → R) (l : Bool) (s : State Bool R q)
    (h : s.slotOf l = none) (ho : s.overflow l = none) (hn : ¬ s.next < q) :
    (((unifFwdAnswerImpl ⟨g⟩).mapStateTBase route) (.inr l)).run s =
      (fun r => (r, spill s l r)) <$> ($ᵗ R : ProbComp R) := by
  rw [tableHandler_apply]; simp [h, ho, hn]

private theorem tableRun_two (k l : Bool) (g : Fin q → R) :
    tableRun (twoQueries k l) g =
      (((unifFwdAnswerImpl ⟨g⟩).mapStateTBase route) (.inr k)).run initial >>= fun x =>
        (((unifFwdAnswerImpl ⟨g⟩).mapStateTBase route) (.inr l)).run x.2 >>= fun y =>
          pure ((x.1, y.1), y.2) := by
  rw [tableRun, QueryImpl.simulateQ_mapStateTBase_run]
  simp [twoQueries]

-- One slot and two labels: the first reads the table, the second overflows.
example (g : Fin 1 → R) : tableRun (twoQueries false true) g =
    (fun r => ((g 0, r), spill (assign initial false one_pos (g 0)) true r)) <$>
      ($ᵗ R : ProbComp R) := by
  rw [tableRun_two, hash_assign g false initial rfl rfl one_pos, pure_bind,
    hash_spill g true _ rfl rfl (by simp [assign, initial])]
  simp [initial]

-- Overflow leaves the label without a slot and caches its answer.
example (g : Fin 1 → R) (r : R) :
    (spill (assign initial false one_pos (g 0)) true r).slotOf true = none ∧
      (spill (assign initial false one_pos (g 0)) true r).overflow true = some r := by
  simp [spill, assign, initial]

-- A repeated label keeps its overflow answer, with no slot at all.
example (g : Fin 0 → R) : tableRun (twoQueries true true) g =
    (fun r => ((r, r), record (spill initial true r) true r)) <$> ($ᵗ R : ProbComp R) := by
  rw [tableRun_two, hash_spill g true initial rfl rfl (by simp [initial]), bind_map_left]
  refine (bind_congr fun r => ?_).trans (map_eq_bind_pure_comp _ _ _).symm
  rw [hash_overflow g true _ r (by simp [spill, initial]) (by simp [spill])]
  simp

-- A repeated label within the budget reuses its slot and uses up only one.
example (g : Fin 2 → R) : tableRun (twoQueries true true) g =
    pure ((g 0, g 0), record (assign initial true two_pos (g 0)) true (g 0)) := by
  rw [tableRun_two, hash_assign g true initial rfl rfl two_pos, pure_bind,
    hash_slot g true _ 0 (by simp [assign, initial])]
  simp [initial]

end SlotRenamingTest
