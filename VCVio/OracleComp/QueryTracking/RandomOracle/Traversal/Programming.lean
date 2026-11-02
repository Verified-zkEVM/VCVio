/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal

/-!
# Dependency programming with an ordered full-answer cache

A cell update writes one declared key. If each input reads only cells that agree with a target,
and every cell outside the remaining writes already agrees, the existing traversal installs
that target and the cache written in the same list order. Neither distinct coordinates nor
distinct input keys are required. These deterministic laws assume no sampling or query budget.
-/

public section

open OracleComp OracleSpec

namespace OracleComp.RandomOracleTraversal.Programming

/-- Cells not written by the remaining list already have their target values. -/
@[expose] def AgreesOutside {Index Key Cell : Type} (writeKey : Index → Key)
    (remaining : List Index) (cells target : Key → Cell) : Prop :=
  ∀ key, (∀ node ∈ remaining, writeKey node ≠ key) → cells key = target key

/-- Each read is outside every write at its own position and in the remaining suffix. -/
@[expose] def ReadBeforeWrite {Index Key : Type} (writeKey : Index → Key)
    (reads : Index → List Key) (nodes : List Index) : Prop :=
  ∀ (position : Fin nodes.length) (child : Key), child ∈ reads (nodes[position]) →
    ∀ later ∈ nodes.drop position.val, writeKey later ≠ child

/-- Install full answers at fixed inputs in the exact left-to-right list order. -/
@[expose] def cacheFrom {Index Input Output : Type} [DecidableEq Input]
    (fixedInput : Index → Input) (outputs : Index → Output) (nodes : List Index)
    (cache : QueryCache (Input →ₒ Output)) : QueryCache (Input →ₒ Output) :=
  nodes.foldl (fun saved node => saved.cacheQuery (fixedInput node) (outputs node)) cache

/-- A target-consistent write shrinks the region that may still disagree. -/
theorem AgreesOutside.assign {Index Key Cell Output : Type} [DecidableEq Key]
    (writeKey : Index → Key) (value : Index → Output → Cell)
    (remaining : List Index) (parent : Index) (cells target : Key → Cell) (output : Output)
    (agrees : AgreesOutside writeKey (parent :: remaining) cells target)
    (same : value parent output = target (writeKey parent)) :
    AgreesOutside writeKey remaining
      (Function.update cells (writeKey parent) (value parent output)) target := by
  intro key outside
  by_cases equal : key = writeKey parent
  · subst key
    simpa only [Function.update_self] using same
  · rw [Function.update_of_ne equal]
    apply agrees key
    intro node member
    rcases List.mem_cons.mp member with rfl | member
    · exact Ne.symm equal
    · exact outside node member

/-- Child agreement determines the current input before its write. -/
theorem input_eq_target {Index Key Cell Input : Type}
    (writeKey : Index → Key) (reads : Index → List Key)
    (input : Index → (Key → Cell) → Input)
    (depends : ∀ parent left right,
      (∀ child ∈ reads parent, left child = right child) → input parent left = input parent right)
    (parent : Index) (remaining : List Index) (cells target : Key → Cell)
    (order : ∀ child ∈ reads parent,
      ∀ later ∈ parent :: remaining, writeKey later ≠ child)
    (agrees : AgreesOutside writeKey (parent :: remaining) cells target) :
    input parent cells = input parent target := by
  apply depends parent cells target
  intro child member
  exact agrees child (order child member)

/-- The existing traversal installs the target cells and the same ordered full-answer cache. -/
theorem program_eq_cacheFrom {Index Key Cell Input Output : Type}
    [DecidableEq Key] [DecidableEq Input]
    (writeKey : Index → Key) (reads : Index → List Key)
    (input : Index → (Key → Cell) → Input) (value : Index → Output → Cell)
    (depends : ∀ parent left right,
      (∀ child ∈ reads parent, left child = right child) → input parent left = input parent right)
    (outputs : Index → Output) (nodes : List Index) :
    ∀ (cells target : Key → Cell),
      ReadBeforeWrite writeKey reads nodes → AgreesOutside writeKey nodes cells target →
      (∀ parent ∈ nodes, value parent (outputs parent) = target (writeKey parent)) →
      ∀ cache : QueryCache (Input →ₒ Output),
        OracleComp.RandomOracleTraversal.program input
          (fun parent current answer =>
            Function.update current (writeKey parent) (value parent answer))
          outputs nodes cells cache =
          (target, cacheFrom (fun parent => input parent target) outputs nodes cache) := by
  induction nodes with
  | nil =>
      intro cells target order agrees consistent cache
      have same : cells = target := by
        funext key
        exact agrees key (by simp)
      simp only [program, cacheFrom, List.foldl_nil, same]
  | cons parent remaining ih =>
      intro cells target order agrees consistent cache
      have first : ∀ child ∈ reads parent,
          ∀ later ∈ parent :: remaining, writeKey later ≠ child := by
        intro child member later occurs
        exact order ⟨0, by simp⟩ child (by simpa using member) later (by simpa using occurs)
      have inputSame : input parent cells = input parent target :=
        input_eq_target writeKey reads input depends parent remaining cells target first agrees
      have tailOrder : ReadBeforeWrite writeKey reads remaining := by
        intro position child member later occurs
        let next : Fin (parent :: remaining).length :=
          ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩
        exact order next child (by simpa [next] using member) later
          (by simpa [next] using occurs)
      have tailAgree : AgreesOutside writeKey remaining
          (Function.update cells (writeKey parent) (value parent (outputs parent))) target :=
        AgreesOutside.assign writeKey value remaining parent cells target (outputs parent) agrees
          (consistent parent (by simp))
      rw [program, inputSame]
      simpa only [cacheFrom, List.foldl_cons] using
        ih _ target tailOrder tailAgree
          (fun node member => consistent node (List.mem_cons_of_mem parent member))
          (cache.cacheQuery (input parent target) (outputs parent))

end OracleComp.RandomOracleTraversal.Programming
