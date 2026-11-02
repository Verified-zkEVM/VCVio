/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Traversal

/-! # Effect-preserving frame laws for computed graph cells -/

public section

open OracleSpec OracleComp

namespace OracleComp.RandomOracleTraversal

variable {Index State Key Cell Input Output Result : Type}

/-- Appending two traversal lists executes them in order with the complete intermediate state. -/
theorem evaluate_append (input : Index → State → Input) (step : Index → State → Output → State)
    (left right : List Index) (state : State) :
    evaluate input step (left ++ right) state = (do
      let middle ← evaluate input step left state
      evaluate input step right middle) := by
  induction left generalizing state with
  | nil => simp [evaluate]
  | cons node nodes ih => simp [evaluate, ih, bind_assoc]

variable [DecidableEq Key]

/-- A cell outside all writes keeps its initial value on every free-program result. -/
theorem read_outside_of_mem_support
    (input : Index → (Key → Cell) → Input) (key : Index → Key)
    (value : Index → Output → Cell) (nodes : List Index) (state : Key → Cell)
    (outside : Key) (notWritten : ∀ node ∈ nodes, key node ≠ outside)
    (final : Key → Cell)
    (reachable : final ∈ support (evaluate input
      (fun node cells answer => Function.update cells (key node) (value node answer))
      nodes state)) : final outside = state outside := by
  induction nodes generalizing state with
  | nil =>
      have same := OracleComp.eq_of_mem_support_pure state reachable
      rw [same]
  | cons node nodes ih =>
      obtain ⟨answer, _, reachable⟩ := OracleComp.mem_support_bind_peel _ _ reachable
      have outsideHead : outside ≠ key node := Ne.symm (notWritten node (by simp))
      have outsideTail : ∀ other ∈ nodes, key other ≠ outside :=
        fun other member => notWritten other (by simp [member])
      rw [ih _ outsideTail reachable]
      exact Function.update_of_ne outsideHead _ _

/-- Reading an unwritten cell in a continuation preserves the entire original traversal. -/
theorem bind_read_outside
    (input : Index → (Key → Cell) → Input) (key : Index → Key)
    (value : Index → Output → Cell) (nodes : List Index) (state : Key → Cell)
    (outside : Key) (notWritten : ∀ node ∈ nodes, key node ≠ outside)
    (continuation : (Key → Cell) → Cell → OracleComp (Input →ₒ Output) Result) :
    (do
      let final ← evaluate input
        (fun node cells answer => Function.update cells (key node) (value node answer)) nodes state
      continuation final (final outside)) =
    (do
      let final ← evaluate input
        (fun node cells answer => Function.update cells (key node) (value node answer)) nodes state
      continuation final (state outside)) := by
  apply OracleComp.bind_congr_of_forall_mem_support
  intro final reachable
  rw [read_outside_of_mem_support input key value nodes state outside notWritten final reachable]

end OracleComp.RandomOracleTraversal
