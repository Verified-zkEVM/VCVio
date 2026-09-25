/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import VCVioComplexity.Backend.TuringMachine

/-!
# Output-size bounds from exact complexitylib runs

An output word of length `m` requires at least `m` transitions in complexitylib's concrete
Turing-machine model. The proof uses only the compiling base machine API: one transition changes
only the output cell under its head, and that head advances by at most one cell per transition.

The resulting bounds connect the actual `TM.reachesIn` witness stored in `ExactRun` to raw and
represented output sizes. They do not infer output growth from an unrelated semantic evaluator or
from a separately asserted cost meter.
-/

@[expose] public section

namespace VCVioComplexity.Backend.TuringMachine

open _root_.Complexity

variable {workTapes : ℕ}

/-- The output head advances by at most one cell in a single machine transition. -/
private theorem output_head_step_le {machine : TM workTapes}
    {current next : Cfg workTapes machine.Q}
    (step : machine.step current = some next) :
    next.output.head ≤ current.output.head + 1 := by
  simp only [TM.step] at step
  split at step
  · simp at step
  · simp only [Option.some.injEq] at step
    rw [← step]
    exact Tape.head_writeAndMove_le _ _ _

/-- One machine transition leaves every output cell other than the current head unchanged. -/
private theorem output_cells_eq_of_ne_head {machine : TM workTapes}
    {current next : Cfg workTapes machine.Q} (step : machine.step current = some next)
    {index : ℕ} (hne : index ≠ current.output.head) :
    next.output.cells index = current.output.cells index := by
  simp only [TM.step] at step
  split at step
  · simp at step
  · simp only [Option.some.injEq] at step
    rw [← step]
    simp only [Tape.move_cells, Tape.write]
    split
    · rfl
    · change Function.update current.output.cells current.output.head _ index =
        current.output.cells index
      rw [Function.update_of_ne hne]

/-- An output cell beyond the initial head position plus the run length is unchanged. -/
private theorem output_cells_far_of_reachesIn {machine : TM workTapes} :
    ∀ {steps : ℕ} {initial final : Cfg workTapes machine.Q},
      machine.reachesIn steps initial final →
        ∀ index, initial.output.head + steps < index →
          final.output.cells index = initial.output.cells index := by
  intro steps
  induction steps with
  | zero =>
      intro initial final reaches index hindex
      cases reaches
      rfl
  | succ steps ih =>
      intro initial final reaches index hindex
      cases reaches with
      | step firstStep rest =>
          next middle =>
            have hhead : middle.output.head ≤ initial.output.head + 1 :=
              output_head_step_le firstStep
            have hcell : middle.output.cells index = initial.output.cells index :=
              output_cells_eq_of_ne_head firstStep (by omega)
            rw [ih rest index (by omega), hcell]

/-- A concrete run from an initialized machine needs at least one transition per output bit. -/
private theorem output_length_le_of_reachesIn {machine : TM workTapes} {input output : Word}
    {final : Cfg workTapes machine.Q} {steps : ℕ}
    (reaches : machine.reachesIn steps (machine.initCfg input) final)
    (hasOutput : final.output.HasOutput output) : output.length ≤ steps := by
  by_contra hle
  have hsteps : steps < output.length := Nat.lt_of_not_ge hle
  have hnonempty : 0 < output.length := lt_of_le_of_lt (Nat.zero_le steps) hsteps
  let index := output.length - 1
  have hindex : index < output.length := by
    dsimp only [index]
    omega
  have hnext : index + 1 = output.length := by omega
  have hbit := hasOutput.1 index hindex
  have hfar := output_cells_far_of_reachesIn reaches output.length (by simp; omega)
  have hblank : final.output.cells output.length = Γ.blank := by
    rw [hfar]
    simp [Tape.init, hnonempty.ne']
  rw [hnext, hblank] at hbit
  exact Γ.ofBool_ne_blank _ hbit.symm

/-- A complexitylib time theorem bounds the length of the word computed on each input. -/
theorem output_length_le_of_computesInTime {machine : TM workTapes}
    {wordFunction : Word → Word} {bound : ℕ → ℕ}
    (computes : machine.ComputesInTime wordFunction bound) (word : Word) :
    (wordFunction word).length ≤ bound word.length := by
  obtain ⟨final, steps, steps_le, reaches, _halted, hasOutput⟩ := computes word
  exact (output_length_le_of_reachesIn reaches hasOutput).trans steps_le

namespace ExactRun

variable {machine : TM workTapes} {input output : Word}

/-- The output length of an exact run is at most its actual transition count. -/
theorem output_length_le_steps (run : ExactRun machine input output) :
    output.length ≤ run.steps :=
  output_length_le_of_reachesIn run.reaches run.output_correct

end ExactRun

namespace Code

variable {A B : Type} {input : Representation A} {output : Representation B}
  {function : A → B}

/-- Raw output length is bounded by the exact transition count selected for the same word. -/
theorem wordFunction_length_le_wordCost (code : Code input output function) (word : Word) :
    (code.wordFunction word).length ≤ code.wordCost word :=
  (code.run word).output_length_le_steps

/-- Encoded semantic output size is bounded by the exact transition count on that input. -/
theorem encodedSize_output_le_valueCost (code : Code input output function) (value : A) :
    encodedSize output (function value) ≤ code.valueCost value := by
  simpa [encodedSize, valueCost, code.encode_eq value] using
    code.wordFunction_length_le_wordCost (input.encode value)

end Code

end VCVioComplexity.Backend.TuringMachine
