/-
Copyright (c) 2026 Samuel Schlesinger, Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Devon Tuma
-/

module

public import VCVioComplexity.Backend.Polynomial
public import Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Exact linear copying and sum tagging

One finite-control transducer copies an arbitrary binary input, optionally prefixing a tag.
Its transition count is exactly the input length plus two, or plus three when tagging.
The proof uses the binary-prefix invariant of complexitylib's input-to-output copy proof
(`Subroutines/Internal/CopyOutput.lean`), specialized to zero work tapes and extended with an
explicit tag phase. It imports only the tape vocabulary and the basic machine model.
-/

public section

namespace VCVioComplexity.Backend.TuringMachine

open _root_.Complexity PFunctor

namespace LinearCopy

/-- Control distinguishes marker handling, optional tagging, copying, and termination. -/
inductive Control
  | start | tag | copying | done
  deriving DecidableEq

instance : Fintype Control where
  elems := {.start, .tag, .copying, .done}
  complete state := by cases state <;> simp

/-- Convert a read symbol to a writable symbol; the protected marker is never copied. -/
@[expose] def writeSymbol : Γ → Γw
  | .zero => .zero
  | .one => .one
  | _ => .blank

/-- A uniform copier, optionally adding one sum tag before the input. -/
@[expose] def machine (tag : Option Bool) : TM 0 where
  Q := Control
  qstart := .start
  qhalt := .done
  δ state input _ _ :=
    (match state with
      | .start => if tag.isSome then .tag else .copying
      | .tag => .copying
      | .copying => if input = .blank then .done else .copying
      | .done => .done,
    fun i => Fin.elim0 i,
    match state with
      | .tag => Γw.ofBool (tag.getD false)
      | .copying => writeSymbol input
      | _ => .blank,
    if state = .tag then Primitive.safeDirection input else .right,
    fun i => Fin.elim0 i,
    .right)
  δ_right_of_start := by
    intro state input work output
    refine ⟨?_, fun i => Fin.elim0 i, fun _ => rfl⟩
    intro h
    simp [h, Primitive.safeDirection]

private theorem emptyWork (left right : Fin 0 → Tape) : left = right := by
  funext i
  exact Fin.elim0 i

/-- Copying a remaining suffix takes one transition per bit and one terminating blank step. -/
private theorem loop (tag : Option Bool) (x initial : Word) :
    ∀ rem k (c : Cfg 0 (machine tag).Q),
      rem = x.length - k → c.state = .copying →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = k + 1 →
      c.output.HasBinaryPrefix (initial ++ x.take k) → k ≤ x.length →
      ∃ final, (machine tag).reachesIn (rem + 1) c final ∧
        (machine tag).halted final ∧ final.output.HasOutput (initial ++ x) := by
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hstate hcells hhead hprefix hk
      have heq : k = x.length := by omega
      subst k
      have hread : c.input.read = .blank := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge x x.length le_rfl]
      have hp : c.output.HasBinaryPrefix (initial ++ x) := by simpa using hprefix
      let final : Cfg 0 (machine tag).Q :=
        ⟨.done, c.input.move .right, fun i => Fin.elim0 i,
          c.output.writeAndMove .blank .right⟩
      refine ⟨final, .step ?_ .zero, rfl, ?_⟩
      · simpa [TM.step, machine, hstate, hread, final, writeSymbol] using emptyWork _ _
      · constructor
        · intro i hi
          have hne : i + 1 ≠ c.output.head := by rw [hp.1]; omega
          change (c.output.write .blank).cells (i + 1) = _
          rw [Tape.write, if_neg (show c.output.head ≠ 0 by rw [hp.1]; omega)]
          simp only
          rw [Function.update_of_ne hne]
          exact hp.2.1 i hi
        · simp [final, Tape.writeAndMove, Tape.write, Tape.move, hp.1]
  | succ rem ih =>
      intro k c hrem hstate hcells hhead hp hk
      have hklt : k < x.length := by omega
      have hread : c.input.read = Γ.ofBool (x[k]'hklt) := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt x k hklt]
      let next : Cfg 0 (machine tag).Q :=
        ⟨.copying, c.input.move .right, fun i => Fin.elim0 i,
          c.output.writeAndMove (Γ.ofBool (x[k]'hklt)) .right⟩
      have hstep : (machine tag).step c = some next := by
        cases hbit : x[k]'hklt <;>
          simpa [TM.step, machine, hstate, hread, hbit, next, Γ.ofBool, writeSymbol]
            using emptyWork _ _
      have hpnext : next.output.HasBinaryPrefix (initial ++ x.take (k + 1)) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit (x[k]'hklt) hp
        simpa [next, List.take_concat_get' x k hklt, List.append_assoc] using hwrite
      obtain ⟨final, hrun, hhalt, hout⟩ := ih (k + 1) next (by omega) rfl
        (by simpa [next, Tape.move] using hcells)
        (by simp [next, Tape.move, hhead]) hpnext (by omega)
      exact ⟨final, .step hstep hrun, hhalt, hout⟩

/-- Exact total run, including the marker and optional tag phases. -/
theorem reaches (tag : Option Bool) (word : Word) :
    ∃ final, (machine tag).reachesIn (word.length + 2 + if tag.isSome then 1 else 0)
      ((machine tag).initCfg word) final ∧ (machine tag).halted final ∧
      final.output.HasOutput (tag.toList ++ word) := by
  let first : Cfg 0 (machine tag).Q :=
    ⟨if tag.isSome then .tag else .copying,
      (Tape.init (word.map Γ.ofBool)).move .right,
      fun i => Fin.elim0 i, (Tape.init []).move .right⟩
  have hfirst : (machine tag).step ((machine tag).initCfg word) = some first := by
    simpa [TM.step, machine, first, Tape.read, Tape.init, Tape.write,
      Tape.move] using emptyWork _ _
  cases tag with
  | none =>
      obtain ⟨final, hrun, hhalt, hout⟩ := loop none word [] word.length 0 first
        (by simp) rfl (by simp [first, Tape.move]) (by simp [first, Tape.move])
        (by simpa [first] using Tape.init_nil_move_right_hasBinaryPrefix_nil)
        (Nat.zero_le _)
      exact ⟨final, by simpa [Nat.add_assoc] using TM.reachesIn.step hfirst hrun,
        hhalt, hout⟩
  | some bit =>
      let second : Cfg 0 (machine (some bit)).Q :=
        ⟨.copying, first.input, fun i => Fin.elim0 i,
          first.output.writeAndMove (Γ.ofBool bit) .right⟩
      have hread : first.input.read ≠ Γ.start := by
        cases word with
        | nil => simp [first, Tape.read, Tape.move, Tape.init]
        | cons b rest => cases b <;> simp [first, Tape.read, Tape.move, Tape.init, Γ.ofBool]
      have hsecond : (machine (some bit)).step first = some second := by
        dsimp [first, Tape.move] at hread
        cases bit <;>
          simpa [TM.step, machine, first, second, Primitive.safeDirection, hread, Tape.move,
            Γw.ofBool, Γ.ofBool] using emptyWork _ _
      have hp : second.output.HasBinaryPrefix [bit] := by
        simpa [first, second] using Tape.hasBinaryPrefix_write_bit bit
          Tape.init_nil_move_right_hasBinaryPrefix_nil
      obtain ⟨final, hrun, hhalt, hout⟩ := loop (some bit) word [bit] word.length 0 second
        (by simp) rfl (by simp [second, first, Tape.move])
        (by simp [second, first, Tape.move]) (by simpa using hp) (Nat.zero_le _)
      exact ⟨final, by simpa [Nat.add_assoc] using
        TM.reachesIn.step hfirst (TM.reachesIn.step hsecond hrun), hhalt, hout⟩

/-- An exact run certificate with its transition count fixed before choosing the final state. -/
noncomputable def run (tag : Option Bool) (word : Word) :
    ExactRun (machine tag) word (tag.toList ++ word) where
  final := Classical.choose (reaches tag word)
  steps := word.length + 2 + if tag.isSome then 1 else 0
  reaches := (Classical.choose_spec (reaches tag word)).1
  halted := (Classical.choose_spec (reaches tag word)).2.1
  output_correct := (Classical.choose_spec (reaches tag word)).2.2

end LinearCopy

/-! ## Represented code and polynomial bounds -/

/-- One concrete identity machine for every trusted representation, charged for copying it. -/
noncomputable def copyCode {A : Type} (rep : Representation A) : Code rep rep id where
  workTapes := 0
  machine := LinearCopy.machine none
  wordFunction := id
  run := LinearCopy.run none
  encode_eq _ := rfl

/-- Inject a represented value into the left summand by copying it after the false tag. -/
noncomputable def inlCopyCode {A B : Type} (a : Representation A) (b : Representation B) :
    Code a (.sum a b) (Sum.inl : A → A ⊕ B) where
  workTapes := 0
  machine := LinearCopy.machine (some false)
  wordFunction := List.cons false
  run := LinearCopy.run (some false)
  encode_eq _ := rfl

/-- Encode a present optional value by copying its payload after the true tag. -/
noncomputable def someCopyCode {A : Type} (rep : Representation A) :
    Code rep (.option rep) some where
  workTapes := 0
  machine := LinearCopy.machine (some true)
  wordFunction := List.cons true
  run := LinearCopy.run (some true)
  encode_eq _ := rfl

/-- Identity's charged work grows with the encoded input length. -/
@[simp] theorem copyCode_cost {A : Type} (rep : Representation A) (value : A) :
    quantitativeStepClass.cost (copyCode rep) value = encodedSize rep value + 2 := by
  rfl

/-- Left injection pays for the tag and every copied payload bit. -/
@[simp] theorem inlCopyCode_cost {A B : Type} (a : Representation A) (b : Representation B)
    (value : A) : quantitativeStepClass.cost (inlCopyCode a b) value =
      encodedSize a value + 3 := by
  rfl

/-- Optional-value injection also copies and tags its complete input. -/
@[simp] theorem someCopyCode_cost {A : Type} (rep : Representation A) (value : A) :
    quantitativeStepClass.cost (someCopyCode rep) value = encodedSize rep value + 3 := by
  rfl

/-- Polynomial identity code, preserving input size exactly. -/
@[expose] noncomputable def copyPolyRealizer {A : Type} (rep : Representation A) :
    quantitativeStepClass.PolyRealizer rep rep id where
  code := copyCode rep
  work := .add .input (.const 2)
  outputSize := .input
  work_le value := by rw [copyCode_cost]; rfl
  outputSize_le _ := le_rfl

/-- Polynomial left-injection code, with exactly one bit of output growth. -/
@[expose] noncomputable def inlCopyPolyRealizer {A B : Type}
    (a : Representation A) (b : Representation B) :
    quantitativeStepClass.PolyRealizer a (.sum a b) (Sum.inl : A → A ⊕ B) where
  code := inlCopyCode a b
  work := .add .input (.const 3)
  outputSize := .add .input (.const 1)
  work_le value := by rw [inlCopyCode_cost]; rfl
  outputSize_le _ := by simp [quantitativeStepClass, encodedSize]

/-- Polynomial optional-value code, with exactly one bit of output growth. -/
@[expose] noncomputable def someCopyPolyRealizer {A : Type} (rep : Representation A) :
    quantitativeStepClass.PolyRealizer rep (.option rep) some where
  code := someCopyCode rep
  work := .add .input (.const 3)
  outputSize := .add .input (.const 1)
  work_le value := by rw [someCopyCode_cost]; rfl
  outputSize_le _ := by simp [quantitativeStepClass, encodedSize]

end VCVioComplexity.Backend.TuringMachine
