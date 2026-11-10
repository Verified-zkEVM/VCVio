/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction
public import Lean.Util.CollectAxioms

/-! Single-group certified algebraic interaction tests. -/

public section

open OracleComp OracleSpec GroupModel.Interaction

namespace AGMTest.Interaction

private abbrev Group := fun _ : Unit => Nat

-- The same certified interface also supports programs with no oracle requests.
private def noOracles : Adversary Nat Group Unit Empty (fun _ => Unit) Unit where
  main input := pure (Explained.ofVectors input.groups () (fun _ => [fun _ => 1]))
  algebraic input := Explained.valid_ofVectors input.groups () (fun _ => [fun _ => 1])

example : (noOracles.run (N := Id) (fun q => nomatch q.data) ⟨(), fun _ => [2, 3]⟩).1.value =
    ⟨(), fun _ => [5]⟩ := rfl

-- Replies may be ordinary scalar data; neither hashing nor signing is prescribed.
private def measured : Adversary Nat Group Nat Nat (fun _ => Nat) Nat where
  main input := do
    let first ← (explainedSpec Nat Group Nat (fun _ => Nat)).query
      ⟨⟨input.data, fun _ => []⟩, fun _ => []⟩
    let second ← (explainedSpec Nat Group Nat (fun _ => Nat)).query
      ⟨⟨input.data + first.data, fun _ => []⟩, fun _ => []⟩
    return Explained.ofVectors (extend (extend input.groups first.groups) second.groups)
      second.data (fun _ => [fun _ => first.data])
  algebraic input := by
    refine ⟨fun _ => List.Forall₂.nil, fun first => ?_⟩
    refine ⟨fun _ => List.Forall₂.nil, fun second => ?_⟩
    exact Explained.valid_ofVectors _ _ _

example : (measured.run (N := Id) (fun q => pure ⟨q.data + 1, fun _ => []⟩)
    ⟨2, fun _ => [4, 5]⟩).1.value = ⟨6, fun _ => [27]⟩ := rfl

private abbrev spec := explainedSpec Nat Group Nat (fun _ => Unit)

-- Ordinary do notation, two adaptive calls, and multiple group arguments in the second call.
private def adaptive (inputs : Groups Group) : OracleComp spec (Explained Nat String Group) := do
  let first ← spec.query (Explained.ofVectors inputs 0 (fun _ => [fun _ => 1]))
  let basis := extend inputs first.groups
  let second ← spec.query (Explained.ofVectors basis (first.groups ()).length
    (fun _ => [fun _ => 1, fun _ => 0]))
  return Explained.ofVectors (extend basis second.groups) "done" (fun _ => [fun _ => 1])

private theorem adaptive_algebraic (inputs : Groups Group) : IsAlgebraic inputs (adaptive inputs)
    := by
  constructor
  · exact Explained.valid_ofVectors _ _ _
  intro first
  constructor
  · exact Explained.valid_ofVectors _ _ _
  intro second
  exact Explained.valid_ofVectors _ _ _

private def adversary : Adversary Nat Group Unit Nat (fun _ => Unit) String where
  main input := adaptive input.groups
  algebraic input := adaptive_algebraic input.groups

-- Replies are plain messages: no coefficient vectors or known logarithms are supplied.
private def impl : QueryImpl (plainSpec Group Nat (fun _ => Unit))
    (StateM (List (Message Nat Group))) := fun q => do
  modify (· ++ [q])
  return ⟨(), fun _ => if q.data = 0 then [7] else [11]⟩

example : ((adversary.run impl ⟨(), fun _ => [2, 3]⟩).run []).1.1.value =
    ⟨"done", fun _ => [23]⟩ := rfl

-- Only incoming replies extend the basis, not the outgoing values 5, 12, or 0.
example : ((adversary.run impl ⟨(), fun _ => [2, 3]⟩).run []).1.2 () = [2, 3, 7, 11] := rfl

example : ((adversary.run impl ⟨(), fun _ => [2, 3]⟩).run []).2 =
    [⟨0, fun _ => [5]⟩, ⟨1, fun _ => [12, 0]⟩] := rfl

-- A wrong value, missing vector, short vector, and extra coefficient are all rejected.
example : ¬ (⟨⟨(), fun _ => [7]⟩, fun _ => [[1]]⟩ : Explained Nat Unit Group).Valid (fun _ => [2])
    := by
  simp [Explained.Valid, GroupModel.Interaction.evaluate]
example : ¬ (⟨⟨(), fun _ => [2, 2]⟩, fun _ => [[1]]⟩ : Explained Nat Unit Group).Valid
    (fun _ => [2]) := by
  simp [Explained.Valid, GroupModel.Interaction.evaluate]
example : ¬ (⟨⟨(), fun _ => [2]⟩, fun _ => [[1]]⟩ : Explained Nat Unit Group).Valid
    (fun _ => [2, 3]) := by
  simp [Explained.Valid, GroupModel.Interaction.evaluate]
example : ¬ (⟨⟨(), fun _ => [2]⟩, fun _ => [[1, 0]]⟩ : Explained Nat Unit Group).Valid
    (fun _ => [2]) := by
  simp [Explained.Valid, GroupModel.Interaction.evaluate]

-- A group-free request is legal even with an empty basis: hash-to-group needs no input witness.
example : (⟨⟨"hash this message", fun _ => []⟩, fun _ => []⟩ : Explained Nat String Group).Valid
    (fun _ => []) := by
  simp [Explained.Valid, GroupModel.Interaction.evaluate]

/-- Any fresh group reply is accepted without an explanation in the old (here empty) basis. -/
theorem isAlgebraic_fresh_reply {F G : Type} [Zero F] [One F] [AddMonoid G] [SMul F G] :
    IsAlgebraic (Reply := fun _ : String => Unit) (fun _ : Unit => ([] : List G))
      (OracleComp.queryBind (⟨⟨"hash", fun _ => []⟩, fun _ => []⟩ : Explained F String (fun _
          : Unit => G))
        (fun reply => pure (Explained.ofVectors reply.groups () (fun _ => [fun _ => 1])))) := by
  constructor
  · exact fun _ => .nil
  intro reply
  exact Explained.valid_ofVectors _ _ _

-- Equal received elements are separate basis positions, with separate coefficients.
example : (⟨⟨(), fun _ => [10]⟩, fun _ => [[2, 3]]⟩ : Explained Nat Unit Group).Valid
    (fun _ => [2, 2]) := by
  simp [Explained.Valid, GroupModel.Interaction.evaluate]

-- A later reply cannot justify an earlier outgoing group argument.
example : ¬ IsAlgebraic (fun _ : Unit => ([] : List Nat))
    (OracleComp.queryBind (spec := spec) (⟨⟨0, fun _ => [7]⟩, fun _ => [[]]⟩
        : Explained Nat Nat Group)
      (fun reply => pure (Explained.ofVectors reply.groups () (fun _ => [fun _ => 1])))) := by
  intro h
  have invalid : ¬ (⟨⟨0, fun _ => [7]⟩, fun _ => [[]]⟩ : Explained Nat Nat Group).Valid
      (fun _ => []) := by
    simp [Explained.Valid, GroupModel.Interaction.evaluate]
  exact invalid h.1

-- The same check applies to final outputs, not just queries.
example : ¬ IsAlgebraic (Reply := fun _ : Nat => Unit) (fun _ => [2])
    (pure (⟨⟨(), fun _ => [7]⟩, fun _ => [[1]]⟩ : Explained Nat Unit Group)) := by
  change ¬ (⟨⟨(), fun _ => [7]⟩, fun _ => [[1]]⟩ : Explained Nat Unit Group).Valid (fun _ => [2])
  simp [Explained.Valid, GroupModel.Interaction.evaluate]

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``Adversary.run_valid, ``Explained.valid_ofVectors] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"
  for name in #[`Model.LazyAGM.advSpec, `GroupModel.BilinearPairing] do
    if (← getEnv).contains name then
      throwError "Interactive AGM unexpectedly imports signature infrastructure: {name}"

end AGMTest.Interaction
