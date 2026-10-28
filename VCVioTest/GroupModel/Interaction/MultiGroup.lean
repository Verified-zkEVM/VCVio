/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction

/-! Multiple-group certified algebraic interaction tests. -/

public section

open OracleComp OracleSpec GroupModel.Interaction

namespace AGMTest.MultiGroup

-- Different carriers ensure the implementation is genuinely dependent on the sort.
private abbrev Group : Bool → Type
  | false => Nat
  | true => Int

private instance (s : Bool) : AddMonoid (Group s) := by
  cases s <;> dsimp [Group] <;> infer_instance

private instance (s : Bool) : SMul Nat (Group s) := by
  cases s <;> dsimp [Group] <;> infer_instance

private def initial : Groups Group
  | false => [2, 3]
  | true => [10]

private abbrev spec := explainedSpec Nat Group Nat (fun _ => Nat)

private def adaptive (inputs : Groups Group) : OracleComp spec (Explained Nat Nat Group) := do
  let first ← spec.query (Explained.ofVectors inputs 0 (fun _ => [fun _ => 1]))
  let basis := extend inputs first.groups
  let second ← spec.query (Explained.ofVectors basis first.data
    (fun s => [fun _ => if s then (first.groups false).length else first.data]))
  return Explained.ofVectors (extend basis second.groups) second.data (fun _ => [fun _ => 1])

-- The second query depends on earlier scalar and group replies across the two sorts.
private def adversary : Adversary Nat Group Unit Nat (fun _ => Nat) Nat where
  main input := adaptive input.groups
  algebraic input := by
    refine ⟨Explained.valid_ofVectors _ _ _, fun first => ?_⟩
    refine ⟨Explained.valid_ofVectors _ _ _, fun second => ?_⟩
    exact Explained.valid_ofVectors _ _ _

private def firstReply : Message Nat Group :=
  ⟨3, fun s => match s with | false => [7] | true => [13, 17]⟩

private def secondReply : Message Nat Group :=
  ⟨4, fun s => match s with | false => [] | true => [19]⟩

private def impl : QueryImpl (plainSpec Group Nat (fun _ => Nat))
    (StateM (List (Message Nat Group))) := fun q => do
  modify (· ++ [q])
  return if q.data = 0 then firstReply else secondReply

private def inspect (message : Message Nat Group) : Nat × List Nat × List Int :=
  (message.data, message.groups false, message.groups true)

example : inspect ((adversary.run impl ⟨(), initial⟩).run []).1.1.value =
    (4, [12], [59]) := rfl

-- Outgoing values never extend either basis. Each sort retains its own reply order.
example : ((adversary.run impl ⟨(), initial⟩).run []).1.2 =
    (fun s => match s with | false => [2, 3, 7] | true => [10, 13, 17, 19]) := by
  funext s
  cases s <;> rfl

example : ((adversary.run impl ⟨(), initial⟩).run []).2.map inspect =
    [(0, [5], [10]), (3, [36], [40])] := rfl

-- Isolation also holds when the two sorts happen to have the same carrier type.
private def wrongSort : Explained Nat Unit (fun _ : Bool => Nat) :=
  ⟨⟨(), fun s => if s then [7] else []⟩, fun s => if s then [[]] else []⟩

example : ¬ wrongSort.Valid (fun s => if s then [] else [7]) := by
  intro h
  have invalid := h true
  simp [wrongSort, GroupModel.Interaction.evaluate] at invalid

-- Equal basis lengths do not permit using the other sort's value either.
example : ¬ (⟨⟨(), fun s => if s then [2] else []⟩,
    fun s => if s then [[1]] else []⟩ : Explained Nat Unit (fun _ : Bool => Nat)).Valid
      (fun s => if s then [7] else [2]) := by
  intro h
  have invalid := h true
  simp [GroupModel.Interaction.evaluate] at invalid

-- Coefficient lengths are checked against the particular sort's basis, not a pooled basis.
example : ¬ (⟨⟨(), fun s => if s then [7] else []⟩,
    fun s => if s then [[0, 1]] else []⟩ : Explained Nat Unit (fun _ : Bool => Nat)).Valid
      (fun s => if s then [7] else [2, 3]) := by
  intro h
  have invalid := h true
  simp at invalid

-- Every output needs a vector; a final value cannot bypass the query checks.
example : ¬ IsAlgebraic (Reply := fun _ : Unit => Unit) (fun _ : Bool => [7])
    (pure (⟨⟨(), fun _ => [7]⟩, fun _ => []⟩ : Explained Nat Unit (fun _ : Bool => Nat))) := by
  intro h
  have invalid := h false
  simp at invalid

/-- A reply may introduce fresh values in both groups without explanations. -/
theorem isAlgebraic_fresh_reply {Tag F : Type} {G : Tag → Type} [Zero F] [One F]
    [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)] :
    IsAlgebraic (Reply := fun _ : String => Unit) (fun _ => ([] : List (G _)))
      (OracleComp.queryBind (⟨⟨"hash", fun _ => []⟩, fun _ => []⟩ : Explained F String G)
        (fun reply => pure (Explained.ofVectors reply.groups () (fun _ => [fun _ => 1])))) := by
  refine ⟨fun _ => .nil, fun reply => ?_⟩
  exact Explained.valid_ofVectors _ _ _

-- A future value in the correct sort cannot justify an earlier request.
example : ¬ IsAlgebraic (fun _ : Bool => ([] : List Nat))
    (OracleComp.queryBind (spec := explainedSpec Nat (fun _ : Bool => Nat) Unit (fun _ => Unit))
      wrongSort (fun reply => pure (Explained.ofVectors reply.groups () (fun _ => [fun _ => 1]))))
          := by
  intro h
  have invalid := h.1 true
  simp [wrongSort, GroupModel.Interaction.evaluate] at invalid

-- Repeated values still have separate positions within each sort's basis.
example : (⟨⟨(), fun _ => [10]⟩, fun _ => [[2, 3]]⟩ :
    Explained Nat Unit (fun _ : Bool => Nat)).Valid (fun _ => [2, 2]) := by
  intro s
  cases s <;> simp [GroupModel.Interaction.evaluate]

end AGMTest.MultiGroup
