/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Model.SequenceLaws
public import PolyFunCryptol.Translation.SourceElaboration
public import PolyFun.Control.Semantics.Correspondence

/-!
# Finite views of Foundation lists

Foundation's `List a` is a suspended infinite stream paired with an integer
length. A finite view observes exactly that length and its in-range elements.
An empty list does not demand the stream, and tails beyond the length are
irrelevant. This is a logical relation, not an equivalence of semantic carriers.
The laws concern the representation boundary; they do not certify translation
of Foundation's list functions.
-/

public section

namespace Cryptol.Bridge.ListView

open OmegaCompletePartialOrder

/-- Carrier of the Foundation list type synonym, using the importer's tuple spine. -/
abbrev listType (a : ClosedTy) : ClosedTy := .prod (.seq .infinite a) (.prod .integer .unit)

/-- The finite view uses exactly the carrier assigned to the source tuple. -/
theorem coreType_list (a : Reference.ValueType) :
    Translation.SourceElaboration.coreType (.tuple [.seq .infinite a, .integer]) =
      listType (Translation.SourceElaboration.coreType a) := rfl

/-- A finite native list observes only the represented prefix of a lazy source list. -/
@[expose] noncomputable def Represents {A : Type} {a : ClosedTy}
    (element : A → Computation a → Prop) (xs : List A)
    (value : Computation (listType a)) : Prop :=
  ∃ (stream : Computation (.seq .infinite a)) (endTuple : Computation .unit),
    value = DomainResult.value (stream,
      DomainResult.value (DomainResult.value ⟨(xs.length : Int)⟩, endTuple)) ∧
    ∀ i : Fin xs.length, element xs[i] (Semantics.indexAt stream (i.val : Int))

/-- Encoding permits any undefined or defined tail after the finite prefix. -/
@[expose] noncomputable def encode {A : Type} {a : ClosedTy}
    (element : A → Computation a) (xs : List A) (tail : Nat → Computation a) :
    Computation (listType a) :=
  DomainResult.value (DomainResult.value (fun i : Nat =>
    if h : i < xs.length then element xs[i] else tail (i - xs.length)),
    DomainResult.value (DomainResult.value ⟨(xs.length : Int)⟩, DomainResult.value ⟨()⟩))

/-- The encoding represents the finite list regardless of its unused tail. -/
theorem represents_encode {A : Type} {a : ClosedTy}
    (relation : A → Computation a → Prop) (element : A → Computation a)
    (faithful : ∀ x, relation x (element x)) (xs : List A) (tail : Nat → Computation a) :
    Represents relation xs (encode element xs tail) := by
  refine ⟨_, _, rfl, ?_⟩
  intro i
  rw [Semantics.indexAt_value_infinite]
  simp only [dite_eq_left i.isLt, Fin.getElem_fin]
  exact faithful _

/-- Even an undefined entire stream represents the empty finite list. -/
theorem represents_nil {A : Type} {a : ClosedTy} (relation : A → Computation a → Prop)
    (stream : Computation (.seq .infinite a)) (endTuple : Computation .unit) :
    Represents relation [] (DomainResult.value
      (stream, DomainResult.value (DomainResult.value ⟨0⟩, endTuple))) :=
  ⟨stream, endTuple, rfl, fun i => Fin.elim0 i⟩

/-- Functional element observations give a unique native finite list. -/
theorem represents_leftUnique {A : Type} {a : ClosedTy}
    {relation : A → Computation a → Prop} (unique : Relator.LeftUnique relation) :
    Relator.LeftUnique (Represents relation) := by
  intro xs ys value hx hy
  obtain ⟨sx, ux, hx, hxs⟩ := hx
  obtain ⟨sy, uy, hy, hys⟩ := hy
  have pairEq := DomainResult.value_inj.mp (hx.symm.trans hy)
  have streamEq : sx = sy := congrArg Prod.fst pairEq
  have lengthEq : xs.length = ys.length := by
    have tailEq := DomainResult.value_inj.mp (congrArg Prod.snd pairEq)
    have h := DomainResult.value_inj.mp (congrArg Prod.fst tailEq)
    exact Int.ofNat_inj.mp (congrArg DiscreteOrder.value h)
  apply List.ext_getElem lengthEq
  intro i hi hj
  apply unique (hxs ⟨i, hi⟩)
  simpa only [streamEq, Fin.getElem_fin] using hys ⟨i, hj⟩

/-- Every native list has a representative with bottom in the unused tail. -/
theorem represents_leftTotal {A : Type} {a : ClosedTy}
    (relation : A → Computation a → Prop) (element : A → Computation a)
    (faithful : ∀ x, relation x (element x)) : Relator.LeftTotal (Represents relation) :=
  fun xs => ⟨encode element xs (fun _ => ⊥), represents_encode relation element faithful xs _⟩

/-- Contracts transfer through a prefix logical relation without identifying unused tails. -/
theorem contract_iff {A B : Type} {a b : ClosedTy}
    (input : A → Computation a → Prop) (output : B → Computation b → Prop)
    (implementation : List A → List B)
    (meaning : Computation (listType a) → Computation (listType b))
    (pre : List A → Prop) (post : List A → List B → Prop)
    (correct : Relator.LiftFun (fun xs value => pre xs ∧ Represents input xs value)
      (Represents output) implementation meaning)
    (available : ∀ xs, pre xs → ∃ value, Represents input xs value)
    (unique : Relator.LeftUnique output) :
    Control.Semantics.RelationalContract (Represents input) (Represents output)
      meaning pre post ↔ ∀ xs, pre xs → post xs (implementation xs) :=
  Control.Semantics.RelationalContract.iff_of_liftFun pre post correct available
    (represents_leftUnique unique)

end Cryptol.Bridge.ListView
