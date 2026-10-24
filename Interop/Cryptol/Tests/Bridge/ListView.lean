/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.ListView

/-! # Partial-list views through ordinary public imports -/

public section

open Cryptol Cryptol.Bridge.ListView

namespace Cryptol.Tests.ListView

/-- A returned Boolean element. -/
def bit (b : Bool) : Computation .bit := DomainResult.value ⟨b⟩
/-- Native Booleans represented by returned elements. -/
def bitRelation (b : Bool) (value : Computation .bit) : Prop := value = bit b

example : Represents bitRelation []
    (DomainResult.value ((⊥ : Computation (.seq .infinite .bit)),
      DomainResult.value (DomainResult.value ⟨0⟩, ⊥))) :=
  represents_nil _ _ _

example (a : Reference.ValueType) :
    Translation.SourceElaboration.coreType (.tuple [.seq .infinite a, .integer]) =
      listType (Translation.SourceElaboration.coreType a) := coreType_list a

example (xs : List Bool) (tail : Nat → Computation .bit) :
    Represents bitRelation xs (encode bit xs tail) :=
  represents_encode bitRelation bit (fun _ => rfl) xs tail

example (xs ys : List Bool) (value : Computation (listType .bit))
    (hx : Represents bitRelation xs value) (hy : Represents bitRelation ys value) : xs = ys := by
  apply represents_leftUnique (relation := bitRelation) ?_ hx hy
  intro a b value ha hb
  exact congrArg DiscreteOrder.value (DomainResult.value_inj.mp (ha.symm.trans hb))

example : ¬ Relator.RightUnique (Represents bitRelation) := by
  intro unique
  have h := unique (represents_nil bitRelation (⊥ : Computation (.seq .infinite .bit)) ⊥)
    (represents_nil bitRelation (DomainResult.error (EvalError.user "unused")) ⊥)
  have streams := congrArg Prod.fst (DomainResult.value_inj.mp h)
  exact DomainResult.error_ne_bot (EvalError.user "unused") streams.symm

end Cryptol.Tests.ListView
