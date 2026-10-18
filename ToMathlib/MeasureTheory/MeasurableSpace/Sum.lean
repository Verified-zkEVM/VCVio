/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! # Measurable singletons in coproducts -/

public section

namespace Sum

instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton value := by
    cases value <;> simp [measurableSet_sum_iff, Set.preimage]

end Sum
