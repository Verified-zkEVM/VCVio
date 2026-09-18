/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable spaces on additive and multiplicative type tags

Algebraic type tags carry the measurable space of their underlying type. The tag conversions
are measurable in both directions.
-/

public section

variable {α : Type*} [MeasurableSpace α]

namespace Multiplicative

instance instMeasurableSpace : MeasurableSpace (Multiplicative α) := ‹MeasurableSpace α›

instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Multiplicative α) := ‹MeasurableSingletonClass α›

instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (Multiplicative α) := ‹DiscreteMeasurableSpace α›

@[fun_prop]
theorem measurable_ofAdd : Measurable (ofAdd : α → Multiplicative α) := measurable_id

@[fun_prop]
theorem measurable_toAdd : Measurable (toAdd : Multiplicative α → α) := measurable_id

end Multiplicative

namespace Additive

instance instMeasurableSpace : MeasurableSpace (Additive α) := ‹MeasurableSpace α›

instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Additive α) := ‹MeasurableSingletonClass α›

instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (Additive α) := ‹DiscreteMeasurableSpace α›

@[fun_prop]
theorem measurable_ofMul : Measurable (ofMul : α → Additive α) := measurable_id

@[fun_prop]
theorem measurable_toMul : Measurable (toMul : Additive α → α) := measurable_id

end Additive
