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

Singleton measurability and discreteness lift to Mathlib's measurable spaces on algebraic
type tags. The four measurable conversions are available to `fun_prop`.
-/

public section

attribute [fun_prop] measurable_ofAdd measurable_toAdd measurable_ofMul measurable_toMul

variable {α : Type*} [MeasurableSpace α]

namespace Multiplicative

instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Multiplicative α) := ‹MeasurableSingletonClass α›

instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (Multiplicative α) := ‹DiscreteMeasurableSpace α›

end Multiplicative

namespace Additive

instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Additive α) := ‹MeasurableSingletonClass α›

instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (Additive α) := ‹DiscreteMeasurableSpace α›

end Additive
