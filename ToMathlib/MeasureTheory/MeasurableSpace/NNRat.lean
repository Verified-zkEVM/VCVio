/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.NNRat.Encodable
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! # The measurable subtype structure on nonnegative rationals -/

public section

namespace NNRat

instance instMeasurableSpaceSubtype : MeasurableSpace ℚ≥0 :=
  inferInstanceAs (MeasurableSpace {q : ℚ // 0 ≤ q})

instance : MeasurableSingletonClass ℚ≥0 :=
  inferInstanceAs (MeasurableSingletonClass {q : ℚ // 0 ≤ q})

end NNRat
