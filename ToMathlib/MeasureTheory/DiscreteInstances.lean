/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Discrete measurable-space instances for cryptographic sample types

Mathlib equips a selection of standard countable types with the discrete σ-algebra `⊤` in
`Mathlib.MeasureTheory.MeasurableSpace.Instances` — `Bool`, `ℕ`, `ℤ`, `ℚ`, `Fin n`, `ZMod n`
among them. `BitVec n` is not on that list, and it is the type most cryptographic sampling
statements are phrased over.

Everything here follows the upstream file's style exactly so the local compatibility layer is easy
to remove if Mathlib gains the same instances; nothing in this file is specific to VCVio.

## Why `⊤` rather than a blanket instance

There is deliberately no `[Finite α] → MeasurableSpace α := ⊤` instance. It would overlap the
concrete instances above and other selected σ-algebras on finite types: finiteness alone does not
choose a measurable space. Once a space is selected, Mathlib derives `DiscreteMeasurableSpace α`
from `Countable α` and `MeasurableSingletonClass α`. Discrete measurable structure is opted into
per type, exactly as upstream does it. Continuous types retain their canonical Borel structures.
-/

public section

/-- `BitVec n` is finite, hence countable.

Mathlib derives `Fintype (BitVec n)` from `FinEnum (BitVec n)` (`Mathlib.Data.FinEnum`), which this
module deliberately does not import; the `Finite` instance is restated here so that this module
stands alone: without `Countable` in scope,
`MeasurableSingletonClass.toDiscreteMeasurableSpace` does not fire, and the discrete structure
below fails to propagate to products and function types — which is exactly what cryptographic
sampling statements are built from. `Finite` is `Prop`-valued, so this cannot conflict with any
`Fintype` instance. -/
instance BitVec.instFinite (n : ℕ) : Finite (BitVec n) :=
  Finite.of_injective BitVec.toFin fun _ _ h => BitVec.toFin_inj.mp h

instance BitVec.instMeasurableSpace (n : ℕ) : MeasurableSpace (BitVec n) := ⊤

instance BitVec.instMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (BitVec n) := ⟨fun _ => trivial⟩

instance BitVec.instDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (BitVec n) := inferInstance

/-! ## Lists over a countable alphabet

A computation that draws repeatedly returns a `List`, and observing the *whole* draw — rather
than a numeric summary of it — needs a σ-algebra on that list type. Mathlib equips no list type
with one, so there is nothing to overlap with, and countability already forces any reasonable
choice to be discrete. The guard is `Countable`, not `Finite`: `List α` is countable exactly when
`α` is, and the instances below are the ones Mathlib derives from `⊤` in that case.
-/

/-- `Countable` is a guard on when this fires, not data the σ-algebra reads, so the argument is
deliberately unused in the value. -/
@[nolint unusedArguments]
instance List.instMeasurableSpace {α : Type*} [Countable α] : MeasurableSpace (List α) := ⊤

instance List.instMeasurableSingletonClass {α : Type*} [Countable α] :
    MeasurableSingletonClass (List α) := ⟨fun _ => trivial⟩

instance List.instDiscreteMeasurableSpace {α : Type*} [Countable α] :
    DiscreteMeasurableSpace (List α) := inferInstance
