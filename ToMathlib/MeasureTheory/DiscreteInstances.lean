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

Everything here follows the upstream file's style exactly and is a candidate for
contribution to it; nothing in this file is specific to VCVio.

## Why `⊤` rather than a blanket instance

There is deliberately no `[Finite α] → MeasurableSpace α := ⊤` instance. It would overlap the
concrete instances above and, more seriously, would compete with the Borel σ-algebras that
lattice-based cryptography needs on `ℝ`. Discrete measurable structure is opted into per type,
exactly as upstream does it.
-/

public section

instance BitVec.instMeasurableSpace (n : ℕ) : MeasurableSpace (BitVec n) := ⊤

instance BitVec.instMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (BitVec n) := ⟨fun _ => trivial⟩

instance BitVec.instDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (BitVec n) := inferInstance
