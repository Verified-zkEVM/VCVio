/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsConcentrationOccupancy
public import Mathlib.Probability.Independence.Basic

/-!
# Simultaneous prefix capacity for a fixed disclosure tape

These probability lemmas concern independent leaf samples with fixed instance
assignments. They do not identify an adaptive shared-oracle transcript with that
distribution.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace SlhDsaSecurity.ForsPrefixCapacity

noncomputable section

abbrev Leaf := Fin 4096
abbrev TreeTape (requests : Nat) := Fin requests → Leaf
abbrev InstanceTape (requests : Nat) := Fin 10 → TreeTape requests
abbrev Tape {ι : Type*} (loads : ι → Nat) := (i : ι) → InstanceTape (loads i)

def leafMeasure : Measure Leaf := (PMF.uniformOfFintype Leaf).toMeasure
def treeMeasure (requests : Nat) : Measure (TreeTape requests) :=
  Measure.pi (fun _ => leafMeasure)
def instanceMeasure (requests : Nat) : Measure (InstanceTape requests) :=
  Measure.pi (fun _ => treeMeasure requests)
def tapeMeasure {ι : Type*} [Fintype ι] (loads : ι → Nat) : Measure (Tape loads) :=
  Measure.pi (fun i => instanceMeasure (loads i))

instance : IsProbabilityMeasure leafMeasure := by unfold leafMeasure; infer_instance
instance (n : Nat) : IsProbabilityMeasure (treeMeasure n) := by
  unfold treeMeasure; infer_instance
instance (n : Nat) : IsProbabilityMeasure (instanceMeasure n) := by
  unfold instanceMeasure; infer_instance
instance {ι : Type*} [Fintype ι] (loads : ι → Nat) :
    IsProbabilityMeasure (tapeMeasure loads) := by unfold tapeMeasure; infer_instance

end

end SlhDsaSecurity.ForsPrefixCapacity
