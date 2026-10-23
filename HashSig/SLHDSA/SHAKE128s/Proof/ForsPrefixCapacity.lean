/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ForsConcentrationOccupancy
public import Mathlib.Probability.Independence.Basic

/-!
# Disclosure tapes for FORS prefix capacity

The sample space for counting FORS leaf disclosures with fixed instance assignments: a `Tape`
holds, for every FORS instance `i`, one uniformly random leaf in each of the 10 FORS trees of
`i` per signing request assigned to `i`, and `tapeMeasure` is the product of the uniform
measures. This models independent leaf samples only; it does not identify an adaptive
shared-oracle transcript with that distribution.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SlhDsaSecurity.ForsPrefixCapacity

noncomputable section

/-- A leaf index in a FORS tree of height 12. -/
abbrev Leaf := Fin 4096
/-- One disclosed leaf in a single FORS tree for each of `requests` signing requests. -/
abbrev TreeTape (requests : Nat) := Fin requests → Leaf
/-- The disclosed leaves of all 10 trees of one FORS instance over `requests` signing
requests. -/
abbrev InstanceTape (requests : Nat) := Fin 10 → TreeTape requests
/-- The disclosed leaves of every FORS instance `i`, which serves `loads i` signing requests. -/
abbrev Tape {ι : Type*} (loads : ι → Nat) := (i : ι) → InstanceTape (loads i)

/-- The uniform distribution on leaves. -/
def leafMeasure : Measure Leaf := uniformOn Set.univ
/-- Independent uniform leaves for every request in one tree. -/
def treeMeasure (requests : Nat) : Measure (TreeTape requests) :=
  Measure.pi (fun _ => leafMeasure)
/-- Independent uniform leaves for every tree and request of one instance. -/
def instanceMeasure (requests : Nat) : Measure (InstanceTape requests) :=
  Measure.pi (fun _ => treeMeasure requests)
/-- Independent uniform leaves for every instance, tree and request. -/
def tapeMeasure {ι : Type*} [Fintype ι] (loads : ι → Nat) : Measure (Tape loads) :=
  Measure.pi (fun i => instanceMeasure (loads i))

/-- The uniform leaf distribution is a probability measure. -/
instance : IsProbabilityMeasure leafMeasure := by unfold leafMeasure; infer_instance
/-- The per-tree leaf distribution is a probability measure. -/
instance (n : Nat) : IsProbabilityMeasure (treeMeasure n) := by
  unfold treeMeasure; infer_instance
/-- The per-instance leaf distribution is a probability measure. -/
instance (n : Nat) : IsProbabilityMeasure (instanceMeasure n) := by
  unfold instanceMeasure; infer_instance
/-- The tape distribution is a probability measure. -/
instance {ι : Type*} [Fintype ι] (loads : ι → Nat) :
    IsProbabilityMeasure (tapeMeasure loads) := by unfold tapeMeasure; infer_instance

end

end SlhDsaSecurity.ForsPrefixCapacity
