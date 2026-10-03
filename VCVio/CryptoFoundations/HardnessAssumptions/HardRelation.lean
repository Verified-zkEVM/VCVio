/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.Constructions.UniformFinMeasure

/-!
# Hard Relations

This file defines generable relations and the experiment that measures how hard they are. A
`GenerableRelation X W r` packages an algorithm `gen` that produces instance-witness pairs
satisfying a relation `r : X → W → Bool`. In `hardRelationExperiment` an adversary receives a
generated instance and wins if it returns a witness for it; the relation is hard when every
efficient adversary wins with small probability.

## Implementation notes

The relation and the experiment carry no security parameter, unlike the asymptotic games of
`VCVio.CryptoFoundations.Asymptotics.Security`.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

/-- A relation `r` is generable if there is an efficient algorithm `gen`
that produces instance-witness pairs satisfying the relation. -/
structure GenerableRelation
    (X W : Type) (r : X → W → Bool) where
  /-- An efficient algorithm producing instance-witness pairs. -/
  gen : ProbComp (X × W)
  /-- Every pair in the support of `gen` satisfies the relation `r`. -/
  gen_sound (x : X) (w : W) : (x, w) ∈ support gen → r x w

/-- Experiment for checking whether an adversary can find a witness for a generated instance. -/
def hardRelationExperiment {X W : Type} {r : X → W → Bool} (hr : GenerableRelation X W r)
    (adversary : X → ProbComp W) : ProbComp Bool := do
  let ⟨x, _⟩ ← hr.gen
  let w ← adversary x
  return r x w

