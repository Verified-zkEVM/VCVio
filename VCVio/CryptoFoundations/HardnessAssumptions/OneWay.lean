/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.EvalDist.UniformCompatibility
public import VCVio.OracleComp.ProbComp

/-!
# One-Way Functions and Trapdoor Permutations

This file defines one-way functions (OWFs) and one-way trapdoor permutations (OW-TDPs),
along with their security experiments.

## One-Way Functions

A function `f : X → Y` is one-way if no efficient adversary, given `f(x)` for a random `x`,
can find any preimage `x'` with `f(x') = f(x)`.

## Trapdoor Permutations

A trapdoor permutation has a key generation algorithm that produces a public key `pk`
and a secret key `sk`. The forward direction `f(pk, ·)` is a permutation that is hard to
invert given only `pk`; the secret key enables efficient inversion via `f⁻¹(sk, ·)`.

## Main Definitions

- `OWFAdversary X Y` — an adversary trying to invert `f`.
- `owfExperiment` — the one-wayness experiment.
- `TrapdoorPermutation PK SK X` — a trapdoor permutation scheme.
- `TDPAdversary PK X` — an adversary trying to invert the TDP.
- `tdpExperiment` — the TDP inversion experiment.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace OneWay

variable {X Y : Type}

/-! ## One-Way Functions -/

/-- An OWF adversary receives `f(x)` and tries to find a preimage. -/
def OWFAdversary (X Y : Type) := Y → ProbComp X

/-- Sample a challenge and the adversary's candidate preimage. -/
def owfRun [SampleableType X] (f : X → Y) (adversary : OWFAdversary X Y) :
    ProbComp (X × X) := do
  let x ← $ᵗ X
  let x' ← adversary (f x)
  return (x, x')

/-- One-wayness experiment: sample `x` uniformly, give the adversary `f(x)`,
and check whether the adversary's output is a valid preimage. -/
def owfExperiment [SampleableType X] [DecidableEq Y] (f : X → Y) (adversary : OWFAdversary X Y) :
    ProbComp Bool := do
  let (x, x') ← owfRun f adversary
  return decide (f x' = f x)

/-- OWF advantage: the probability that `owfExperiment` outputs `true`. -/
noncomputable def owfAdvantage [SampleableType X] [DecidableEq Y] (f : X → Y)
    (adversary : OWFAdversary X Y) : ℝ≥0∞ :=
  𝒟[owfExperiment f adversary] {true}

/-! ## Trapdoor Permutations -/

variable {PK SK : Type}

/-- A trapdoor permutation with key spaces `PK`/`SK` and domain `X`.
The forward direction is a permutation computable from the public key;
the inverse requires the secret key (the trapdoor). -/
structure TrapdoorPermutation (PK SK X : Type) where
  keygen : ProbComp (PK × SK)
  forward : PK → X → X
  inverse : SK → X → X

/-- A trapdoor permutation is correct if inversion recovers the original input
for all honestly generated key pairs. -/
def TrapdoorPermutation.Correct (tdp : TrapdoorPermutation PK SK X) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support tdp.keygen →
    ∀ x, tdp.inverse sk (tdp.forward pk x) = x

/-- A TDP adversary receives the public key and a challenge `y = f(pk, x)`,
and tries to find a valid preimage of `y`. -/
def TDPAdversary (PK X : Type) := PK → X → ProbComp X

/-- Generate keys, sample a challenge, and retain the adversary's candidate preimage. -/
def tdpRun [SampleableType X] (tdp : TrapdoorPermutation PK SK X)
    (adversary : TDPAdversary PK X) : ProbComp ((PK × X) × X) := do
  let (pk, _) ← tdp.keygen
  let x ← $ᵗ X
  let x' ← adversary pk (tdp.forward pk x)
  return ((pk, x), x')

/-- TDP inversion experiment: generate keys, sample `x` uniformly,
and check whether the adversary outputs a valid preimage of `f(pk, x)`. -/
def tdpExperiment [SampleableType X] [DecidableEq X] (tdp : TrapdoorPermutation PK SK X)
    (adversary : TDPAdversary PK X) : ProbComp Bool := do
  let ((pk, x), x') ← tdpRun tdp adversary
  return decide (tdp.forward pk x' = tdp.forward pk x)

/-- TDP advantage: the probability that `tdpExperiment` outputs `true`. -/
noncomputable def tdpAdvantage [SampleableType X] [DecidableEq X]
    (tdp : TrapdoorPermutation PK SK X) (adversary : TDPAdversary PK X) : ℝ≥0∞ :=
  𝒟[tdpExperiment tdp adversary] {true}

end OneWay
