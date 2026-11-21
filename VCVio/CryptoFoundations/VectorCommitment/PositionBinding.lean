/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Position binding of vector commitments

A position-binding adversary outputs one commitment together with two openings, each a partial
vector of claimed values and a proof. It wins when both openings are accepted and they
conflict (`PartialVec.Conflict`): some position is defined in both with different values (cf.
Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*, Version 1.2, Lemma 18.4.1,
stated there for Merkle trees).

The advantage is stated in the random oracle model: the experiment runs against the lazily
sampled random oracle `ProbCompRuntime.rom (X →ₒ Y)`, shared by the adversary and `Check`.

## Main definitions

* `VectorCommitment.PositionBindingAdversary`, `VectorCommitment.positionBindingExperiment` and
  `VectorCommitment.positionBindingAdvantage`.
* `VectorCommitment.PositionBindingAdversary.MakesAtMostQueries`: an oracle-query budget for the
  adversary.

## Main results

* `VectorCommitment.positionBindingAdvantage_def`: the position-binding advantage is the
  probability that the experiment accepts.

## References

* [Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*, Version 1.2,
  Lemma 18.4.1](https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex#L12981-L13005).
-/

public section

open OracleComp OracleSpec

namespace VectorCommitment

variable {X : Type} {Y : Type} {Msg : Type} {Cm Td Pf : Type} {ℓ : ℕ}

/-- A position-binding adversary outputs a commitment and two claimed openings, each a partial
vector of values with a proof. The openings are outputs of an oracle computation, so `Msg` is in
`Type`. -/
abbrev PositionBindingAdversary (X : Type) (Y : Type) (Msg : Type) (Cm Pf : Type) (ℓ : ℕ) :=
  OracleComp (unifSpec + (X →ₒ Y)) (Cm × (PartialVec ℓ Msg × Pf) × (PartialVec ℓ Msg × Pf))

/-- The position-binding experiment: run the adversary, and accept when its openings conflict
and `Check` accepts both against the same commitment. -/
@[expose]
def positionBindingExperiment [DecidableEq Msg] (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : PositionBindingAdversary X Y Msg Cm Pf ℓ) :
    OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let (cm, (a₁, pf₁), (a₂, pf₂)) ← adversary
  if PartialVec.Conflict a₁ a₂ then
    let ok₁ ← vc.check cm a₁ pf₁
    let ok₂ ← vc.check cm a₂ pf₂
    return ok₁ && ok₂
  else
    return false

/-- The position-binding advantage: the probability that `positionBindingExperiment` accepts,
against the lazily sampled random oracle. -/
noncomputable def positionBindingAdvantage [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : PositionBindingAdversary X Y Msg Cm Pf ℓ) : ENNReal :=
  (ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.positionBindingExperiment adversary) {true}

/-- The position-binding advantage is the probability that `positionBindingExperiment` returns
`true` against the lazily sampled random oracle. -/
theorem positionBindingAdvantage_def [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : PositionBindingAdversary X Y Msg Cm Pf ℓ) :
    vc.positionBindingAdvantage adversary =
      (ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.positionBindingExperiment adversary) {true} := by
  rw [positionBindingAdvantage]

/-- A position-binding adversary `MakesAtMostQueries t` when it makes at most `t` queries to the
oracle on every path. Coins are free. -/
@[expose]
def PositionBindingAdversary.MakesAtMostQueries
    (adversary : PositionBindingAdversary X Y Msg Cm Pf ℓ) (t : ℕ) : Prop :=
  IsQueryBoundP adversary (· matches .inr _) t

end VectorCommitment
