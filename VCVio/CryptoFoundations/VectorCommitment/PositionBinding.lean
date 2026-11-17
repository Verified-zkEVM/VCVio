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
conflict: some position is defined in both with different values (cf. Chiesa and Yogev,
*Building Cryptographic Proofs from Hash Functions*, Lemma 18.4.1, stated there for Merkle trees).

The advantage is stated in the random oracle model: the experiment runs against the lazily
sampled random oracle `ProbCompRuntime.rom (X →ₒ Y)`, shared by the adversary and `Check`.

## Main definitions

* `PartialVec.Conflict`: two partial vectors disagree at a position both define.
* `VectorCommitment.PositionBindingAdversary`, `VectorCommitment.positionBindingExperiment` and
  `VectorCommitment.positionBindingAdvantage`.
* `VectorCommitment.PositionBindingAdversary.MakesAtMostQueries`: an oracle-query budget for the
  adversary.
-/

public section

open OracleComp OracleSpec MeasureTheory

universe u

namespace PartialVec

variable {ℓ : ℕ} {Msg : Type u}

/-- Two partial vectors conflict when some position is defined in both with different values. -/
@[expose]
def Conflict (a b : PartialVec ℓ Msg) : Prop :=
  ∃ q x y, a q = some x ∧ b q = some y ∧ x ≠ y

/-- Conflict is decidable: it is a finite disjunction. -/
instance [DecidableEq Msg] (a b : PartialVec ℓ Msg) : Decidable (Conflict a b) :=
  decidable_of_iff (∃ q, ∃ x ∈ a q, ∃ y ∈ b q, x ≠ y) (by simp [Conflict])

/-- A partial vector never conflicts with itself. -/
theorem not_conflict_self (a : PartialVec ℓ Msg) : ¬ Conflict a a := by
  rintro ⟨q, x, y, hx, hy, hxy⟩
  exact hxy (Option.some_injective _ (hx.symm.trans hy))

end PartialVec

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
@[expose]
noncomputable def positionBindingAdvantage [DecidableEq X] [SampleableType Y] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : PositionBindingAdversary X Y Msg Cm Pf ℓ) : ENNReal :=
  (ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.positionBindingExperiment adversary) {true}

/-- A position-binding adversary `MakesAtMostQueries q` when it makes at most `q` queries to the
oracle on every path. Coins are free. -/
@[expose]
def PositionBindingAdversary.MakesAtMostQueries
    (adversary : PositionBindingAdversary X Y Msg Cm Pf ℓ) (q : ℕ) : Prop :=
  IsQueryBoundP adversary (· matches .inr _) q

end VectorCommitment
