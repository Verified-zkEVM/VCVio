/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Position binding of vector commitments

A position-binding adversary outputs one commitment together with two openings, each a partial
vector of claimed values and a proof. It wins when both openings are accepted and they
conflict: some position is defined in both with different values (Chiesa and Yogev, *Building
Cryptographic Proofs from Hash Functions*, §18.4).

The winning probability is relative to a distribution `D` on oracle functions, as for
completeness (`VectorCommitment.completenessProb`): it is the lower integral over `D` of the
winning probability against each fixed function. For an advantage, undercounting is the unsafe
direction: under a coarse σ-algebra on `X → Y` the lower integral can drop below the true
probability, which makes a bound easier to prove. State security bounds for every σ-algebra, or for
one under which the integrand is measurable, such as the discrete σ-algebra on a countable
function space.

## Main definitions

* `PartialVec.Conflict`: two partial vectors disagree at a position both define.
* `VectorCommitment.PositionBindingAdversary`, `VectorCommitment.positionBindingExperiment` and
  `VectorCommitment.positionBindingAdvantage`.
* `VectorCommitment.PositionBindingAdversary.MakesAtMostQueries`: an oracle-query budget for the
  adversary.
-/

public section

open OracleComp OracleSpec MeasureTheory

universe u uX

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

section Experiment

variable {X : Type uX} {Y : Type} {Msg : Type} {Cm Td Pf : Type} {ℓ : ℕ}

/-- A position-binding adversary outputs a commitment and two claimed openings, each a partial
vector of values with a proof. The openings are outputs of an oracle computation, so `Msg` is in
`Type`. -/
abbrev PositionBindingAdversary (X : Type uX) (Y : Type) (Msg : Type) (Cm Pf : Type)
    (ℓ : ℕ) :=
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

/-- The position-binding advantage with the oracle sampled from `D`: the lower integral over `D`
of the probability that `positionBindingExperiment` accepts against each fixed function. When the
integrand is not measurable, the lower integral may undercount. For an advantage, that makes bounds
easier to prove, so bounds should hold for every σ-algebra on `X → Y` (see the module
docstring). -/
@[expose]
noncomputable def positionBindingAdvantage [MeasurableSpace (X → Y)] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (D : Measure (X → Y))
    (adversary : PositionBindingAdversary X Y Msg Cm Pf ℓ) : ENNReal :=
  ∫⁻ H, Pr{let b ←
    simulateQ (fixedOracleImpl H) (vc.positionBindingExperiment adversary)}[b = true] ∂D

end Experiment

section QueryBound

variable {X : Type} {Y : Type} {Msg : Type} {Cm Pf : Type} {ℓ : ℕ}

/-- A position-binding adversary `MakesAtMostQueries q` when it makes at most `q` queries to the
oracle on every path. Coins are free. The oracle input type is in `Type` here, as `IsQueryBoundP`
requires of the index type. -/
@[expose]
def PositionBindingAdversary.MakesAtMostQueries
    (adversary : PositionBindingAdversary X Y Msg Cm Pf ℓ) (q : ℕ) : Prop :=
  IsQueryBoundP adversary (fun i : ℕ ⊕ X ↦ i.isRight = true) q

end QueryBound

end VectorCommitment
