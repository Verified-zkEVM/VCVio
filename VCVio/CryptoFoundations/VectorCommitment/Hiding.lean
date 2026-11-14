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
# Hiding of vector commitments

Two-message hiding of commitment and opening. A hiding adversary chooses two messages and a set
`Q` of positions on which they agree, receives the commitment to one of them and the opening proof
for `Q`, and outputs a bit. Its advantage is the difference between the probabilities that it
outputs `true` in the two worlds. Chiesa and Yogev (*Building Cryptographic Proofs from Hash
Functions*, §18.6, Lemma 18.6.3) state hiding with a simulator, for each opening size `q` fixed in
advance, with error `ζ(q)`. The fixed-size form of this game follows with error `2 ζ(q)`; this
adaptive-size form follows with error `2 Σ_q ζ(q)`, summed over the `ℓ + 1` possible sizes.

The adversary chooses `Q`, including its size, after seeing its own oracle answers and before the
commitment. A notion with the size of `Q` fixed in advance is weaker and follows by restricting
the adversary.

Probabilities are relative to a distribution `D` on oracle functions, as for completeness
(`VectorCommitment.completenessProb`): each is the lower integral over `D` of the probability
against each fixed function. For an advantage, undercounting is the unsafe direction: under a
coarse σ-algebra on `X → Y` the lower integral can drop below the true probability, which makes a
bound easier to prove. State security bounds for every σ-algebra, or for one under which the
integrand is measurable, such as the discrete σ-algebra on a countable function space.

## Main definitions

* `VectorCommitment.HidingAdversary`, `VectorCommitment.hidingExperiment` and
  `VectorCommitment.hidingAdvantage`.
* `VectorCommitment.HidingAdversary.MakesAtMostQueries`: one oracle-query budget shared by both
  stages of the adversary.
-/

public section

open OracleComp OracleSpec MeasureTheory

universe uX

namespace VectorCommitment

section Experiment

variable {X : Type uX} {Y : Type} {Msg : Type} {Cm Td Pf : Type} {ℓ : ℕ}

/-- A two-stage hiding adversary. `choose` returns two messages, a set of positions to open and a
state; `distinguish` sees the state, the commitment and the opening proof, and outputs a bit. The
messages are outputs of an oracle computation, so `Msg` is in `Type`. -/
structure HidingAdversary (X : Type uX) (Y : Type) (Msg : Type) (Cm Pf : Type) (ℓ : ℕ) where
  /-- State carried from the first stage to the second. -/
  State : Type
  /-- Choose the two messages, the positions to open and a state. -/
  choose : OracleComp (unifSpec + (X →ₒ Y))
    ((Fin ℓ → Msg) × (Fin ℓ → Msg) × Finset (Fin ℓ) × State)
  /-- Guess the world from the state, the commitment and the opening proof. -/
  distinguish : State → Cm → Pf → OracleComp (unifSpec + (X →ₒ Y)) Bool

/-- The hiding experiment in world `b`: commit to the second message when `b` is `true` and to the
first otherwise, open the chosen positions, and return the adversary's bit. Messages that differ
on the chosen positions make both worlds return `false`, so they give no advantage. -/
@[expose]
def hidingExperiment [DecidableEq Msg] (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (adversary : HidingAdversary X Y Msg Cm Pf ℓ) (b : Bool) :
    OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let (m₀, m₁, Q, st) ← adversary.choose
  if PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q then
    let (cm, td) ← vc.commit (if b then m₁ else m₀)
    let pf ← liftComp (vc.opening Q td) (unifSpec + (X →ₒ Y))
    adversary.distinguish st cm pf
  else
    return false

/-- The hiding advantage with the oracle sampled from `D`: the distance between the lower
integrals over `D` of the probabilities that `hidingExperiment` returns `true` in the two worlds.
When the integrand is not measurable, the lower integral may undercount. For an advantage, that
makes bounds easier to prove, so bounds should hold for every σ-algebra on `X → Y` (see the module
docstring). -/
@[expose]
noncomputable def hidingAdvantage [MeasurableSpace (X → Y)] [DecidableEq Msg]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (D : Measure (X → Y))
    (adversary : HidingAdversary X Y Msg Cm Pf ℓ) : ENNReal :=
  ENNReal.absDiff
    (∫⁻ H, Pr{let r ←
      simulateQ (fixedOracleImpl H) (vc.hidingExperiment adversary true)}[r = true] ∂D)
    (∫⁻ H, Pr{let r ←
      simulateQ (fixedOracleImpl H) (vc.hidingExperiment adversary false)}[r = true] ∂D)

end Experiment

section QueryBound

variable {X : Type} {Y : Type} {Msg : Type} {Cm Pf : Type} {ℓ : ℕ}

/-- A hiding adversary `MakesAtMostQueries q` when, for every commitment and proof, running both
stages makes at most `q` queries to the oracle on every path. Coins are free. The oracle input
type is in `Type` here, as `IsQueryBoundP` requires of the index type. -/
@[expose]
def HidingAdversary.MakesAtMostQueries (adversary : HidingAdversary X Y Msg Cm Pf ℓ) (q : ℕ) :
    Prop :=
  ∀ (cm : Cm) (pf : Pf),
    IsQueryBoundP
      (do
        let (_, _, _, st) ← adversary.choose
        adversary.distinguish st cm pf)
      (fun i : ℕ ⊕ X ↦ i.isRight = true) q

end QueryBound

end VectorCommitment
