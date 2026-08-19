/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.MultiRoundOp
public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Coordinate-wise forking — program logic bridge

Wraps the coordinate-wise forking bounds as quantitative Hoare triples, matching what
`VCVio/ProgramLogic/SeededFork.lean` does for the seeded fork.

`triple_coordForkOp` carries the single-round bound of Figure 11 of Fenzi–Moghaddas–Nguyen and
`triple_multiForkOp` its `μ`-round recursion. Both are the success bound only; the loop's lookup
count is data it returns, not part of the postcondition.
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.EvalDist CoordinateWise ENNReal

namespace OracleComp.ProgramLogic

variable {ι S : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [Nonempty S]
variable [SampleableType (ι → S)]

/-- The single-round coordinate fork as a quantitative Hoare triple: against a fixed acceptance
table, the resampling loop succeeds with weight at least `ε - ℓ(k-1)/N`. -/
theorem triple_coordForkOp (k : ℕ) (ρ : (ι → S) → Bool) :
    Triple
      (((Finset.univ.filter fun c : ι → S => ρ c).card : ℝ≥0∞) / Fintype.card (ι → S)
        - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S)
      (coordForkOp k ρ)
      (fun r => if r.1.isSome then 1 else 0) :=
  triple_ofLE <| le_trans (sub_div_le_probEvent_isSome_coordForkOp k ρ)
    (triple_toLE (triple_probEvent_indicator (coordForkOp k ρ) fun r => r.1.isSome))

/-- The `μ`-round recursion as a quantitative Hoare triple, losing `μ` copies of the per-round
`ℓ(k-1)/N`. -/
theorem triple_multiForkOp (μ k : ℕ) (ρ : Transcript ι S μ → Bool) :
    Triple
      (avgTranscript (fun t => if ρ t then 1 else 0) - μ * roundLoss ι S k)
      (multiForkOp μ k ρ)
      (fun r => if r.1.isSome then 1 else 0) :=
  triple_ofLE <| le_trans (sub_le_probEvent_isSome_multiForkOp μ k ρ)
    (triple_toLE (triple_probEvent_indicator (multiForkOp μ k ρ) fun r => r.1.isSome))

end OracleComp.ProgramLogic
