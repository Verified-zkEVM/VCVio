/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import VCVio.OracleComp.ProbComp

/-!
# Bit security

A security game returns a winning bit and a count per query kind. `SecurityGame.advantage` is
the probability that an adversary wins, and `SecurityGame.HasQueryBound` says that the counts of
the kinds in a counting mode `Z`, which select the adversary's work, total at most `q` with
probability one. A bit-security statement bounds the advantage of every adversary of bounded
work by `q / 2^bits`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity

/-- A security game for schemes of type `Scheme`, counting queries of the kinds in `Kind`. -/
structure SecurityGame (Scheme : Type) (Kind : Type) where
  /-- The adversaries of the game. -/
  Adversary : Type
  /-- The winning bit and query counts. -/
  experiment : Scheme → Adversary → ProbComp (Bool × (Kind → ℕ))

namespace SecurityGame

variable {Scheme Kind : Type} (game : SecurityGame Scheme Kind) (scheme : Scheme)

/-- The probability that the adversary wins. -/
noncomputable def advantage (adversary : game.Adversary) : ℝ≥0∞ :=
  Pr{let result ← game.experiment scheme adversary}[result.1 = true]

/-- The total count in mode `Z` is at most `q` with probability one. -/
def HasQueryBound (Z : Finset Kind) (adversary : game.Adversary) (q : ℕ) : Prop :=
  Pr{let result ← game.experiment scheme adversary}[∑ kind ∈ Z, result.2 kind ≤ q] = 1

end SecurityGame

end SlhDsaSecurity
