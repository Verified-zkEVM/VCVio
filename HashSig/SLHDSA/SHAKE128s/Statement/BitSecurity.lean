/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import VCVio.OracleComp.ProbComp

/-!
# Bit security

A game returns a winning bit and a count per query kind; a counting mode `Z` selects which
counts are work. `bits` bits of security: every adversary whose work is at most `q ≥ 1` with
probability one wins with probability at most `q / 2^bits`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace Xmss

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

/-- Every adversary with budget `q ≥ 1` wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (Z : Finset Kind) (bits : ℕ) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, game.HasQueryBound scheme Z adversary q →
    game.advantage scheme adversary ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞)

/-- Security at `bits`, but not at `bits + 1`. -/
def HasExactClassicalSecurityBits (Z : Finset Kind) (bits : ℕ) : Prop :=
  game.HasClassicalSecurityBits scheme Z bits ∧
    ¬ game.HasClassicalSecurityBits scheme Z (bits + 1)

end SecurityGame

end Xmss
