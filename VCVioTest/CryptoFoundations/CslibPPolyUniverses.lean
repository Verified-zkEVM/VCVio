/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVioCslib.NonuniformPPoly

/-!
# Higher-universe canaries for the optional cslib P/poly facade

Lean can silently specialize an exported declaration to `Type 0` when its
universe is omitted. These examples keep the security-game facade usable by
ordinary oracle families whose query and answer types live above `Type 0`.
-/

public section

universe u

open OracleSpec ENNReal OracleComp.Complexity

namespace VCVioTest.CslibPPolyUniverses

variable {index input output : ℕ → Type (u + 1)}
  [∀ n, DecidableEq (index n)]
  {spec : (n : ℕ) → OracleSpec.{u + 1, u + 1} (index n)}

example (boundary : NonuniformBoundary spec input output)
    (game : SecurityGame ((n : ℕ) → input n → OracleComp (spec n) (output n))) : Prop :=
  game.secureAgainstNonuniformPPT boundary

example (boundary : NonuniformBoundary spec input output)
    (game : SecurityGame ((n : ℕ) → input n → OracleComp (spec n) (output n)))
    {error : ℕ → ℝ≥0∞} (errorNegligible : negligible error)
    (advantageBound :
      ∀ (adversary : (n : ℕ) → input n → OracleComp (spec n) (output n))
        (queries : ℕ → ℕ),
        (∀ n value, OracleComp.IsTotalQueryBound (adversary n value) (queries n)) →
        ∀ n, game.advantage adversary n ≤ (queries n : ℝ≥0∞) * error n) :
    game.secureAgainstNonuniformPPT boundary :=
  SecurityGame.secureAgainstNonuniformPPT_of_advantage_le_mul_totalQueries
    boundary game errorNegligible advantageBound

end VCVioTest.CslibPPolyUniverses
