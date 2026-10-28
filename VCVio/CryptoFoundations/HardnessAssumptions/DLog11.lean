/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Module.Basic

/-! # The (1,1)-discrete logarithm problem

The problem of Bauer, Fuchsbauer and Loss supplies one common scalar multiple in each
of two source groups. The solver returns the scalar, rather than another group element.
-/

public section

open OracleComp OracleSpec

namespace DLog11

/-- A solver receiving the first generator and challenge, then the second generator and
challenge, and returning a scalar guess. -/
abbrev Adversary (F G₁ G₂ : Type) := G₁ → G₁ → G₂ → G₂ → ProbComp F

/-- Sample a uniform scalar, reveal its multiples in both source groups, and accept exactly
when the solver recovers it. -/
@[expose] def experiment {F G₁ G₂ : Type} [SampleableType F] [DecidableEq F]
    [SMul F G₁] [SMul F G₂] (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F G₁ G₂) : ProbComp Bool := do
  let α ← $ᵗ F
  let guess ← A g₁ (α • g₁) g₂ (α • g₂)
  return decide (guess = α)

end DLog11
