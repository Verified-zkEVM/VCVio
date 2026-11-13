/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import Mathlib.Data.Fin.Basic

/-!
# Shared-response GXMSS query coordinates

One evaluator domain separates public parameters, parameter-indexed starts and parameter/message/
epoch-indexed retries. The interval construction embeds these coordinates and adds frontier roots.
-/

public section
namespace GXMSS.PRFDerived
variable {Key PP H M R Response : Type} {h v : ℕ}

/-- The three disjoint query families for one shared evaluator key. -/
inductive Query (PP M : Type) (h v : ℕ) where
  /-- The public parameter from the distinguished query. -/
  | publicSeed
  /-- A chain start indexed by the derived parameter, epoch, and chain label. -/
  | start (pp : PP) (epoch : Fin (2 ^ h)) (chain : Fin v)
  /-- A retry randomizer indexed by the parameter, epoch, message, and zero-based attempt. -/
  | retry (pp : PP) (epoch : Fin (2 ^ h)) (message : M) (attempt : ℕ)

/-- A single abstract response domain for the shared keyed evaluator. -/
abbrev Evaluator (Key PP M Response : Type) (h v : ℕ) :=
  Key → Query PP M h v → Response

/-- Interpret the common response domain at each of the three disjoint query families. -/
structure Interpretation (PP H R Response : Type) where
  /-- Interpret the distinguished public-parameter response. -/
  publicParameter : Response → PP
  /-- Interpret a parameter-indexed chain-start response. -/
  chainStart : Response → H
  /-- Interpret a parameter-indexed retry response. -/
  retryRandomizer : Response → R

/-- The distinguished public-parameter query is separate from start queries. -/
theorem publicSeed_ne_start (pp : PP) (epoch : Fin (2 ^ h)) (chain : Fin v) :
    (Query.publicSeed : Query PP M h v) ≠ Query.start pp epoch chain := by
  intro equality
  cases equality

/-- The distinguished public-parameter query is separate from retry queries. -/
theorem publicSeed_ne_retry (pp : PP) (epoch : Fin (2 ^ h)) (message : M)
    (attempt : ℕ) :
    (Query.publicSeed : Query PP M h v) ≠ Query.retry pp epoch message attempt := by
  intro equality
  cases equality

/-- Start and retry queries are disjoint, including at the same public parameter. -/
theorem start_ne_retry (startPP : PP) (startEpoch : Fin (2 ^ h)) (chain : Fin v)
    (retryPP : PP) (retryEpoch : Fin (2 ^ h)) (message : M) (attempt : ℕ) :
    (Query.start startPP startEpoch chain : Query PP M h v) ≠
      Query.retry retryPP retryEpoch message attempt := by
  intro equality
  cases equality

/-- Equality of start queries determines their parameter, epoch, and chain label. -/
theorem start_eq_iff (pp₁ pp₂ : PP) (epoch₁ epoch₂ : Fin (2 ^ h))
    (chain₁ chain₂ : Fin v) :
    (Query.start pp₁ epoch₁ chain₁ : Query PP M h v) = Query.start pp₂ epoch₂ chain₂ ↔
      pp₁ = pp₂ ∧ epoch₁ = epoch₂ ∧ chain₁ = chain₂ := by
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Equality of retry queries determines every field, including the public parameter. -/
theorem retry_eq_iff (pp₁ pp₂ : PP) (epoch₁ epoch₂ : Fin (2 ^ h))
    (message₁ message₂ : M) (attempt₁ attempt₂ : ℕ) :
    (Query.retry pp₁ epoch₁ message₁ attempt₁ : Query PP M h v) =
        Query.retry pp₂ epoch₂ message₂ attempt₂ ↔
      pp₁ = pp₂ ∧ epoch₁ = epoch₂ ∧ message₁ = message₂ ∧ attempt₁ = attempt₂ := by
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- The public parameter derived from the sampled evaluator key. -/
@[expose] def publicSeed (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) : PP :=
  interpretation.publicParameter (evaluate key .publicSeed)

/-- All starts use the derived public parameter in their exact indexed queries. -/
@[expose] def starts (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) (pp : PP) :
    Fin (2 ^ h) → Fin v → H :=
  fun epoch chain => interpretation.chainStart (evaluate key (.start pp epoch chain))

/-- The query equation for a selected chain start. -/
theorem starts_apply (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) (pp : PP)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    starts evaluate interpretation key pp epoch chain =
      interpretation.chainStart (evaluate key (.start pp epoch chain)) := rfl

end GXMSS.PRFDerived
