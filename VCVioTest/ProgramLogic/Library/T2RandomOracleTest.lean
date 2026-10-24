/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.SimulateQ
public import VCVio.ProgramLogic.Library.T2.RandomOracle

/-!
# Tests for the random oracle specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T2.RandomOracle` and the structural
`simulateQ` rules of `VCVio.ProgramLogic.Library.T1.SimulateQ`: consistency of repeated queries
with probability one, fresh-point probabilities, and frames of random-oracle-model runs.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T2RandomOracle

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP ENNReal

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- Lazy sampling is consistent: two queries at the same point agree with probability one. -/
example (t : spec.Domain) (c₀ : spec.QueryCache) :
    Pr{let z ← (do let a ← spec.randomOracle t; let b ← spec.randomOracle t; return (a, b) :
        StateT spec.QueryCache ProbComp _).run c₀}[z.1.1 = z.1.2] = 1 := by
  refine (prEvent_run_eq_one_iff_triple _ c₀
    (fun (x : spec.Range t × spec.Range t) _ => x.1 = x.2)).2 ?_
  vcgen
  grind

/-- The same consistency for a simulated program. -/
example (t : spec.Domain) :
    ⦃ fun _ => True ⦄
      (simulateQ spec.randomOracle (do
        let a ← (spec.query t : OracleComp spec _)
        let b ← (spec.query t : OracleComp spec _)
        return (a, b)))
    ⦃ fun p _ => p.1 = p.2 ⦄ := by
  vcgen
  grind

/-- A fresh point is answered uniformly. -/
example [∀ t, Fintype (spec.Range t)] (t : spec.Domain) (u : spec.Range t) :
    Pr{let v ← (spec.randomOracle t).run' ∅}[v = u] = (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ :=
  randomOracle.prEvent_run'_eq_of_eq_none rfl u

/-- Repeated queries collapse to one before any probability is computed. -/
example (t : spec.Domain) (c : spec.QueryCache) :
    (simulateQ spec.randomOracle ((spec.query t : OracleComp spec _) >>= fun a =>
        (spec.query t : OracleComp spec _) >>= fun b => pure (a, b))).run' c =
      (simulateQ spec.randomOracle ((spec.query t : OracleComp spec _) >>= fun a =>
        pure (a, a))).run' c := by
  rw [QueryImpl.simulateQ_withCaching_query_bind_query_self]

/-- For any program, a random-oracle run only grows the cache. -/
example {α : Type} (oa : OracleComp spec α) (c₀ : spec.QueryCache) :
    ⦃ fun c => c₀ ≤ c ∧ True ⦄ (simulateQ spec.randomOracle oa) ⦃ fun _ c => c₀ ≤ c ⦄ := by
  vcgen
  grind

variable {hashSpec : OracleSpec.{0, 0} ι} [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]

/-- In the random oracle model, two hash queries at the same point agree, around a uniform draw.
The sum handler dispatches each query to its summand. -/
example (t : hashSpec.Domain) (n : ℕ) :
    ⦃ fun _ => True ⦄
      (do
        let a ← hashSpec.romImpl (.inr t)
        let _ ← hashSpec.romImpl (.inl n)
        let b ← hashSpec.romImpl (.inr t)
        return (a, b))
    ⦃ fun p _ => p.1 = p.2 ⦄ := by
  vcgen
  grind

/-- An opaque random-oracle-model adversary followed by a hash query: the answer is cached, and
any cache entry from before the adversary survives. -/
example {α : Type} (adv : OracleComp (unifSpec + hashSpec) α) (t t' : hashSpec.Domain)
    (u : hashSpec.Range t') :
    ⦃ fun c => c t' = some u ⦄
      (do let _ ← simulateQ hashSpec.romImpl adv; hashSpec.romImpl (.inr t))
    ⦃ fun v c => c t = some v ∧ c t' = some u ⦄ := by
  vcgen
  rename_i h₀ _ _ h₁ _ _ h₂ h₃
  exact ⟨h₃, h₂ (h₁ h₀)⟩

end VCVioTest.ProgramLogic.Library.T2RandomOracle
