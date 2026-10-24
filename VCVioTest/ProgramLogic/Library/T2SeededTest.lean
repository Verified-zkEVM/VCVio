/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.SimulateQ
public import VCVio.ProgramLogic.Library.T2.Seeded

/-!
# Tests for the seeded handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T2.Seeded`: answers drawn from a known
seed, fall-through on an exhausted seed, seed consumption by an opaque program, and erasure from the
empty seed.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T2Seeded

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}

/-- Two queries at a seeded input return the two seeded answers, in order, and exhaust it. -/
example (t : spec.Domain) (u₁ u₂ : spec.Range t) (s₀ : QuerySeed spec) (h : s₀ t = [u₁, u₂]) :
    ⦃ fun s => s = s₀ ⦄
      (do let a ← spec.seededOracle t; let b ← spec.seededOracle t; return (a, b) :
        StateT (QuerySeed spec) (OracleComp spec) _)
    ⦃ fun p s => p = (u₁, u₂) ∧ s t = [] ⦄ := by
  vcgen
  simp_all

/-- Queries at exhausted inputs fall through and keep the seed. -/
example (t₁ t₂ : spec.Domain) (s₀ : QuerySeed spec) (h₁ : s₀ t₁ = []) (h₂ : s₀ t₂ = []) :
    ⦃ fun s => s = s₀ ⦄
      (do let _ ← spec.seededOracle t₁; spec.seededOracle t₂ :
        StateT (QuerySeed spec) (OracleComp spec) _)
    ⦃ fun _ s => s = s₀ ⦄ := by
  vcgen
  grind

/-- A simulated program reads a seeded answer through the structural `simulateQ` rules. -/
example (t : spec.Domain) (u : spec.Range t) (s₀ : QuerySeed spec) (h : s₀ t = [u]) :
    ⦃ fun s => s = s₀ ⦄
      (simulateQ spec.seededOracle (spec.query t : OracleComp spec _))
    ⦃ fun v _ => v = u ⦄ := by
  vcgen
  simp_all

/-- For any program, every final seed list is a suffix of the initial one. -/
example {α : Type} (oa : OracleComp spec α) (s₀ : QuerySeed spec) (i : ι) :
    ⦃ fun s => s = s₀ ⦄ (simulateQ spec.seededOracle oa) ⦃ fun _ s => s i <:+ s₀ i ⦄ := by
  vcgen
  grind

/-- An opaque program followed by a query: a seed exhausted before stays exhausted, so the query
falls through. -/
example {α : Type} (oa : OracleComp spec α) (t : spec.Domain) :
    ⦃ fun s => s t = [] ∧ True ⦄
      (do let _ ← simulateQ spec.seededOracle oa; spec.seededOracle t :
        StateT (QuerySeed spec) (OracleComp spec) _)
    ⦃ fun _ s => s t = [] ⦄ := by
  vcgen
  rename_i h₀ _ _ _ hsuf _ _ hnil _
  have := hsuf t
  simp_all

/-- From the empty seed, a seeded run is the program itself. -/
example {α : Type} (oa : OracleComp spec α) : (simulateQ spec.seededOracle oa).run' ∅ = oa :=
  seededOracle.run'_simulateQ_empty oa

variable [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- The eager random oracle answers from its seed first. -/
example (t : spec.Domain) (u : spec.Range t) (s₀ : QuerySeed spec) (h : s₀ t = [u]) :
    ⦃ fun s => s = s₀ ⦄
      (do let a ← eagerRandomOracle t; let b ← eagerRandomOracle t; return (a, b) :
        StateT (QuerySeed spec) ProbComp _)
    ⦃ fun p s => p.1 = u ∧ s = s₀.update t [] ⦄ := by
  vcgen
  simp_all

/-- From the empty seed, the eager random oracle is uniform sampling. -/
example {α : Type} (oa : OracleComp spec α) :
    (simulateQ (eagerRandomOracle (spec := spec)) oa).run' ∅ = simulateQ uniformSampleImpl oa :=
  eagerRandomOracle.run'_simulateQ_empty oa

end VCVioTest.ProgramLogic.Library.T2Seeded
