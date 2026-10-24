/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.SimulateQ
public import VCVio.ProgramLogic.Library.T2.Counting
public import VCVio.ProgramLogic.Library.T2.Logging

/-!
# Tests for the counting and cost handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T2.Counting`: exact counts of query
sequences, costs in a submonoid, per-index bounds of opaque programs, and a counted and a logged
run of the same bounded program.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T2Counting

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary WriterT.MonoidWP

set_option experimental.vcgen true

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}

/-- Two counted queries add one at each index, in order. -/
example (t₁ t₂ : spec.Domain) :
    ⦃ fun qc => Multiplicative.toAdd qc = 0 ⦄
      (do let _ ← spec.countingOracle t₁; spec.countingOracle t₂ :
        AddWriterT (QueryCount ι) (OracleComp spec) _)
    ⦃ fun _ qc => Multiplicative.toAdd qc = QueryCount.single t₁ + QueryCount.single t₂ ⦄ := by
  vcgen
  simp_all

/-- A simulated program is costed through the structural `simulateQ` rules. -/
example (costFn : spec.Domain → ℕ) (t₁ t₂ : spec.Domain) :
    ⦃ fun c => c = 1 ⦄
      (simulateQ (costOracle (fun t => Multiplicative.ofAdd (costFn t)))
        (do let _ ← (spec.query t₁ : OracleComp spec _); (spec.query t₂ : OracleComp spec _)))
    ⦃ fun _ c => Multiplicative.toAdd c = costFn t₁ + costFn t₂ ⦄ := by
  vcgen
  simp_all

/-- For any program and handler, costs in a submonoid give a total cost in the submonoid. -/
example {α : Type} (so : QueryImpl spec (OracleComp spec)) (oa : OracleComp spec α)
    (costFn : spec.Domain → ℕ) (S : Submonoid (Multiplicative ℕ))
    (hS : ∀ t, Multiplicative.ofAdd (costFn t) ∈ S) :
    ⦃ fun c => c = 1 ⦄
      (simulateQ (so.withCost fun t => Multiplicative.ofAdd (costFn t)) oa)
    ⦃ fun _ c => c ∈ S ⦄ := by
  vcgen [QueryImpl.simulateQ_withCost_wp_of_mem so _ S hS oa]
  simp_all

/-- A per-index bound of an opaque program bounds the count of its counted run, and a final
query adds one. -/
example {α : Type} (oa : OracleComp spec α) (qb : ι → ℕ) (h : IsPerIndexQueryBound oa qb)
    (t : spec.Domain) :
    ⦃ fun qc => qc = 1 ⦄
      (do let _ ← simulateQ spec.countingOracle oa; spec.countingOracle t :
        AddWriterT (QueryCount ι) (OracleComp spec) _)
    ⦃ fun _ qc => Multiplicative.toAdd qc ≤ qb + QueryCount.single t ⦄ := by
  vcgen [simulateQ_countingOracle_wp_of_isPerIndexQueryBound h]
  simp_all

/-- Counting and logging the same bounded program: every index is counted at most its budget
times, and the log holds at most that many entries at each index. -/
example [Fintype ι] {α : Type} (oa : OracleComp spec α) (qb : ι → ℕ)
    (h : IsPerIndexQueryBound oa qb) (i : ι) :
    (∀ z ∈ support (simulateQ spec.countingOracle oa).run, Multiplicative.toAdd z.2 i ≤ qb i) ∧
      ∀ z ∈ support (simulateQ spec.loggingOracle oa).run, z.2.countQ (· = i) ≤ qb i :=
  ⟨fun _ hz => toAdd_le_of_mem_support_run_simulateQ_countingOracle h hz i,
    fun _ hz => by
      simpa [Finset.filter_eq'] using countQ_le_of_mem_support_run_simulateQ
        (IsPerIndexQueryBound.isQueryBoundP (p := (· = i)) h) hz⟩

end VCVioTest.ProgramLogic.Library.T2Counting
