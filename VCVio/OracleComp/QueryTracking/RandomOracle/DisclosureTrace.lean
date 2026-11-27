/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Undisclosed
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Direct disclosures on the realized graph trace

The protected set can be chosen after observing the run. Its cells must be absent initially,
and every protected node must have a protected child. Under these conditions, a protected
cell can appear before the final fill only if the logged run directly read a protected cell.
-/

public section
open OracleComp OracleSpec

namespace CanonicalGraph

variable {ι X K R α : Type} {pub : OracleSpec ι} (G : CanonicalGraph pub X K R)
  [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- Initially absent cells stay absent before the final fill if each protected node has a protected
child and this execution logs no direct read from the set. -/
theorem stays_undisclosed_on_log (oa : OracleComp (pub.withLabels X K R) α)
    {hidden : Set (X ⊕ K)} (child : ∀ k, .inr k ∈ hidden → ∃ c ∈ G.ch k, c ∈ hidden)
    {s : RelabelState pub X K R × List (X ⊕ K)} (cold : ∀ c ∈ hidden, s.1.2 c = none)
    {z} (run : z ∈ support ((simulateQ G.deferredImpl (simulateQ loggingOracle oa).run).run s))
    (avoid : ∀ entry ∈ z.1.2, AvoidsDirectRead (pub := pub) (R := R) hidden entry.1) :
    ∀ c ∈ hidden, z.2.1.2 c = none := by
  induction oa using OracleComp.inductionOn generalizing s z with
  | pure a =>
    simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst z
    exact cold
  | query_bind t k ih =>
    rw [run_simulateQ_loggingOracle_query_bind] at run
    simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
      mem_support_bind_iff, support_map] at run
    obtain ⟨w, head, tail, suffix, rfl⟩ := run
    have allowed := avoid ⟨t, w.1⟩ List.mem_cons_self
    have absent := G.stays_undisclosed child ((allQueriesSatisfy_query_iff _ _).2 allowed) cold head
    exact ih w.1 absent (z := tail) suffix (fun entry h => avoid entry (List.mem_cons_of_mem _ h))

end CanonicalGraph
