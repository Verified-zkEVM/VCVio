/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Structural Reservation of a Future Query Budget

Stopping-time proofs sometimes need a proof-only continuation that reserves an exact number of
future syntax steps, even when the executable continuation depends on a log maintained by an
interpreter. `reserveQueries` repeats one fixed query and discards every answer. It is never used as
executable protocol code; its exact query-bound characterization lets an outer phase induction
recover that the residual counter still contains the reserved future budget.
-/

@[expose] public section

open OracleSpec

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι}

/-- Make exactly `count` syntactic queries at one fixed oracle index, discarding all responses. -/
def reserveQueries (query : spec.Domain) : ℕ → OracleComp spec Unit
  | 0 => pure ()
  | count + 1 => do
      let _ ← (liftM (spec.query query) : OracleComp spec _)
      reserveQueries query count

/-- Exact structural query-bound characterization for `reserveQueries`. -/
theorem reserveQueries_isTotalQueryBound_iff
    (query : spec.Domain) [Inhabited (spec.Range query)] (count budget : ℕ) :
    IsTotalQueryBound (reserveQueries query count) budget ↔ count ≤ budget := by
  induction count generalizing budget with
  | zero => simp only [Nat.zero_le]; exact ⟨fun _ => trivial, fun _ => trivial⟩
  | succ count ih =>
      simp only [reserveQueries, isTotalQueryBound_query_bind_iff]
      constructor
      · rintro ⟨hbudget, hrest⟩
        have htail := (ih (budget - 1)).mp (hrest (default : spec.Range query))
        omega
      · intro hcount
        refine ⟨by omega, fun _ => (ih (budget - 1)).mpr (by omega)⟩

/-- The canonical reservation satisfies its exact budget. -/
theorem reserveQueries_isTotalQueryBound
    (query : spec.Domain) [Inhabited (spec.Range query)] (count : ℕ) :
    IsTotalQueryBound (reserveQueries query count) count :=
  (reserveQueries_isTotalQueryBound_iff query count count).2 le_rfl

/-- Support-aware bind rule. Under uniform oracle semantics every syntactically reachable
continuation value lies in `support oa`, so it suffices to bound the continuation on that support
rather than on every value of its result type. -/
theorem isTotalQueryBound_bind_of_mem_support
    [IsUniformSpec spec]
    {α β : Type} (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (prefixBound suffixBound : ℕ)
    (hprefix : IsTotalQueryBound oa prefixBound)
    (hsuffix : ∀ x ∈ support oa, IsTotalQueryBound (ob x) suffixBound) :
    IsTotalQueryBound (oa >>= ob) (prefixBound + suffixBound) := by
  induction oa using OracleComp.inductionOn generalizing prefixBound with
  | pure x =>
      simpa using (hsuffix x (by simp)).mono (by omega : suffixBound ≤ prefixBound + suffixBound)
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at hprefix
      rw [bind_assoc, isTotalQueryBound_query_bind_iff]
      refine ⟨by omega, fun response => ?_⟩
      apply (ih response (prefixBound - 1) (hprefix.2 response) ?_).mono
      · omega
      · intro x hx
        apply hsuffix x
        rw [mem_support_bind_iff]
        exact ⟨response, by simp, hx⟩

end OracleComp
