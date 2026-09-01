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

end OracleComp
