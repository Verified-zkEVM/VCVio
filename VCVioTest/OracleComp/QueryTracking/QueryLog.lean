/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module
public import VCVio.OracleComp.QueryTracking.QueryLog

/-!
# Lookup and routing of concrete dependent query logs

Repeated queries retain their first answer, and removing interleaved private queries preserves
the order and answers of both public oracle slots.
-/

open OracleSpec

public section

namespace VCVioTest.QueryLog

/-- The answer type distinguishes numeric and Boolean queries. -/
abbrev replies : OracleSpec Bool
  | false => ℕ
  | true => Bool

/-- Lookup respects dependent answer types and returns the first of repeated queries. -/
theorem lookup_first_repeated :
    let log : QueryLog replies := [⟨false, (7 : ℕ)⟩, ⟨true, true⟩, ⟨false, (9 : ℕ)⟩]
    log.lookup? false = some (7 : ℕ) ∧ log.lookup? true = some true := by
  decide

/-- Removing private samples from an interleaved log keeps both public slots, their order,
and repeated queries with different answers. -/
theorem erase_private_interleaved :
    let log : QueryLog ((replies + coinSpec) + replies) :=
      [⟨.inl (.inl false), (7 : ℕ)⟩, ⟨.inl (.inr ()), true⟩,
       ⟨.inr true, false⟩, ⟨.inl (.inl false), (9 : ℕ)⟩]
    log.eraseMiddle =
      ([⟨.inl false, (7 : ℕ)⟩, ⟨.inr true, false⟩, ⟨.inl false, (9 : ℕ)⟩] :
        QueryLog (replies + replies)) := by
  rfl

end VCVioTest.QueryLog
