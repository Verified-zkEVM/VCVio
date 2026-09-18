/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Combining query budgets from an interface partition

Separate bounds for two complementary classes of operations give a total bound for the same
adaptive program. This turns local tag and reader budgets into a finite runtime schedule.
-/

public section

namespace OracleComp

variable {ι α : Type} {spec : OracleSpec ι}

/-- Complementary query classes cover every operation, so their budgets add to a total bound. -/
theorem isTotalQueryBound_of_partition (program : OracleComp spec α)
    (p q : ι → Prop) [DecidablePred p] [DecidablePred q]
    (hpartition : ∀ a, q a ↔ ¬ p a) (left right : ℕ)
    (hleft : IsQueryBoundP program p left) (hright : IsQueryBoundP program q right) :
    IsTotalQueryBound program (left + right) := by
  induction program using OracleComp.inductionOn generalizing left right with
  | pure value => trivial
  | query_bind a next ih =>
      rw [isQueryBoundP_query_bind_iff] at hleft hright
      rw [isTotalQueryBound_query_bind_iff]
      by_cases hp : p a
      · have hq : ¬ q a := fun h => (hpartition a).1 h hp
        have hl : 0 < left := hleft.1.resolve_left (not_not_intro hp)
        refine ⟨by omega, fun answer => ?_⟩
        have h := ih answer (left - 1) right
          (by simpa [hp] using hleft.2 answer) (by simpa [hq] using hright.2 answer)
        convert h using 1
        omega
      · have hq : q a := (hpartition a).2 hp
        have hr : 0 < right := hright.1.resolve_left (not_not_intro hq)
        refine ⟨by omega, fun answer => ?_⟩
        have h := ih answer left (right - 1)
          (by simpa [hp] using hleft.2 answer) (by simpa [hq] using hright.2 answer)
        convert h using 1
        omega

end OracleComp
