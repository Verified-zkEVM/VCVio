/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.WeightedCap

/-!
# Resources on every path of a capped caller

If a query increases the resource by at most its fee, the final resource is at most its
initial value plus the budget. The cap deducts the full fee even when the resource grows
by less. The bound also holds on refusal.
-/

public section
open OracleSpec
namespace OracleComp.WeightedCap

variable {ι S α : Type} {spec : OracleSpec ι}
variable (impl : QueryImpl spec (StateT S ProbComp)) (fee : ι → Nat) (resource : S → ℕ∞)
variable (grow : ∀ t s w, w ∈ support ((impl t).run s) →
  resource w.2 ≤ resource s + fee t)

include grow in
/-- The ordinary fee bounds resource growth for all final states, including an outer stop. -/
theorem resource_le (p : OracleComp spec α) (q : Nat) (s : S) {w}
    (hw : w ∈ support ((simulateQ impl (capCompOpt fee q p)).run s)) :
    resource w.2 ≤ resource s + q := by
  induction p using OracleComp.inductionOn generalizing s q with
  | pure x =>
    simp only [capCompOpt_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hw
    subst w
    exact le_self_add
  | query_bind t next ih =>
    rw [capCompOpt_query_bind] at hw
    split_ifs at hw with affordable
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hw
      obtain ⟨y, hy, tail⟩ := hw
      refine (ih y.1 (q - fee t) y.2 tail).trans ?_
      calc
        _ ≤ (resource s + (fee t : ℕ∞)) + ((q - fee t : Nat) : ℕ∞) :=
          add_le_add (grow t s y hy) le_rfl
        _ = _ := by rw [add_assoc, ← Nat.cast_add, Nat.add_sub_of_le affordable]
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hw
      subst w
      exact le_self_add

end OracleComp.WeightedCap
