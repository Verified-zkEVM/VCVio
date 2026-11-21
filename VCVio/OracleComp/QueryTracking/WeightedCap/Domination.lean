/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.WeightedCap
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Relaxing a cutoff with a persistent bad event

A caller may be stopped at two different points under two tariffs.
A returned result is compared as usual.
After an early refusal only the bad event in the current state can contribute.
If it already holds, it still holds at every later endpoint.
-/

public section
namespace OracleComp.WeightedCap

open OracleSpec
open scoped ENNReal
variable {ι α S : Type} {spec : OracleSpec ι}

/-- Decreasing every query charge and increasing the remaining limit can only increase the
probability of a returned event or a persistent bad state.
Refused branches may contribute the bad event under either cutoff. -/
theorem prEvent_cap_le_cap_of_preserves (impl : QueryImpl spec (StateT S ProbComp))
    (tight loose : ι → Nat) (cheaper : ∀ i, loose i ≤ tight i)
    (bad : S → Prop) (preserves : impl.PreservesInv bad) (win : α → S → Prop)
    (body : OracleComp spec α) (n m : Nat) (more : n ≤ m) (initial : S) :
    let event (z : Option α × S) := z.1.elim False (fun a => win a z.2) ∨ bad z.2
    Pr{let z ← (simulateQ impl (capCompOpt tight n body)).run initial}[event z] ≤
      Pr{let z ← (simulateQ impl (capCompOpt loose m body)).run initial}[event z] := by
  classical
  intro event
  induction body using OracleComp.inductionOn generalizing n m initial with
  | pure a =>
    simp [capCompOpt_pure]
  | query_bind t next ih =>
    rw [capCompOpt_query_bind]
    split_ifs with pay
    · have free : loose t ≤ m := (cheaper t).trans (pay.trans more)
      rw [capCompOpt_query_bind, ite_eq_left free]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z =>
        ih z.1 (n - tight t) (m - loose t) (by have := cheaper t; omega) z.2
    · by_cases failed : bad initial
      · have sure : Pr{let z ← (simulateQ impl (capCompOpt loose m
            (liftM (spec.query t) >>= next))).run initial}[event z] = 1 :=
          (prEvent_eq_one_iff _ _).2 fun z hz => Or.inr
            (simulateQ_run_preservesInv impl bad preserves _ initial failed z hz)
        rw [sure]
        exact prEvent_le_one _
      · simp [simulateQ_pure, StateT.run_pure, event, failed]

end OracleComp.WeightedCap
