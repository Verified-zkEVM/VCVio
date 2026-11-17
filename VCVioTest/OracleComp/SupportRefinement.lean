/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Stateful support refinement and resource bounds

A support refinement preserves replies and a shared cache.
The second run may cost more.
A bound on every second-run endpoint then bounds every first-run endpoint.
The adaptive client uses different reply types at its two query labels.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.OracleComp.SupportRefinement

/-- Full-run bounds transfer to a cheaper handler when replies and the whole cache agree. -/
theorem bound_of_support_refinement
    {ι ιCheap ιFull Cache α : Type} {front : OracleSpec.{0, 0} ι}
    {cheapSpec : OracleSpec.{0, 0} ιCheap} {fullSpec : OracleSpec.{0, 0} ιFull}
    (cheap : QueryImpl front (StateT (Cache × Nat) (OracleComp cheapSpec)))
    (full : QueryImpl front (StateT (Cache × Nat) (OracleComp fullSpec)))
    (hstep : ∀ (t : front.Domain) (sCheap sFull : Cache × Nat),
      sCheap.1 = sFull.1 ∧ sCheap.2 ≤ sFull.2 →
      ∀ (reply : front.Range t) (sCheap' : Cache × Nat),
        (reply, sCheap') ∈ support ((cheap t).run sCheap) →
        ∃ sFull', (reply, sFull') ∈ support ((full t).run sFull) ∧
          sCheap'.1 = sFull'.1 ∧ sCheap'.2 ≤ sFull'.2)
    (body : OracleComp front α) (initial : Cache × Nat) (budget : Nat)
    (hbound : ∀ reply final, (reply, final) ∈ support ((simulateQ full body).run initial) →
      final.2 ≤ budget)
    (reply : α) (final : Cache × Nat)
    (hcheap : (reply, final) ∈ support ((simulateQ cheap body).run initial)) :
    final.2 ≤ budget := by
  obtain ⟨fullFinal, hfull, _, hcost⟩ := simulateQ_run_support_refinement cheap full
    (fun sCheap sFull => sCheap.1 = sFull.1 ∧ sCheap.2 ≤ sFull.2)
    hstep body initial initial ⟨rfl, le_rfl⟩ reply final hcheap
  exact hcost.trans (hbound reply fullFinal hfull)

/-- An infinite dependent reply family: the first query returns an option, the second a number. -/
abbrev adaptiveSpec : OracleSpec Bool
  | false => Option Nat
  | true => Nat

/-- Only a successful first reply asks the second, differently typed query. -/
def adaptive : OracleComp adaptiveSpec (Option Nat) := do
  let first ← (adaptiveSpec.query false : OracleComp adaptiveSpec (Option Nat))
  match first with
  | none => pure none
  | some value =>
    let second ← (adaptiveSpec.query true : OracleComp adaptiveSpec Nat)
    pure (some (value + second))

/-- Universal handler refinement covers both branches of the adaptive dependent client. -/
example {ιCheap ιFull Cache : Type}
    {cheapSpec : OracleSpec.{0, 0} ιCheap} {fullSpec : OracleSpec.{0, 0} ιFull}
    (cheap : QueryImpl adaptiveSpec (StateT (Cache × Nat) (OracleComp cheapSpec)))
    (full : QueryImpl adaptiveSpec (StateT (Cache × Nat) (OracleComp fullSpec)))
    (hstep : ∀ (t : adaptiveSpec.Domain) (sCheap sFull : Cache × Nat),
      sCheap.1 = sFull.1 ∧ sCheap.2 ≤ sFull.2 →
      ∀ (reply : adaptiveSpec.Range t) (sCheap' : Cache × Nat),
        (reply, sCheap') ∈ support ((cheap t).run sCheap) →
        ∃ sFull', (reply, sFull') ∈ support ((full t).run sFull) ∧
          sCheap'.1 = sFull'.1 ∧ sCheap'.2 ≤ sFull'.2)
    (initial : Cache × Nat) (budget : Nat)
    (hbound : ∀ reply final, (reply, final) ∈ support ((simulateQ full adaptive).run initial) →
      final.2 ≤ budget)
    (reply : Option Nat) (final : Cache × Nat)
    (hcheap : (reply, final) ∈ support ((simulateQ cheap adaptive).run initial)) :
    final.2 ≤ budget :=
  bound_of_support_refinement cheap full hstep adaptive initial budget hbound reply final hcheap

end VCVioTest.OracleComp.SupportRefinement
