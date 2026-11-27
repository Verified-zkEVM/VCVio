/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.DisclosureTrace
public import VCVio.OracleComp.QueryTracking.RandomOracle.PublicReplay

/-!
# A public probe of a deferred Boolean chain

A public probe to an unready node leaves its private child undisclosed. Repeating a pending
Boolean cell in the final fill still gives a fixed guess probability at most one half.
-/

public section
open OracleSpec OracleComp
open scoped ENNReal

namespace VCVioTest.RandomOracleUndisclosed

/-- The node uses one private Boolean predecessor as its public point. -/
def chain : CanonicalGraph (Bool →ₒ Bool) Unit Unit Bool where
  ch _ := [.inl ()]
  pt _ vs := vs.headD false
  range_eq _ _ := rfl
  pt_inj {_ _ xs ys} hx hy eq := by
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hx
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hy
    exact ⟨Subsingleton.elim _ _, congrArg (fun v => [v]) eq⟩

/-- Starting from empty caches, querying `true` leaves the node and its private child absent. -/
theorem raw_probe {z} (run : z ∈ support ((chain.deferredImpl
    (.inl (.inl (.inr true)))).run ((∅, ∅), []))) :
    z.2.1.2 (.inr ()) = none ∧ z.2.1.2 (.inl ()) = none := by
  have closed (k : Unit) (_ : Sum.inr k ∈ (Set.univ : Set (Unit ⊕ Unit))) :=
    show ∃ c ∈ chain.ch k, c ∈ (Set.univ : Set (Unit ⊕ Unit)) from
      ⟨.inl (), List.mem_singleton_self _, Set.mem_univ _⟩
  let t : ((Bool →ₒ Bool).withLabels Unit Unit Bool).Domain := .inl (.inl (.inr true))
  have step := chain.stays_undisclosed closed
    ((allQueriesSatisfy_query_iff t _).2 trivial)
    (s := ((∅, ∅), [])) (fun _ _ => rfl) (z := z) (by simpa using run)
  exact ⟨step _ (Set.mem_univ _), step _ (Set.mem_univ _)⟩

/-- Repeating the same pending cell does not increase its chance of matching a fixed Boolean. -/
theorem repeated_guess :
    Pr{let st ← RelabelState.endFill (((∅, ∅) : RelabelState (Bool →ₒ Bool) Unit Unit Bool),
      [.inl (), .inr (), .inl ()])}[st.2 (.inl ()) = some true] ≤ (1 : ℝ≥0∞) / 2 := by
  have bound := RelabelState.prEvent_endFill_guesses_le
    ((∅, ∅) : RelabelState (Bool →ₒ Bool) Unit Unit Bool)
    [.inl (), .inr (), .inl ()] (fun _ : Unit => Sum.inl ()) (fun _ => true)
  simpa [Nat.card_eq_fintype_card, div_eq_mul_inv] using bound

end VCVioTest.RandomOracleUndisclosed
