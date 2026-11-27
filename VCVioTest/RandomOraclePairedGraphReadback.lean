/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.GraphReadback

/-!
# Paired readback with an ordinary high row and a canonical low row

One full word can combine a canonical low label with an ordinary high row. A conflict can
make a stored ordinary low bit disagree with the merged lookup.
-/

public section
open OracleSpec OracleComp CanonicalGraph.PairedQueries
namespace VCVioTest.RandomOraclePairedGraphReadback

/-- Only the low tag at the child's value is a graph point. -/
def graph : CanonicalGraph (PairedSpec Bool Bool) Unit Unit Bool where
  ch _ := [.inl ()]
  pt _ vs := .inl (vs.headD false)
  range_eq _ _ := rfl
  pt_inj {_ _ vs ws} hl hr eq := by
    match vs, ws, hl, hr with
    | [v], [w], _, _ => exact ⟨rfl, by simpa using eq⟩

private abbrev State := RelabelState (PairedSpec Bool Bool) Unit Unit Bool

/-- A ready low label and a public high entry can represent one full reply. -/
example (s : State) (key low high : Bool)
    (child : s.2 (.inl ()) = some key) (label : s.2 (.inr ()) = some low)
    (ordinary : s.1 (.inr key) = some high) :
    RandomOraclePairedValue.joinCache (Equiv.refl _) (graph.merge s) key = some (low, high) := by
  have ready : graph.childVals s () = some [key] :=
    graph.childVals_eq_some_iff.mpr (.cons child .nil)
  have lo := graph.merge_apply_pt ready
  have hi := graph.merge_apply_of_not_exists (st := s) (t := .inr key) (by
    rintro ⟨_, _, _, eq⟩
    cases eq)
  exact (RandomOraclePairedValue.joinCache_eq_some_iff _ _ _ _).2
    ⟨by simpa [graph, label] using lo, hi.trans ordinary⟩

/-- A ready node label can shadow an ordinary low reply in the same state. -/
private theorem shadowedLow (s : State) (key : Bool) (child : s.2 (.inl ()) = some key)
    (old : s.1 (.inl key) = some false) (label : s.2 (.inr ()) = some true) :
    graph.Conflict s ∧ graph.merge s (.inl key) ≠ some false := by
  have ready : graph.childVals s () = some [key] :=
    graph.childVals_eq_some_iff.mpr (.cons child .nil)
  refine ⟨⟨(), [key], ready, by simp [graph, old]⟩, ?_⟩
  have read := graph.merge_apply_pt ready
  change graph.merge s (.inl key) = _ at read
  simp [read, label]

/-- The conflicting snapshot exists with opposite ordinary and canonical bits. -/
example : ∃ s : State, graph.Conflict s ∧ s.1 (.inl true) = some false ∧
    graph.merge s (.inl true) ≠ some false := by
  let s : State := (.ofFn (fun _ => some false), .ofFn (fun _ => some true))
  have bad := shadowedLow s true rfl rfl rfl
  exact ⟨s, bad.1, rfl, bad.2⟩

/-- Filling a missing high row changes its answer while preserving every physical address. -/
example (c : (PairedSpec Nat Bool).QueryCache) (key : Nat) (low high : Bool)
    (warm : c (.inl key) = some low) (cold : c (.inr key) = none) :
    (c.cacheQuery (.inr key) high) (.inr key) ≠ c (.inr key) ∧
      physicalInputs (c.cacheQuery (.inr key) high) = physicalInputs c := by
  refine ⟨by simp [cold], ?_⟩
  ext x
  by_cases eq : x = key
  · subst x
    simp [physicalInputs, warm]
  · simp [physicalInputs, eq]

end VCVioTest.RandomOraclePairedGraphReadback
