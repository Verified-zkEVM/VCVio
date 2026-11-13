/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import ToMathlib.Data.List.FirstWrite

/-!
# Certificate readback at the earliest logical event

The final stored payload selects an origin in the same supplied event list.
The selected event retains its certificate from that list, including when later events also match.
-/

public section

namespace VCVioTest.ListFirstWrite

universe uS uE uP uCert

/-- The earliest-origin event retains its certificate from this same finite event list. -/
theorem certified_earliest_origin
    {S : Type uS} {E : Type uE} {P : Type uP}
    (lookup : S → Option P) (step : S → E → S)
    (isMatch : E → Prop) [DecidablePred isMatch] (value : E → P)
    (preserves_some : ∀ state event payload,
      lookup state = some payload → lookup (step state event) = some payload)
    (step_none : ∀ state event, lookup state = none →
      lookup (step state event) = if isMatch event then some (value event) else none)
    (events : List E) (initial : S) (payload : P)
    (Cert : E → Sort uCert) (certified : ∀ event ∈ events, Cert event)
    (empty : lookup initial = none)
    (stored : lookup (events.foldl step initial) = some payload) :
    ∃ before event after, events = before ++ event :: after ∧
      (∀ earlier ∈ before, ¬ isMatch earlier) ∧ isMatch event ∧
      value event = payload ∧ Nonempty (Cert event) := by
  obtain ⟨before, event, after, decomposition, earlier, matching, value_eq⟩ :=
    List.exists_first_match_of_lookup_foldl_eq_some lookup step isMatch value
      preserves_some step_none events initial payload empty stored
  have member : event ∈ events := by
    rw [decomposition]
    simp
  exact ⟨before, event, after, decomposition, earlier, matching, value_eq,
    ⟨certified event member⟩⟩


-- A recorded unsuccessful result is a payload, rather than an empty outer lookup.
private theorem recorded_none_survives
    {S : Type uS} {E : Type uE} {P : Type uP}
    (lookup : S → Option (Option P)) (step : S → E → S)
    (preserves_some : ∀ state event payload,
      lookup state = some payload → lookup (step state event) = some payload)
    (events : List E) (initial : S) (stored : lookup initial = some none) :
    lookup (events.foldl step initial) = some none :=
  List.lookup_foldl_eq_some_of_preserves_some lookup step preserves_some events initial none stored

end VCVioTest.ListFirstWrite
