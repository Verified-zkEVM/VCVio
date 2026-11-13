/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module
public import Mathlib.Data.List.Basic

/-!
# Earliest origin of a first-write value

The initial lookup is `none`, and each matching event can fill it with its payload.
Once the lookup is `some payload`, every later step preserves that same value.
The final payload therefore comes from the first matching event in the same finite list.
The split `before ++ event :: after` locates its least logical position at `before.length`.

`none` means that no payload is stored.
If the payload type is itself an `Option`, `some none` is a stored value and is preserved.
These laws impose no recorder implementation, query order, freshness or probability interpretation.
-/

public section

namespace List

universe uS uE uP

variable {S : Type uS} {E : Type uE} {P : Type uP}

/-- Every later event preserves the same already stored payload. -/
theorem lookup_foldl_eq_some_of_preserves_some
    (lookup : S → Option P) (step : S → E → S)
    (preserves_some : ∀ state event payload,
      lookup state = some payload → lookup (step state event) = some payload)
    (events : List E) (initial : S) (payload : P)
    (stored : lookup initial = some payload) :
    lookup (events.foldl step initial) = some payload := by
  exact List.foldlRecOn (motive := fun state => lookup state = some payload)
    events step stored (fun state kept event _ => preserves_some state event payload kept)

/-- The final payload is written at the least matching position of this same event list. -/
theorem exists_first_match_of_lookup_foldl_eq_some
    (lookup : S → Option P) (step : S → E → S)
    (isMatch : E → Prop) [DecidablePred isMatch] (value : E → P)
    (preserves_some : ∀ state event payload,
      lookup state = some payload → lookup (step state event) = some payload)
    (step_none : ∀ state event, lookup state = none →
      lookup (step state event) = if isMatch event then some (value event) else none)
    (events : List E) (initial : S) (payload : P)
    (empty : lookup initial = none)
    (stored : lookup (events.foldl step initial) = some payload) :
    ∃ before event after, events = before ++ event :: after ∧
      (∀ earlier ∈ before, ¬ isMatch earlier) ∧ isMatch event ∧ value event = payload := by
  induction events generalizing initial with
  | nil =>
    have impossible : (none : Option P) = some payload := empty.symm.trans stored
    cases impossible
  | cons event rest ih =>
    simp only [List.foldl_cons] at stored
    by_cases matching : isMatch event
    · have recorded : lookup (step initial event) = some (value event) := by
        rw [step_none initial event empty, ite_eq_left matching]
      -- The same head payload survives the complete remaining suffix.
      have final := lookup_foldl_eq_some_of_preserves_some lookup step preserves_some rest
        (step initial event) (value event) recorded
      have value_eq : value event = payload := Option.some.inj (final.symm.trans stored)
      exact ⟨[], event, rest, rfl, by simp, matching, value_eq⟩
    · have still_empty : lookup (step initial event) = none := by
        rw [step_none initial event empty, ite_eq_right matching]
      obtain ⟨before, first, after, decomposition, earlier, first_matches, value_eq⟩ :=
        ih (step initial event) still_empty stored
      refine ⟨event :: before, first, after, ?_, ?_, first_matches, value_eq⟩
      · simp only [List.cons_append]
        rw [decomposition]
      · intro candidate member
        rcases List.mem_cons.mp member with same | prior
        · subst candidate
          exact matching
        · exact earlier candidate prior

end List
