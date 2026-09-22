/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.Covering

/-! # Interleaved-target coverage canaries

Two properties of `KeyedHash.Covering.TapeCoveredReuse` that its bound depends on and that no
statement in `Covering.lean` pins.

The freshness requirement — that a coverer differ from the target — is what keeps the event from
holding for every tuple: a one-coordinate tuple is uncovered, while the requirement-free
`TapeCoveredNoFresh` is satisfied by that same tuple.

Coverer reuse is a strict weakening: at `q = 2` and `k = 2` a constant tuple is covered with
reuse although no injective coverer assignment exists there at all.
-/

public section

open KeyedHash.Covering

namespace CoveringTest

/-! ## Freshness -/

/-- A one-coordinate tuple is not covered: its only coordinate is the target, and a coverer must
differ from the target. -/
theorem not_tapeCoveredReuse_of_q_eq_one (v : Fin 1 → Digest 0 1 1) :
    ¬ TapeCoveredReuse 0 1 1 1 v := by
  rintro ⟨j₀, f, hne, -⟩
  exact hne 0 (Subsingleton.elim _ _)

/-- Without the freshness requirement that same tuple *is* covered. -/
theorem tapeCoveredNoFresh_of_q_eq_one (v : Fin 1 → Digest 0 1 1) :
    TapeCoveredNoFresh 0 1 1 1 v :=
  tapeCoveredNoFresh_of_pos 0 1 1 Nat.one_pos v

/-! ## Reuse -/

/-- A constant two-coordinate tuple is covered with reuse: the second coordinate covers both
digits of the first. -/
theorem tapeCoveredReuse_const :
    TapeCoveredReuse 0 1 2 2 (fun _ => (0, fun _ => 0)) :=
  ⟨0, fun _ => 1, fun _ => (by decide : (1 : Fin 2) ≠ (0 : Fin 2)), fun _ => ⟨rfl, rfl⟩⟩

/-- At `q = 2` and `k = 2` no injective coverer assignment exists at all: a target coordinate
together with two distinct coverers needs three distinct coordinates out of two.  With
`tapeCoveredReuse_const` this makes coverage with reuse a strict super-event of its injective
restriction. -/
theorem not_exists_injective_coverers :
    ¬ ∃ (j₀ : Fin 2) (f : Fin 2 → Fin 2), Function.Injective f ∧ ∀ i, f i ≠ j₀ := by
  decide

end CoveringTest
