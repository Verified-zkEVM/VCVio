/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.Collection

/-!
# Final-validity monitoring for multi-target tweakable-hash games

The EasyCrypt/BDHMS games answer and record every target and collection query, then require at the
end that the target cap, distinct-target-tweak condition, and target/collection disjointness all
hold. This file packages an equivalent sticky **poison bit** presentation: every query is still
answered and recorded, while the first validity violation changes `valid` permanently to `false`.

This is intentionally separate from `collectionOracle`, whose rejection-on-arrival semantics are a
different adaptive experiment. A reduction may use the declarations below only when it is proving
the source final-validity game or has a separate equivalence theorem.
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec

variable {ι PkSeed Tweak Y Q : Type}

/-- Histories and sticky validity bit shared by a target oracle and a collection oracle. -/
structure FinalValidityState (Q Tweak : Type) where
  /-- Every target query, including queries issued after the game became invalid. -/
  challenges : List Q
  /-- Every collection tweak, including queries issued after the game became invalid. -/
  collectionTweaks : List Tweak
  /-- Sticky validity bit for the target cap and tweak-separation conditions. -/
  valid : Bool

/-- The initially valid empty final-validity state. -/
def FinalValidityState.initial : FinalValidityState Q Tweak := ⟨[], [], true⟩

/-- The explicit final predicate used by the EasyCrypt/BDHMS games: no more than `numTargets`
targets, pairwise-distinct target tweaks, and no target tweak used by the collection oracle. -/
def FinalValid (numTargets : ℕ) (tweakOf : Q → Tweak) (st : FinalValidityState Q Tweak) : Prop :=
  st.challenges.length ≤ numTargets ∧
    (st.challenges.map tweakOf).Nodup ∧
    (st.challenges.map tweakOf).Disjoint st.collectionTweaks

instance [DecidableEq Tweak] (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : FinalValidityState Q Tweak) : Decidable (FinalValid numTargets tweakOf st) :=
  decidable_of_iff
    (st.challenges.length ≤ numTargets ∧
      (st.challenges.map tweakOf).Nodup ∧
      ∀ a ∈ st.challenges.map tweakOf, ∀ b ∈ st.collectionTweaks, a ≠ b)
    (and_congr Iff.rfl (and_congr Iff.rfl List.disjoint_iff_ne.symm))

/-- Executable form of `FinalValid`. The disjointness conjunct is expanded elementwise so the
decision procedure is explicit and stable. -/
def FinalValidBool [DecidableEq Tweak] (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : FinalValidityState Q Tweak) : Bool :=
  decide (st.challenges.length ≤ numTargets) &&
    decide (st.challenges.map tweakOf).Nodup &&
    decide (∀ a ∈ st.challenges.map tweakOf, ∀ b ∈ st.collectionTweaks, a ≠ b)

/-- The monitor invariant: the sticky bit is exactly the decision procedure for the source final
predicate, rather than merely a one-way soundness flag. -/
def FinalValidityInvariant [DecidableEq Tweak] (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : FinalValidityState Q Tweak) : Prop :=
  st.valid = FinalValidBool numTargets tweakOf st

/-- Record a target query and poison the state if the target cap or tweak discipline is violated.
The query is always recorded; hashing and returning its answer is the caller's responsibility. -/
def FinalValidityState.recordTarget [DecidableEq Tweak] (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : FinalValidityState Q Tweak) (q : Q) : FinalValidityState Q Tweak where
  challenges := st.challenges ++ [q]
  collectionTweaks := st.collectionTweaks
  valid := st.valid && st.challenges.length < numTargets &&
    decide (TweakFresh tweakOf st.challenges st.collectionTweaks (tweakOf q))

/-- Record a collection tweak and poison the state if it was already reserved by a target query.
Repeated collection tweaks are valid and remain recorded, exactly as in the source collection
game. -/
def FinalValidityState.recordCollection [DecidableEq Tweak] (tweakOf : Q → Tweak)
    (st : FinalValidityState Q Tweak) (t : Tweak) : FinalValidityState Q Tweak where
  challenges := st.challenges
  collectionTweaks := st.collectionTweaks ++ [t]
  valid := st.valid && decide (¬TweakReserved tweakOf st.challenges t)

/-! ## Correspondence to the source final predicate -/

section Correspondence

variable [DecidableEq Tweak]

/-- The executable check recognizes exactly the source final predicate. -/
theorem finalValidBool_eq_true_iff (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : FinalValidityState Q Tweak) :
    FinalValidBool numTargets tweakOf st = true ↔ FinalValid numTargets tweakOf st := by
  simp [FinalValidBool, FinalValid, List.disjoint_iff_ne]
  tauto

/-- Consequently, the invariant also has the literal `decide (FinalValid …)` form. -/
theorem FinalValidityInvariant.eq_decide (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : FinalValidityState Q Tweak) (hinv : FinalValidityInvariant numTargets tweakOf st) :
    st.valid = decide (FinalValid numTargets tweakOf st) := by
  rw [hinv]
  apply Bool.eq_iff_iff.mpr
  simp [finalValidBool_eq_true_iff]

/-- The initial monitor satisfies the exact source predicate. -/
theorem finalValidityInvariant_initial (numTargets : ℕ) (tweakOf : Q → Tweak) :
    FinalValidityInvariant numTargets tweakOf (.initial : FinalValidityState Q Tweak) := by
  simp [FinalValidityInvariant, FinalValidityState.initial, FinalValidBool]

set_option linter.flexible false in
/-- Recording a target query preserves exact correspondence between the poison bit and the source
final predicate. -/
theorem FinalValidityInvariant.recordTarget (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : FinalValidityState Q Tweak) (q : Q)
    (hinv : FinalValidityInvariant numTargets tweakOf st) :
    FinalValidityInvariant numTargets tweakOf (st.recordTarget numTargets tweakOf q) := by
  rcases st with ⟨challenges, collectionTweaks, valid⟩
  simp only [FinalValidityInvariant, FinalValidityState.recordTarget] at hinv ⊢
  rw [hinv]
  apply Bool.eq_iff_iff.mpr
  simp [FinalValidBool, TweakFresh, TweakReserved, List.nodup_append]
  constructor
  · rintro ⟨⟨⟨⟨hlen, hnodup⟩, hdisjoint⟩, hlt⟩, hfresh, hnotColl⟩
    refine ⟨⟨hlt, hnodup, hfresh⟩, ?_⟩
    intro a ha b hb
    rcases ha with ⟨x, hx, rfl⟩ | rfl
    · exact hdisjoint x hx b hb
    · intro heq
      exact hnotColl (heq ▸ hb)
  · rintro ⟨⟨hlt, hnodup, hfresh⟩, hdisjoint⟩
    refine ⟨⟨⟨⟨Nat.le_of_lt hlt, hnodup⟩, ?_⟩, hlt⟩, hfresh, ?_⟩
    · intro x hx b hb
      exact hdisjoint (tweakOf x) (Or.inl ⟨x, hx, rfl⟩) b hb
    · intro hmem
      exact hdisjoint (tweakOf q) (Or.inr rfl) (tweakOf q) hmem rfl

set_option linter.flexible false in
/-- Recording a collection query preserves exact correspondence between the poison bit and the
source final predicate. -/
theorem FinalValidityInvariant.recordCollection (numTargets : ℕ) (tweakOf : Q → Tweak)
    (st : FinalValidityState Q Tweak) (t : Tweak)
    (hinv : FinalValidityInvariant numTargets tweakOf st) :
    FinalValidityInvariant numTargets tweakOf (st.recordCollection tweakOf t) := by
  rcases st with ⟨challenges, collectionTweaks, valid⟩
  simp only [FinalValidityInvariant, FinalValidityState.recordCollection] at hinv ⊢
  rw [hinv]
  apply Bool.eq_iff_iff.mpr
  simp [FinalValidBool, TweakReserved]
  constructor
  · rintro ⟨⟨⟨hlen, hnodup⟩, hdisjoint⟩, hunreserved⟩
    refine ⟨⟨hlen, hnodup⟩, ?_⟩
    intro x hx b hb
    rcases hb with hb | rfl
    · exact hdisjoint x hx b hb
    · exact hunreserved x hx
  · rintro ⟨⟨hlen, hnodup⟩, hdisjoint⟩
    refine ⟨⟨⟨hlen, hnodup⟩, ?_⟩, ?_⟩
    · intro x hx b hb
      exact hdisjoint x hx b (Or.inl hb)
    · intro x hx
      exact hdisjoint x hx t (Or.inr rfl)

end Correspondence

/-- Final-validity collection queries return the member's digest directly: invalid queries poison
the monitor but are never rejected. -/
abbrev finalValidityCollectionSpec (thColl : TweakableHashCollection ι PkSeed Tweak Y) :
    OracleSpec ((i : ι) × Tweak × thColl.Msg i) :=
  _ →ₒ Y

/-- The always-answering collection oracle for final-validity games. -/
def finalValidityCollectionOracle [DecidableEq Tweak] (tweakOf : Q → Tweak)
    (thColl : TweakableHashCollection ι PkSeed Tweak Y) (pk : PkSeed) :
    QueryImpl (finalValidityCollectionSpec thColl) (StateT (FinalValidityState Q Tweak) ProbComp) :=
  fun q => do
    let st ← get
    set (st.recordCollection tweakOf q.2.1)
    return thColl.eval q.1 pk q.2.1 q.2.2

/-! ## Mutation-resistant semantic pins -/

variable [DecidableEq Tweak] (tweakOf : Q → Tweak)
  {st : FinalValidityState Q Tweak} {q : Q} {t : Tweak}

/-- Target queries are still recorded after violating the cap; the validity bit is poisoned. -/
theorem recordTarget_at_cap :
    (st.recordTarget 0 tweakOf q).challenges = st.challenges ++ [q] ∧
      (st.recordTarget 0 tweakOf q).valid = false := by
  simp [FinalValidityState.recordTarget]

/-- Repeating a collection tweak does not poison an otherwise valid state when no target reserved
it. This would fail if collection tweaks were incorrectly required to be distinct. -/
theorem recordCollection_repeated_of_unreserved (hvalid : st.valid = true)
    (hunreserved : ¬TweakReserved tweakOf st.challenges t) :
    ((st.recordCollection tweakOf t).recordCollection tweakOf t).valid = true := by
  simp [FinalValidityState.recordCollection, hvalid, hunreserved]

end TweakableHash
