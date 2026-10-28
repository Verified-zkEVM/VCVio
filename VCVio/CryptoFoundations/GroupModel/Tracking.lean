/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Instances
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import Mathlib.Data.List.GetD

/-!
# Representations preserved by generic group computations

Given handles identify the basis receipts. Every table entry is supported on those
handles and evaluates to its accompanying module element.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

/-- Evaluate a representation against the values in a tracked table. -/
@[expose] def Repr.eval {F G : Type} [CommSemiring F] [AddCommMonoid G] [Module F G]
    (r : Repr F) (tbl : List (Repr F × G)) : G := evRepr (tbl.map Prod.snd) r

/-- Inputs carry the basis representation at their own handle. -/
@[expose] def trackInputs {F S : Type} [Zero F] [One F] {G : S → Type}
    (xs : (s : S) → List (G s)) : Tbl (fun s => Repr F × G s) :=
  fun s => (xs s).mapIdx fun i x => (Pi.single i 1, x)

/-- Every entry is explained by the distinct given handles, in receipt order. -/
structure Explains {F S : Type} [CommSemiring F] {G : S → Type}
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    («given» : S → List Handle) (tbl : Tbl (fun s => Repr F × G s)) : Prop where
  /-- Every given handle refers to an existing table entry. -/
  given_lt : ∀ s h, h ∈ «given» s → h < (tbl s).length
  /-- Each given entry carries the basis vector at its own handle. -/
  repr_given : ∀ s h, h ∈ «given» s → (lookup tbl s h).1 = Pi.single h 1
  /-- Every nonzero coefficient refers to a given handle. -/
  support_subset : ∀ s e, e ∈ tbl s → ∀ h, e.1 h ≠ 0 → h ∈ «given» s
  /-- Every entry evaluates to its accompanying module element. -/
  eq_eval : ∀ s e, e ∈ tbl s → e.2 = e.1.eval (tbl s)
  /-- Receipts occupy distinct handles in each sort. -/
  given_nodup : ∀ s, («given» s).Nodup

section Evaluation

variable {F G : Type} [CommSemiring F] [AddCommMonoid G] [Module F G]

/-- Evaluation as a finite sum over table indices. -/
theorem Repr.eval_eq_sum (r : Repr F) (tbl : List (Repr F × G)) :
    r.eval tbl = ∑ i ∈ Finset.range tbl.length, r i • (tbl.getD i 0).2 := by
  simp only [Repr.eval, evRepr_apply, List.length_map]
  congr 1
  ext i
  rw [show (0 : G) = Prod.snd (0 : Repr F × G) from rfl, List.getD_map]

/-- Evaluation respects addition of coefficient functions. -/
theorem Repr.eval_add (r t : Repr F) (tbl : List (Repr F × G)) :
    (r + t).eval tbl = r.eval tbl + t.eval tbl := map_add _ _ _

/-- Evaluation respects scalar multiplication of coefficient functions. -/
theorem Repr.eval_smul (c : F) (r : Repr F) (tbl : List (Repr F × G)) :
    (c • r).eval tbl = c • r.eval tbl := map_smul _ _ _

/-- The zero representation evaluates to zero. -/
@[simp] theorem Repr.eval_zero (tbl : List (Repr F × G)) : (0 : Repr F).eval tbl = 0 :=
  map_zero _

/-- Evaluation of a basis representation reads the corresponding value. -/
theorem Repr.eval_single (tbl : List (Repr F × G)) (h : Handle) (hh : h < tbl.length) :
    Repr.eval (Pi.single h (1 : F)) tbl = (tbl.getD h 0).2 := by
  simp [Repr.eval_eq_sum, Pi.single_apply, hh]

/-- Appending a value does not affect a representation with zero fresh coefficient. -/
theorem Repr.eval_append (r : Repr F) (tbl : List (Repr F × G)) (e : Repr F × G)
    (hr : r tbl.length = 0) : r.eval (tbl ++ [e]) = r.eval tbl := by
  simp only [Repr.eval_eq_sum, List.length_append, List.length_singleton, Finset.sum_range_succ]
  rw [hr, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]

end Evaluation

section Lookups

variable {F S : Type} [Zero F] {G : S → Type} [∀ s, Zero (G s)]

/-- A lookup outside the table returns the zero pair. -/
theorem lookup_eq_zero (tbl : Tbl (fun s => Repr F × G s)) (s : S) (h : Handle)
    (hh : (tbl s).length ≤ h) : lookup tbl s h = 0 := List.getD_eq_default _ _ hh

variable [DecidableEq S]

/-- Appending preserves lookups at every existing handle. -/
theorem lookup_append_old (tbl : Tbl (fun s => Repr F × G s)) (s : S)
    (e : Repr F × G s) (t : S) (h : Handle) (hh : h < (tbl t).length) :
    lookup (GroupModel.append tbl s e) t h = lookup tbl t h := by
  by_cases ht : t = s
  · subst t
    simp only [lookup, GroupModel.append, Function.update_self]
    exact List.getD_append _ _ _ _ hh
  · simp [lookup, GroupModel.append, Function.update_of_ne ht]

/-- Appending places the new element at the fresh handle. -/
theorem lookup_append_fresh (tbl : Tbl (fun s => Repr F × G s)) (s : S)
    (e : Repr F × G s) : lookup (GroupModel.append tbl s e) s (tbl s).length = e := by
  simp [lookup, GroupModel.append]

end Lookups

section Invariant

variable {F S : Type} [CommSemiring F] {G : S → Type}
  [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]

/-- Initial input tables satisfy the representation invariant. -/
theorem explains_trackInputs (xs : (s : S) → List (G s)) :
    Explains (F := F) (fun s => List.range (xs s).length) (trackInputs xs) := by
  constructor
  · intro s h hh
    simpa [trackInputs] using List.mem_range.mp hh
  · intro s h hh
    simp only [lookup, trackInputs]
    rw [List.getD_eq_getElem _ _ (by simpa using List.mem_range.mp hh)]
    simp
  · intro s e he h hh
    simp only [trackInputs, List.mem_mapIdx] at he
    obtain ⟨i, hi, rfl⟩ := he
    by_cases hih : i = h
    · subst h
      exact List.mem_range.mpr hi
    · exact False.elim (hh (by simp [hih]))
  · intro s e he
    simp only [trackInputs, List.mem_mapIdx] at he
    obtain ⟨i, hi, rfl⟩ := he
    rw [Repr.eval_single _ _ (by simpa [trackInputs] using hi)]
    simp [trackInputs, hi]
  · intro s
    exact List.nodup_range

/-- All lookups, including invalid handles, have support among the given handles. -/
theorem Explains.lookup_support {«given» : S → List Handle} {tbl : Tbl (fun s => Repr F × G s)}
    (ht : Explains «given» tbl) (s : S) (h j : Handle) (hj : (lookup tbl s h).1 j ≠ 0) :
    j ∈ «given» s := by
  by_cases hh : h < (tbl s).length
  · apply ht.support_subset s _ _ j hj
    rw [lookup, List.getD_eq_getElem _ _ hh]
    exact List.getElem_mem _
  · simp [lookup_eq_zero tbl s h (Nat.le_of_not_gt hh)] at hj

/-- Every lookup is the value of its representation, also at invalid handles. -/
theorem Explains.lookup_eval {«given» : S → List Handle} {tbl : Tbl (fun s => Repr F × G s)}
    (ht : Explains «given» tbl) (s : S) (h : Handle) :
    (lookup tbl s h).2 = (lookup tbl s h).1.eval (tbl s) := by
  by_cases hh : h < (tbl s).length
  · apply ht.eq_eval s
    rw [lookup, List.getD_eq_getElem _ _ hh]
    exact List.getElem_mem _
  · simp [lookup_eq_zero tbl s h (Nat.le_of_not_gt hh)]

/-- No explained representation uses the next free table handle. -/
theorem Explains.fresh_zero {«given» : S → List Handle}
    {tbl : Tbl (fun s => Repr F × G s)} (ht : Explains «given» tbl)
    (s : S) (r : Repr F) (hr : ∀ j, r j ≠ 0 → j ∈ «given» s) :
    r (tbl s).length = 0 := by
  by_contra h
  exact (Nat.lt_irrefl _ (ht.given_lt s _ (hr _ h)))

section Append

variable [DecidableEq S]

/-- Appending an explained element preserves the basis and the invariant. -/
theorem Explains.append {«given» : S → List Handle} {tbl : Tbl (fun s => Repr F × G s)}
    (ht : Explains «given» tbl) (s : S) (e : Repr F × G s)
    (hs : ∀ j, e.1 j ≠ 0 → j ∈ «given» s) (he : e.2 = e.1.eval (tbl s)) :
    Explains «given» (GroupModel.append tbl s e) := by
  have old_eval (t : S) (r : Repr F) (hr : ∀ j, r j ≠ 0 → j ∈ «given» t) :
      r.eval (GroupModel.append tbl s e t) = r.eval (tbl t) := by
    by_cases hts : t = s
    · subst t
      simp only [GroupModel.append, Function.update_self]
      exact Repr.eval_append _ _ _ (ht.fresh_zero _ _ hr)
    · simp [GroupModel.append, Function.update_of_ne hts]
  constructor
  · intro t h hh
    have := ht.given_lt t h hh
    by_cases hts : t = s
    · subst t
      simp only [GroupModel.append, Function.update_self, List.length_append, List.length_singleton]
      exact Nat.lt_succ_of_lt (ht.given_lt s h hh)
    · simpa [GroupModel.append, Function.update_of_ne hts] using this
  · intro t h hh
    rw [lookup_append_old _ _ _ _ _ (ht.given_lt t h hh)]
    exact ht.repr_given t h hh
  · intro t v hv j hj
    by_cases hts : t = s
    · subst t
      simp only [GroupModel.append, Function.update_self, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact ht.support_subset s v hv j hj
      · exact hs j hj
    · exact ht.support_subset t v
        (by simpa [GroupModel.append, Function.update_of_ne hts] using hv) j hj
  · intro t v hv
    by_cases hts : t = s
    · subst t
      simp only [GroupModel.append, Function.update_self, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · rw [old_eval s v.1 (ht.support_subset s v hv)]
        exact ht.eq_eval s v hv
      · rw [old_eval s v.1 hs]
        exact he
    · have hv' : v ∈ tbl t := by simpa [GroupModel.append, Function.update_of_ne hts] using hv
      rw [old_eval t v.1 (ht.support_subset t v hv')]
      exact ht.eq_eval t v hv'
  · exact ht.given_nodup

/-- Receive a module element as a new basis entry at its fresh table handle. -/
@[expose] def pushGiven (s : S) (g : G s) {m : Type → Type} [Monad m] :
    StateT (Tbl (fun s => Repr F × G s)) m Handle := fun tbl =>
  (push s (Pi.single (tbl s).length 1, g)).run tbl

/-- Receiving a new basis element extends the list of distinct given handles. -/
theorem Explains.pushGiven {«given» : S → List Handle} {tbl : Tbl (fun s => Repr F × G s)}
    (ht : Explains «given» tbl) (s : S) (g : G s) :
    Explains (Function.update «given» s («given» s ++ [(tbl s).length]))
      (GroupModel.append tbl s (Pi.single (tbl s).length 1, g)) := by
  let h := (tbl s).length
  let e : Repr F × G s := (Pi.single h 1, g)
  have fresh : h ∉ «given» s := fun hh => Nat.lt_irrefl _ (ht.given_lt s h hh)
  have old_eval (t : S) (r : Repr F) (hr : ∀ j, r j ≠ 0 → j ∈ «given» t) :
      r.eval (GroupModel.append tbl s e t) = r.eval (tbl t) := by
    by_cases hts : t = s
    · subst t
      simp only [GroupModel.append, Function.update_self]
      exact Repr.eval_append _ _ _ (ht.fresh_zero _ _ hr)
    · simp [GroupModel.append, Function.update_of_ne hts]
  constructor
  · intro t j hj
    by_cases hts : t = s
    · subst t
      simp only [Function.update_self, List.mem_append, List.mem_singleton] at hj
      simp only [GroupModel.append, Function.update_self, List.length_append, List.length_singleton]
      rcases hj with hj | rfl
      · have := ht.given_lt s j hj
        exact Nat.lt_succ_of_lt (ht.given_lt s j hj)
      · exact Nat.lt_succ_self _
    · simpa [GroupModel.append, Function.update_of_ne hts] using
        ht.given_lt t j (by simpa [Function.update_of_ne hts] using hj)
  · intro t j hj
    by_cases hts : t = s
    · subst t
      simp only [Function.update_self, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · rw [lookup_append_old _ _ _ _ _ (ht.given_lt s j hj)]
        exact ht.repr_given s j hj
      · rw [lookup_append_fresh]
    · have hj' : j ∈ «given» t := by simpa [Function.update_of_ne hts] using hj
      rw [lookup_append_old _ _ _ _ _ (ht.given_lt t j hj')]
      exact ht.repr_given t j hj'
  · intro t v hv j hj
    by_cases hts : t = s
    · subst t
      simp only [GroupModel.append, Function.update_self, List.mem_append, List.mem_singleton] at hv
      simp only [Function.update_self, List.mem_append, List.mem_singleton]
      rcases hv with hv | rfl
      · exact Or.inl (ht.support_subset s v hv j hj)
      · right
        by_contra hne
        exact hj (by simp [Ne.symm hne])
    · simpa [Function.update_of_ne hts] using
        ht.support_subset t v
          (by simpa [GroupModel.append, Function.update_of_ne hts] using hv) j hj
  · intro t v hv
    by_cases hts : t = s
    · subst t
      simp only [GroupModel.append, Function.update_self, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · change v.2 = v.1.eval (GroupModel.append tbl s e s)
        rw [old_eval s v.1 (ht.support_subset s v hv)]
        exact ht.eq_eval s v hv
      · rw [Repr.eval_single _ _ (by simp [GroupModel.append])]
        exact congrArg Prod.snd (lookup_append_fresh tbl s e).symm
    · have hv' : v ∈ tbl t := by simpa [GroupModel.append, Function.update_of_ne hts] using hv
      change v.2 = v.1.eval (GroupModel.append tbl s e t)
      rw [old_eval t v.1 (ht.support_subset t v hv')]
      exact ht.eq_eval t v hv'
  · intro t
    by_cases hts : t = s
    · subst t
      simpa using (ht.given_nodup s).concat fresh
    · simpa [Function.update_of_ne hts] using ht.given_nodup t

/-- The stateful receipt operation returns an invariant with the new basis handle. -/
theorem explains_of_mem_support_pushGiven {«given» : S → List Handle}
    {tbl : Tbl (fun s => Repr F × G s)} (ht : Explains «given» tbl) (s : S) (g : G s)
    (z : Handle × Tbl (fun s => Repr F × G s))
    (hz : z ∈ support ((pushGiven s g : StateT _ ProbComp Handle).run tbl)) :
    Explains (Function.update «given» s («given» s ++ [z.1])) z.2 := by
  have hz' : z = ((tbl s).length, GroupModel.append tbl s (Pi.single (tbl s).length 1, g)) := by
    simpa [pushGiven, push, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StateT.run] using hz
  subst z
  exact ht.pushGiven s g

section Handler

variable [∀ s, DecidableEq (G s)]

/-- Generic module operations preserve explanations over the existing basis receipts. -/
theorem impl_tracking_preservesInv («given» : S → List Handle) :
    QueryImpl.PreservesInv
      (impl (tracking (Model.discrete G)) (fun _ => Prod.snd) ProbComp)
      (Explains (F := F) «given») := by
  intro q
  cases q with
  | add s a b =>
    intro tbl ht z hz
    change Handle × Tbl (fun s => Repr F × G s) at z
    have hz' : z = ((tbl s).length,
        GroupModel.append tbl s (lookup tbl s a + lookup tbl s b)) := by
      change z ∈ support (pure ((tbl s).length,
        GroupModel.append tbl s (lookup tbl s a + lookup tbl s b)) : ProbComp _) at hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      exact hz
    subst z
    apply ht.append
    · intro j hj
      by_contra hn
      have ha : (lookup tbl s a).1 j = 0 := by
        by_contra ha
        exact hn (ht.lookup_support s a j ha)
      have hb : (lookup tbl s b).1 j = 0 := by
        by_contra hb
        exact hn (ht.lookup_support s b j hb)
      exact hj (by simp [ha, hb])
    · change (lookup tbl s a).2 + (lookup tbl s b).2 =
        ((lookup tbl s a).1 + (lookup tbl s b).1).eval (tbl s)
      rw [Repr.eval_add, ← ht.lookup_eval s a, ← ht.lookup_eval s b]
  | smul s c a =>
    intro tbl ht z hz
    change Handle × Tbl (fun s => Repr F × G s) at z
    have hz' : z = ((tbl s).length,
        GroupModel.append tbl s (c • lookup tbl s a)) := by
      change z ∈ support (pure ((tbl s).length,
        GroupModel.append tbl s (c • lookup tbl s a)) : ProbComp _) at hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      exact hz
    subst z
    apply ht.append
    · intro j hj
      apply ht.lookup_support s a j
      intro ha
      exact hj (by simp [ha])
    · change c • (lookup tbl s a).2 = (c • (lookup tbl s a).1).eval (tbl s)
      rw [Repr.eval_smul, ← ht.lookup_eval s a]
  | eq s a b =>
    intro tbl ht z hz
    change Bool × Tbl (fun s => Repr F × G s) at z
    have hz' : z = (decide ((lookup tbl s a).2 = (lookup tbl s b).2), tbl) := by
      change z ∈ support (pure (decide ((lookup tbl s a).2 = (lookup tbl s b).2), tbl) :
        ProbComp _) at hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      exact hz
    subst z
    exact ht
  | lin o a => exact o.elim
  | bil o a b => exact o.elim

/-- Every reachable table of a generic run retains explanations over the given handles. -/
theorem explains_of_mem_support_runGen {«given» : S → List Handle}
    {tbl : Tbl (fun s => Repr F × G s)} (ht : Explains «given» tbl) {α : Type}
    (oa : OracleComp (genSpec F (discreteSig S)) α)
    (z : α × Tbl (fun s => Repr F × G s))
    (hz : z ∈ support (runGen (tracking (Model.discrete G)) (fun _ => Prod.snd) oa tbl)) :
    Explains «given» z.2 := by
  apply simulateQ_run_preservesInv _ _
    ((impl_tracking_preservesInv «given»).add ?_) oa tbl ht z hz
  intro t
  exact StateT.preservesInv_monadLift _ _

end Handler

end Append

/-- A lookup is the linear combination of the given values in receipt order. -/
theorem Explains.lookup_eq_sum_given {«given» : S → List Handle}
    {tbl : Tbl (fun s => Repr F × G s)} (ht : Explains «given» tbl) (s : S) (h : Handle) :
    (lookup tbl s h).2 =
      ((«given» s).map fun j => (lookup tbl s h).1 j • (lookup tbl s j).2).sum := by
  rw [ht.lookup_eval s h, Repr.eval_eq_sum, ← List.sum_toFinset _ (ht.given_nodup s)]
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr (ht.given_lt s j (List.mem_toFinset.mp hj))
  · intro j _ hj
    have hc : (lookup tbl s h).1 j = 0 := by
      by_contra hc
      exact hj (List.mem_toFinset.mpr (ht.lookup_support s h j hc))
    simp [hc]

/-- Coefficient and value lists extracted in receipt order represent every lookup. -/
theorem Explains.lookup_eq_zipWith {«given» : S → List Handle}
    {tbl : Tbl (fun s => Repr F × G s)} (ht : Explains «given» tbl) (s : S) (h : Handle) :
    (lookup tbl s h).2 =
      (List.zipWith (fun c g => c • g) ((«given» s).map (lookup tbl s h).1)
        ((«given» s).map fun j => (lookup tbl s j).2)).sum := by
  rw [ht.lookup_eq_sum_given s h]
  congr 1
  induction «given» s with
  | nil => rfl
  | cons j js ih => simp

end Invariant

end GroupModel
