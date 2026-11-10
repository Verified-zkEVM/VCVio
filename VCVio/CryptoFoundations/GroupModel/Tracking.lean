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
@[expose] def Coeffs.eval {F G : Type} [CommSemiring F] [AddCommMonoid G] [Module F G]
    (r : Coeffs F) (tbl : List (Coeffs F × G)) : G := evRepr (tbl.map Prod.snd) r

/-- Inputs carry the basis representation at their own handle. -/
@[expose] def trackInputs {F S : Type} [Zero F] [One F] {G : S → Type}
    (xs : (s : S) → List (G s)) : Tbl (fun s => Coeffs F × G s) :=
  fun s => (xs s).mapIdx fun i x => (Pi.single i 1, x)

/-- Every entry is explained by the given handles, which are distinct in each sort. -/
structure Explains {F S : Type} [CommSemiring F] {G : S → Type}
    [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    («given» : S → List Handle) (tbl : Tbl (fun s => Coeffs F × G s)) : Prop where
  /-- Every given handle refers to an existing table entry. -/
  given_lt : ∀ s h, h ∈ «given» s → h < (tbl s).length
  /-- Each given entry carries the basis vector at its own handle. -/
  repr_given : ∀ s h, h ∈ «given» s → (lookup tbl s h).1 = Pi.single h 1
  /-- Every nonzero coefficient refers to a given handle. -/
  support_subset : ∀ s e, e ∈ tbl s → ∀ h, e.1 h ≠ 0 → h ∈ «given» s
  /-- Every entry evaluates to its accompanying module element. -/
  eq_eval : ∀ s e, e ∈ tbl s → e.2 = e.1.eval (tbl s)
  /-- The given handles of each sort are distinct. -/
  given_nodup : ∀ s, («given» s).Nodup

section Evaluation

variable {F G : Type} [CommSemiring F] [AddCommMonoid G] [Module F G]

/-- Evaluation as a finite sum over table indices. -/
theorem Coeffs.eval_eq_sum (r : Coeffs F) (tbl : List (Coeffs F × G)) :
    r.eval tbl = ∑ i ∈ Finset.range tbl.length, r i • (tbl.getD i 0).2 := by
  simp only [Coeffs.eval, evRepr_apply, List.length_map]
  congr 1
  ext i
  rw [show (0 : G) = Prod.snd (0 : Coeffs F × G) from rfl, List.getD_map]

/-- Evaluation respects addition of coefficient functions. -/
theorem Coeffs.eval_add (r t : Coeffs F) (tbl : List (Coeffs F × G)) :
    (r + t).eval tbl = r.eval tbl + t.eval tbl := map_add _ _ _

/-- Evaluation respects scalar multiplication of coefficient functions. -/
theorem Coeffs.eval_smul (c : F) (r : Coeffs F) (tbl : List (Coeffs F × G)) :
    (c • r).eval tbl = c • r.eval tbl := map_smul _ _ _

/-- The zero representation evaluates to zero. -/
@[simp] theorem Coeffs.eval_zero (tbl : List (Coeffs F × G)) : (0 : Coeffs F).eval tbl = 0 :=
  map_zero _

/-- Evaluation of a basis representation reads the corresponding value, or zero past the end of
the table. -/
theorem Coeffs.eval_single (tbl : List (Coeffs F × G)) (h : Handle) :
    Coeffs.eval (Pi.single h (1 : F)) tbl = (tbl.getD h 0).2 := by
  rw [Coeffs.eval, evRepr_single, show (0 : G) = Prod.snd (0 : Coeffs F × G) from rfl,
    List.getD_map]

/-- Appending a value does not affect a representation with zero fresh coefficient. -/
theorem Coeffs.eval_append (r : Coeffs F) (tbl : List (Coeffs F × G)) (e : Coeffs F × G)
    (hr : r tbl.length = 0) : r.eval (tbl ++ [e]) = r.eval tbl := by
  simp only [Coeffs.eval_eq_sum, List.length_append, List.length_singleton, Finset.sum_range_succ]
  rw [hr, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]

end Evaluation

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
    rw [Coeffs.eval_single]
    simp [trackInputs, hi]
  · intro s
    exact List.nodup_range

/-- All lookups, including invalid handles, have support among the given handles. -/
theorem Explains.lookup_support {«given» : S → List Handle} {tbl : Tbl (fun s => Coeffs F × G s)}
    (ht : Explains «given» tbl) (s : S) (h j : Handle) (hj : (lookup tbl s h).1 j ≠ 0) :
    j ∈ «given» s := by
  by_cases hh : h < (tbl s).length
  · apply ht.support_subset s _ _ j hj
    rw [lookup, List.getD_eq_getElem _ _ hh]
    exact List.getElem_mem _
  · simp [lookup_eq_zero tbl s h (Nat.le_of_not_gt hh)] at hj

/-- Every lookup is the value of its representation, also at invalid handles. -/
theorem Explains.lookup_eval {«given» : S → List Handle} {tbl : Tbl (fun s => Coeffs F × G s)}
    (ht : Explains «given» tbl) (s : S) (h : Handle) :
    (lookup tbl s h).2 = (lookup tbl s h).1.eval (tbl s) := by
  by_cases hh : h < (tbl s).length
  · apply ht.eq_eval s
    rw [lookup, List.getD_eq_getElem _ _ hh]
    exact List.getElem_mem _
  · simp [lookup_eq_zero tbl s h (Nat.le_of_not_gt hh)]

/-- No explained representation uses the next free table handle. -/
theorem Explains.fresh_zero {«given» : S → List Handle}
    {tbl : Tbl (fun s => Coeffs F × G s)} (ht : Explains «given» tbl)
    (s : S) (r : Coeffs F) (hr : ∀ j, r j ≠ 0 → j ∈ «given» s) :
    r (tbl s).length = 0 := by
  by_contra h
  exact (Nat.lt_irrefl _ (ht.given_lt s _ (hr _ h)))

section Append

variable [DecidableEq S]

/-- Appending an explained element preserves the basis and the invariant. -/
theorem Explains.append {«given» : S → List Handle} {tbl : Tbl (fun s => Coeffs F × G s)}
    (ht : Explains «given» tbl) (s : S) (e : Coeffs F × G s)
    (hs : ∀ j, e.1 j ≠ 0 → j ∈ «given» s) (he : e.2 = e.1.eval (tbl s)) :
    Explains «given» (GroupModel.append tbl s e) := by
  have old_eval (t : S) (r : Coeffs F) (hr : ∀ j, r j ≠ 0 → j ∈ «given» t) :
      r.eval (GroupModel.append tbl s e t) = r.eval (tbl t) := by
    by_cases hts : t = s
    · subst t
      simp only [GroupModel.append, Function.update_self]
      exact Coeffs.eval_append _ _ _ (ht.fresh_zero _ _ hr)
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
    StateT (Tbl (fun s => Coeffs F × G s)) m Handle := fun tbl =>
  (push s (Pi.single (tbl s).length 1, g)).run tbl

/-- Receiving a new basis element extends the list of distinct given handles. -/
theorem Explains.pushGiven {«given» : S → List Handle} {tbl : Tbl (fun s => Coeffs F × G s)}
    (ht : Explains «given» tbl) (s : S) (g : G s) :
    Explains (Function.update «given» s («given» s ++ [(tbl s).length]))
      (GroupModel.append tbl s (Pi.single (tbl s).length 1, g)) := by
  let h := (tbl s).length
  let e : Coeffs F × G s := (Pi.single h 1, g)
  have fresh : h ∉ «given» s := fun hh => Nat.lt_irrefl _ (ht.given_lt s h hh)
  have old_eval (t : S) (r : Coeffs F) (hr : ∀ j, r j ≠ 0 → j ∈ «given» t) :
      r.eval (GroupModel.append tbl s e t) = r.eval (tbl t) := by
    by_cases hts : t = s
    · subst t
      simp only [GroupModel.append, Function.update_self]
      exact Coeffs.eval_append _ _ _ (ht.fresh_zero _ _ hr)
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
      · rw [Coeffs.eval_single]
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
    {tbl : Tbl (fun s => Coeffs F × G s)} (ht : Explains «given» tbl) (s : S) (g : G s)
    (z : Handle × Tbl (fun s => Coeffs F × G s))
    (hz : z ∈ support ((pushGiven s g : StateT _ ProbComp Handle).run tbl)) :
    Explains (Function.update «given» s («given» s ++ [z.1])) z.2 := by
  have hz' : z = ((tbl s).length, GroupModel.append tbl s (Pi.single (tbl s).length 1, g)) := by
    simpa [pushGiven, push, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StateT.run] using hz
  subst z
  exact ht.pushGiven s g

/-- Generic module operations preserve explanations over the existing given handles, for every
observation and in any lawful monad whose support is lawful. -/
theorem impl_tracking_preservesInv {U : S → Type} [∀ s, DecidableEq (U s)]
    {obs : (s : S) → Coeffs F × G s → U s} {m : Type → Type} [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m] («given» : S → List Handle) :
    QueryImpl.PreservesInv (impl (tracking (Model.discrete G)) obs m)
      (Explains (F := F) «given») := by
  intro q tbl ht z hz
  cases q with
  | add s a b =>
    simp only [impl, push, StateT.run_modifyGet, MonadAttach.mem_support] at hz
    obtain rfl := LawfulMonadAttach.eq_of_canReturn_pure hz
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
      rw [Coeffs.eval_add, ← ht.lookup_eval s a, ← ht.lookup_eval s b]
  | smul s c a =>
    simp only [impl, push, StateT.run_modifyGet, MonadAttach.mem_support] at hz
    obtain rfl := LawfulMonadAttach.eq_of_canReturn_pure hz
    apply ht.append
    · intro j hj
      apply ht.lookup_support s a j
      intro ha
      exact hj (by simp [ha])
    · change c • (lookup tbl s a).2 = (c • (lookup tbl s a).1).eval (tbl s)
      rw [Coeffs.eval_smul, ← ht.lookup_eval s a]
  | eq s a b =>
    simp only [impl, StateT.run_bind, StateT.run_get, pure_bind, MonadAttach.mem_support] at hz
    obtain rfl := LawfulMonadAttach.eq_of_canReturn_pure hz
    exact ht
  | lin o a => exact o.elim
  | bil o a b => exact o.elim

/-- Every reachable table of a generic run, under any observation, retains explanations over the
given handles and extends the input table. -/
theorem explains_of_mem_support_runGen {U : S → Type} [∀ s, DecidableEq (U s)]
    {obs : (s : S) → Coeffs F × G s → U s} {«given» : S → List Handle}
    {tbl : Tbl (fun s => Coeffs F × G s)} (ht : Explains «given» tbl) {α : Type}
    (oa : OracleComp (genSpec F (discreteSig S)) α)
    (z : α × Tbl (fun s => Coeffs F × G s))
    (hz : z ∈ support (runGen (tracking (Model.discrete G)) obs oa tbl)) :
    Explains «given» z.2 ∧ Tbl.Extends tbl z.2 := by
  refine ⟨?_, runGen_extends _ obs oa tbl z hz⟩
  apply simulateQ_run_preservesInv _ _
    ((impl_tracking_preservesInv «given»).add ?_) oa tbl ht z hz
  intro t
  exact StateT.preservesInv_monadLift _ _

end Append

/-- A lookup is the linear combination of the given values, summed in the order of `given`. -/
theorem Explains.lookup_eq_sum_given {«given» : S → List Handle}
    {tbl : Tbl (fun s => Coeffs F × G s)} (ht : Explains «given» tbl) (s : S) (h : Handle) :
    (lookup tbl s h).2 =
      ((«given» s).map fun j => (lookup tbl s h).1 j • (lookup tbl s j).2).sum := by
  rw [ht.lookup_eval s h, Coeffs.eval_eq_sum, ← List.sum_toFinset _ (ht.given_nodup s)]
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr (ht.given_lt s j (List.mem_toFinset.mp hj))
  · intro j _ hj
    have hc : (lookup tbl s h).1 j = 0 := by
      by_contra hc
      exact hj (List.mem_toFinset.mpr (ht.lookup_support s h j hc))
    simp [hc]

/-- Coefficient and value lists read off in the order of `given` represent every lookup. -/
theorem Explains.lookup_eq_zipWith {«given» : S → List Handle}
    {tbl : Tbl (fun s => Coeffs F × G s)} (ht : Explains «given» tbl) (s : S) (h : Handle) :
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
