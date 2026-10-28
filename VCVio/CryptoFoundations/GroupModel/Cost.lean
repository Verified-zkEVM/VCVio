/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Oracle
public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
import Mathlib.Data.List.GetD

/-! # Group-operation costs and table growth

Equality and auxiliary queries are free. Each group operation appends one entry.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

variable {F S : Type} {σ : Sig S} {ι : Type} {Γ : OracleSpec ι}

/-- Whether a group query appends an entry. -/
@[expose] def Query.isOp : Query F σ → Bool
  | .eq _ _ _ => false
  | _ => true

/-- Addition appends an entry. -/
@[simp] theorem Query.isOp_add (s : S) (a b : Handle) :
    (Query.add (F := F) (σ := σ) s a b).isOp = true := rfl

/-- Scalar multiplication appends an entry. -/
@[simp] theorem Query.isOp_smul (s : S) (c : F) (a : Handle) :
    (Query.smul (σ := σ) s c a).isOp = true := rfl

/-- Equality appends no entry. -/
@[simp] theorem Query.isOp_eq (s : S) (a b : Handle) :
    (Query.eq (F := F) (σ := σ) s a b).isOp = false := rfl

/-- A linear structure map appends an entry. -/
@[simp] theorem Query.isOp_lin (o : σ.Lin) (a : Handle) :
    (Query.lin (F := F) o a).isOp = true := rfl

/-- A bilinear structure map appends an entry. -/
@[simp] theorem Query.isOp_bil (o : σ.Bil) (a b : Handle) :
    (Query.bil (F := F) o a b).isOp = true := rfl

/-- Count group operations, ignoring auxiliary queries. -/
@[expose] def isGroupOp : Query F σ ⊕ ι → Bool := Sum.elim Query.isOp (fun _ => false)

/-- Each group operation costs one; equality is free. -/
@[expose] def unitCost : CostModel (spec F σ) ℕ where
  queryCost t := if t.isOp then 1 else 0

/-- Group-operation cost extended by zero on the auxiliary oracle. -/
@[expose] def unitCostSum (Γ : OracleSpec ι) : CostModel (spec F σ + Γ) ℕ where
  queryCost t := if isGroupOp t then 1 else 0

/-- A structural group-operation budget bounds the accumulated pathwise cost.
The converse fails when an auxiliary oracle has an empty answer type. -/
theorem worstCaseCostBound_unitCostSum {α : Type} {oa : OracleComp (spec F σ + Γ) α}
    {q : ℕ} (h : IsQueryBoundP oa (fun i => isGroupOp i = true) q) :
    WorstCaseCostBound oa (unitCostSum Γ) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [worstCaseCostBound_query_bind_iff]
    intro u z hz
    have hb := (worstCaseCostBound_iff_support_bound _ _ _).mp (ih u (h.2 u)) z hz
    by_cases ht : isGroupOp t = true
    · have hq := h.1.resolve_left (not_not_intro ht)
      simp [unitCostSum, ht] at hb ⊢
      omega
    · simpa only [unitCostSum, ht, Bool.false_eq_true, ↓reduceIte, zero_add] using hb

variable {V : S → Type} {ι' : Type} {spec' : OracleSpec ι'}

/-- Every reachable reply of the game leaves the table unchanged. -/
@[expose] def PreservesTbl (game : QueryImpl Γ (StateT (Tbl V) (OracleComp spec'))) : Prop :=
  ∀ t tbl z, z ∈ support ((game t).run tbl) → z.2 = tbl

/-- Appending preserves all existing entries in every sort. -/
theorem prefix_append [DecidableEq S] (tbl : Tbl V) (s t : S) (v : V s) :
    tbl t <+: append tbl s v t := by
  by_cases h : t = s
  · subst t; simp [append]
  · simp [append, Function.update_of_ne h]

/-- Appending increases any one sort's length by at most one. -/
theorem length_append_le [DecidableEq S] (tbl : Tbl V) (s t : S) (v : V s) :
    (append tbl s v t).length ≤ (tbl t).length + 1 := by
  by_cases h : t = s
  · subst t; simp [append]
  · simp [append, Function.update_of_ne h]

/-- Appending increases the total number of entries by exactly one. -/
theorem sum_length_append [DecidableEq S] [Fintype S] (tbl : Tbl V) (s : S) (v : V s) :
    ∑ t, (append tbl s v t).length = (∑ t, (tbl t).length) + 1 := by
  classical
  have he : (fun t => (append tbl s v t).length) =
      Function.update (fun t => (tbl t).length) s ((tbl s).length + 1) := by
    funext t
    by_cases h : t = s
    · subst t; simp [append]
    · simp [append, Function.update_of_ne h]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ s)]
  rw [Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
  omega

/-- Lifting private-coin queries into table state preserves the table. -/
theorem preservesTbl_coins : PreservesTbl
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tbl V) ProbComp)) := by
  intro t tbl z hz
  have hz' : ∃ y, (y, tbl) = z := by simpa using hz
  obtain ⟨y, rfl⟩ := hz'
  rfl

/-- Prefix extension preserves the value of every old handle. -/
theorem lookup_eq_of_prefix [∀ s, Zero (V s)] {tbl tbl' : Tbl V} (s : S)
    (hp : tbl s <+: tbl' s) (h : Handle) (hh : h < (tbl s).length) :
    lookup tbl' s h = lookup tbl s h := by
  obtain ⟨tail, he⟩ := hp
  simp only [lookup, ← he, List.getD_append _ _ _ _ hh]

section Semantics

/-- A group handler reply either preserves the table or appends exactly one value. -/
theorem impl_table_step [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    (t : Query F σ) (tbl : Tbl V)
    (z : spec F σ t × Tbl V)
    (hz : z ∈ support ((impl M obs (OracleComp spec') t).run tbl)) :
    if t.isOp then ∃ s v, z.2 = append tbl s v else z.2 = tbl := by
  cases t <;>
    simp only [impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet] at hz <;>
    replace hz := (mem_support_pure_iff _ _).mp hz <;>
    subst z
  all_goals first | rfl | exact ⟨_, _, rfl⟩

/-- Each group handler reply preserves the old table as a prefix in every sort. -/
theorem impl_prefix [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    (t : Query F σ) (tbl : Tbl V) (z : spec F σ t × Tbl V)
    (hz : z ∈ support ((impl M obs (OracleComp spec') t).run tbl)) (s : S) :
    tbl s <+: z.2 s := by
  have h := impl_table_step M obs t tbl z hz
  split at h
  · obtain ⟨t, v, hv⟩ := h
    rw [hv]
    exact prefix_append tbl t s v
  · rw [h]

/-- A group handler increases any size functional by its zero-or-one operation charge. -/
theorem impl_size_le [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    (f : Tbl V → ℕ)
    (hf : ∀ tbl s v, f (append tbl s v) ≤ f tbl + 1)
    (t : Query F σ) (tbl : Tbl V) (z : spec F σ t × Tbl V)
    (hz : z ∈ support ((impl M obs (OracleComp spec') t).run tbl)) :
    f z.2 ≤ f tbl + if t.isOp then 1 else 0 := by
  have h := impl_table_step M obs t tbl z hz
  split at h
  · obtain ⟨s, v, hv⟩ := h
    simp [*]
  · simp_all

/-- All initial entries remain a prefix after a run with a table-preserving game. -/
theorem run_prefix [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    (game : QueryImpl Γ (StateT (Tbl V) (OracleComp spec')))
    (hg : PreservesTbl game) {α : Type} (oa : OracleComp (spec F σ + Γ) α)
    (tbl : Tbl V) (z : α × Tbl V) (hz : z ∈ support (run M obs game oa tbl))
    (s : S) : tbl s <+: z.2 s := by
  induction oa using OracleComp.inductionOn generalizing tbl with
  | pure a =>
    simp only [run, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst z
    exact List.prefix_rfl
  | query_bind t k ih =>
    simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hp : tbl s <+: w.2 s := by
      cases t with
      | inl t => exact impl_prefix M obs t tbl w hw s
      | inr t => rw [hg t tbl w hw]
    exact hp.trans (ih w.1 w.2 hz)

/-- A size functional growing by at most one per append grows by at most the budget. -/
theorem run_size_le [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    (game : QueryImpl Γ (StateT (Tbl V) (OracleComp spec')))
    (hg : PreservesTbl game) (f : Tbl V → ℕ)
    (hf : ∀ tbl s v, f (append tbl s v) ≤ f tbl + 1)
    {α : Type} {oa : OracleComp (spec F σ + Γ) α} {q : ℕ}
    (h : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl V) (z : α × Tbl V) (hz : z ∈ support (run M obs game oa tbl)) :
    f z.2 ≤ f tbl + q := by
  apply h.cost_le_of_mem_support_run_simulateQ f ?_ ?_ tbl z hz
  · intro t ht tbl z hz
    cases t with
    | inl t => simpa only [show t.isOp = true from ht, ↓reduceIte] using
        impl_size_le M obs f hf t tbl z hz
    | inr t => simp [isGroupOp] at ht
  · intro t ht tbl z hz
    cases t with
    | inl t =>
      simpa only [show ¬ t.isOp = true from ht, Bool.false_eq_true, ↓reduceIte, add_zero] using
        impl_size_le M obs f hf t tbl z hz
    | inr t => simp [hg t tbl z hz]

/-- Each sort has at most the operation budget many new entries. -/
theorem run_length_le [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    (game : QueryImpl Γ (StateT (Tbl V) (OracleComp spec')))
    (hg : PreservesTbl game) {α : Type} {oa : OracleComp (spec F σ + Γ) α} {q : ℕ}
    (h : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl V) (z : α × Tbl V) (hz : z ∈ support (run M obs game oa tbl)) (s : S) :
    (z.2 s).length ≤ (tbl s).length + q :=
  run_size_le M obs game hg (fun tbl => (tbl s).length)
    (fun tbl t v => length_append_le tbl t s v) h tbl z hz

/-- The total table size is bounded by its initial size plus the operation budget. -/
theorem run_sum_length_le [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    [Fintype S]
    (game : QueryImpl Γ (StateT (Tbl V) (OracleComp spec')))
    (hg : PreservesTbl game) {α : Type} {oa : OracleComp (spec F σ + Γ) α} {q : ℕ}
    (h : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl V) (z : α × Tbl V) (hz : z ∈ support (run M obs game oa tbl)) :
    ∑ s, (z.2 s).length ≤ (∑ s, (tbl s).length) + q :=
  run_size_le M obs game hg (fun tbl => ∑ s, (tbl s).length)
    (fun tbl s v => (sum_length_append tbl s v).le) h tbl z hz

/-- A group step increases the total size by exactly its operation charge. -/
theorem impl_sum_length [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    [Fintype S] (t : Query F σ) (tbl : Tbl V)
    (z : spec F σ t × Tbl V)
    (hz : z ∈ support ((impl M obs (OracleComp spec') t).run tbl)) :
    ∑ s, (z.2 s).length = (∑ s, (tbl s).length) + if t.isOp then 1 else 0 := by
  have h := impl_table_step M obs t tbl z hz
  split at h
  · obtain ⟨s, v, hv⟩ := h
    simp [*, sum_length_append]
  · simp_all

/-- Private-coin runs preserve all initial entries. -/
theorem runGen_prefix [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    {α : Type} (oa : OracleComp (genSpec F σ) α)
    (tbl : Tbl V) (z : α × Tbl V) (hz : z ∈ support (runGen M obs oa tbl)) (s : S) :
    tbl s <+: z.2 s :=
  run_prefix M obs _ preservesTbl_coins oa tbl z hz s

/-- Private-coin runs add at most the operation budget in any sort. -/
theorem runGen_length_le [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    {α : Type} {oa : OracleComp (genSpec F σ) α} {q : ℕ}
    (h : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl V) (z : α × Tbl V) (hz : z ∈ support (runGen M obs oa tbl)) (s : S) :
    (z.2 s).length ≤ (tbl s).length + q :=
  run_length_le M obs _ preservesTbl_coins h tbl z hz s

/-- Private-coin runs have total size at most the initial size plus the operation budget. -/
theorem runGen_sum_length_le [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    [Fintype S]
    {α : Type} {oa : OracleComp (genSpec F σ) α} {q : ℕ}
    (h : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl V) (z : α × Tbl V) (hz : z ∈ support (runGen M obs oa tbl)) :
    ∑ s, (z.2 s).length ≤ (∑ s, (tbl s).length) + q :=
  run_sum_length_le M obs _ preservesTbl_coins h tbl z hz

end Semantics

end GroupModel
