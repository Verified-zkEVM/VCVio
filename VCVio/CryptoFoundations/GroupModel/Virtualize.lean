/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Cost
import Mathlib.Data.List.GetD

/-! # Virtual handles for nested generic computations

A private translation table restricts an adversary to its own handles. Out-of-range handles
translate to a designated zero entry of the surrounding computation's table.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

variable {F S : Type} {σ : Sig S} {V : S → Type}

/-- Translate group handles, recording each fresh handle privately, and forward private coins. -/
@[expose] def virtualizeImpl [DecidableEq S] (z : S → Handle) :
    QueryImpl (genSpec F σ) (StateT (Tbl (fun _ : S => Handle))
      (OracleComp (genSpec F σ)))
  | .inl (.add s a b) => fun τ => do
      let h ← (genSpec F σ).query (.inl (.add s ((τ s).getD a (z s)) ((τ s).getD b (z s))))
      pure ((τ s).length, append τ s h)
  | .inl (.smul s c a) => fun τ => do
      let h ← (genSpec F σ).query (.inl (.smul s c ((τ s).getD a (z s))))
      pure ((τ s).length, append τ s h)
  | .inl (.eq s a b) => fun τ => do
      let b ← (genSpec F σ).query (.inl (.eq s ((τ s).getD a (z s)) ((τ s).getD b (z s))))
      pure (b, τ)
  | .inl (.lin o a) => fun τ => do
      let h ← (genSpec F σ).query (.inl (.lin o ((τ (σ.lsrc o)).getD a (z (σ.lsrc o)))))
      pure ((τ (σ.ltgt o)).length, append τ (σ.ltgt o) h)
  | .inl (.bil o a b) => fun τ => do
      let h ← (genSpec F σ).query (.inl (.bil o ((τ (σ.src₁ o)).getD a (z (σ.src₁ o)))
        ((τ (σ.src₂ o)).getD b (z (σ.src₂ o)))))
      pure ((τ (σ.tgt o)).length, append τ (σ.tgt o) h)
  | .inr n => fun τ => do
      let b ← (genSpec F σ).query (.inr n)
      pure (b, τ)

/-- Run a generic computation using a private translation from its handles to outer handles. -/
@[expose] def virtualize [DecidableEq S] (z : S → Handle) {α : Type}
    (A : OracleComp (genSpec F σ) α) :
    StateT (Tbl (fun _ : S => Handle)) (OracleComp (genSpec F σ)) α :=
  simulateQ (virtualizeImpl z) A

/-- The adversary's entire table, read through its handle translation. -/
@[expose] def readBack [∀ s, Zero (V s)] (τ : Tbl (fun _ : S => Handle))
    (T : Tbl V) : Tbl V := fun s => (τ s).map (lookup T s)

/-- All translated handles and designated zero handles are in range, and the latter store zero. -/
@[expose] def WellFormed [∀ s, Zero (V s)] (z : S → Handle)
    (τ : Tbl (fun _ : S => Handle)) (T : Tbl V) : Prop :=
  ∀ s, (∀ h ∈ τ s, h < (T s).length) ∧ z s < (T s).length ∧ lookup T s (z s) = 0

/-- Reading through a translation agrees with lookup, including out-of-range adversary handles. -/
theorem lookup_readBack [∀ s, Zero (V s)] {z : S → Handle}
    {τ : Tbl (fun _ : S => Handle)} {T : Tbl V} (hw : WellFormed z τ T)
    (s : S) (h : Handle) :
    lookup (readBack τ T) s h = lookup T s ((τ s).getD h (z s)) := by
  change ((τ s).map (lookup T s)).getD h 0 = _
  rw [← (hw s).2.2]
  exact List.getD_map (τ s) (z s) (lookup T s)

private theorem readBack_prefix [∀ s, Zero (V s)] {z : S → Handle}
    {τ : Tbl (fun _ : S => Handle)} {T T' : Tbl V} (hw : WellFormed z τ T)
    (hp : ∀ s, T s <+: T' s) : readBack τ T' = readBack τ T := by
  funext s
  apply List.map_congr_left
  intro h hh
  exact lookup_eq_of_prefix s (hp s) h ((hw s).1 h hh)

private theorem wellFormed_append [DecidableEq S] [∀ s, Zero (V s)]
    {z : S → Handle} {τ : Tbl (fun _ : S => Handle)} {T : Tbl V}
    (hw : WellFormed z τ T) (s : S) (v : V s) :
    WellFormed z (append τ s (T s).length) (append T s v) := by
  intro t
  have hp := prefix_append T s t v
  refine ⟨?_, lt_of_lt_of_le (hw t).2.1 hp.length_le, ?_⟩
  · intro h hh
    by_cases ht : t = s
    · subst t
      simp only [append, Function.update_self, List.mem_append, List.mem_singleton] at hh
      simp only [append, Function.update_self, List.length_append, List.length_singleton]
      rcases hh with hh | rfl
      · exact Nat.lt_succ_of_lt ((hw s).1 h hh)
      · exact Nat.lt_succ_self _
    · have hh' : h ∈ τ t := by simpa [append, Function.update_of_ne ht] using hh
      exact lt_of_lt_of_le ((hw t).1 h hh') hp.length_le
  · rw [lookup_eq_of_prefix t hp _ (hw t).2.1, (hw t).2.2]

private theorem readBack_append [DecidableEq S] [∀ s, Zero (V s)]
    {z : S → Handle} {τ : Tbl (fun _ : S => Handle)} {T : Tbl V}
    (hw : WellFormed z τ T) (s : S) (v : V s) :
    readBack (append τ s (T s).length) (append T s v) = append (readBack τ T) s v := by
  have hp := readBack_prefix hw (fun t => prefix_append T s t v)
  funext t
  by_cases ht : t = s
  · subst t
    simpa [readBack, append, lookup, List.map_append] using
      congrArg (fun R : Tbl V => R s ++ [v]) hp
  · simpa [readBack, append, Function.update_of_ne ht] using congrFun hp t

private theorem runGen_bind [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    {α β : Type} (A : OracleComp (genSpec F σ) α)
    (k : α → OracleComp (genSpec F σ) β) (T : Tbl V) :
    runGen M obs (A >>= k) T =
      (runGen M obs A T >>= fun r => runGen M obs (k r.1) r.2) := by
  simp only [runGen, run, simulateQ_bind, StateT.run_bind]

private theorem runGen_virtualize_bind [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    (z : S → Handle) {α β : Type} (A : OracleComp (genSpec F σ) α)
    (k : α → OracleComp (genSpec F σ) β) (τ : Tbl (fun _ : S => Handle)) (T : Tbl V) :
    runGen M obs ((virtualize z (A >>= k)).run τ) T =
      (runGen M obs ((virtualize z A).run τ) T >>= fun r =>
        runGen M obs ((virtualize z (k r.1.1)).run r.1.2) r.2) := by
  simp only [runGen, run, virtualize, simulateQ_bind, StateT.run_bind]

/-- A single virtualized query preserves valid translated handles and the designated zero. -/
theorem wellFormed_runGen_virtualizeImpl [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    {z : S → Handle} {τ : Tbl (fun _ : S => Handle)} {T : Tbl V}
    (hw : WellFormed z τ T) (t : (genSpec F σ).Domain)
    (r : ((genSpec F σ).Range t × Tbl (fun _ : S => Handle)) × Tbl V)
    (hr : r ∈ support (runGen M obs ((virtualizeImpl z t).run τ) T)) :
    WellFormed z r.1.2 r.2 := by
  rcases t with t | n
  · cases t <;>
      change r ∈ support (pure _ : ProbComp _) at hr <;>
      rw [mem_support_pure_iff] at hr <;>
      subst r
    all_goals first | exact wellFormed_append hw _ _ | exact hw
  · simp only [virtualizeImpl, StateT.run] at hr
    simp only [runGen, run, simulateQ_bind, simulateQ_pure, simulateQ_spec_query,
      StateT.run_bind, StateT.run_pure, QueryImpl.add_apply_inr] at hr
    change r ∈ support ((do
      let b ← (liftM (unifSpec.query n) : ProbComp _)
      pure (b, T)) >>= fun w => pure ((w.1, τ), w.2)) at hr
    simp only [bind_assoc, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨b, _, hr⟩ := hr
    subst r
    exact hw

private theorem virtualize_step_readBack [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    {z : S → Handle} {τ : Tbl (fun _ : S => Handle)} {T : Tbl V}
    (hw : WellFormed z τ T) (t : (genSpec F σ).Domain) :
    runGen M obs (liftM ((genSpec F σ).query t)) (readBack τ T) =
      (fun r => (r.1.1, readBack r.1.2 r.2)) <$>
        runGen M obs ((virtualizeImpl z t).run τ) T := by
  rcases t with t | n
  · cases t with
    | add s a b =>
      change (pure ((readBack τ T s).length,
        append (readBack τ T) s
          (lookup (readBack τ T) s a + lookup (readBack τ T) s b)) : ProbComp _) =
          (fun r => (r.1.1, readBack r.1.2 r.2)) <$>
            pure (((τ s).length, append τ s (T s).length),
              append T s (lookup T s ((τ s).getD a (z s)) + lookup T s ((τ s).getD b (z s))))
      simp only [map_pure, lookup_readBack hw, readBack_append hw]
      simp only [readBack, List.length_map]
    | smul s c a =>
      change (pure ((readBack τ T s).length,
        append (readBack τ T) s (c • lookup (readBack τ T) s a)) : ProbComp _) =
          (fun r => (r.1.1, readBack r.1.2 r.2)) <$>
            pure (((τ s).length, append τ s (T s).length),
              append T s (c • lookup T s ((τ s).getD a (z s))))
      simp only [map_pure, lookup_readBack hw, readBack_append hw]
      simp only [readBack, List.length_map]
    | lin o a =>
      change (pure ((readBack τ T (σ.ltgt o)).length,
        append (readBack τ T) (σ.ltgt o)
          (M.lin o (lookup (readBack τ T) (σ.lsrc o) a))) : ProbComp _) =
          (fun r => (r.1.1, readBack r.1.2 r.2)) <$>
            pure (((τ (σ.ltgt o)).length, append τ (σ.ltgt o) (T (σ.ltgt o)).length),
              append T (σ.ltgt o)
                (M.lin o (lookup T (σ.lsrc o) ((τ (σ.lsrc o)).getD a (z (σ.lsrc o))))))
      simp only [map_pure, lookup_readBack hw, readBack_append hw]
      simp only [readBack, List.length_map]
    | bil o a b =>
      change (pure ((readBack τ T (σ.tgt o)).length,
        append (readBack τ T) (σ.tgt o)
          (M.bil o (lookup (readBack τ T) (σ.src₁ o) a)
            (lookup (readBack τ T) (σ.src₂ o) b))) : ProbComp _) =
          (fun r => (r.1.1, readBack r.1.2 r.2)) <$>
            pure (((τ (σ.tgt o)).length, append τ (σ.tgt o) (T (σ.tgt o)).length),
              append T (σ.tgt o)
                (M.bil o (lookup T (σ.src₁ o) ((τ (σ.src₁ o)).getD a (z (σ.src₁ o))))
                  (lookup T (σ.src₂ o) ((τ (σ.src₂ o)).getD b (z (σ.src₂ o))))))
      simp only [map_pure, lookup_readBack hw, readBack_append hw]
      simp only [readBack, List.length_map]
    | eq s a b =>
      change (pure (decide (obs s (lookup (readBack τ T) s a) =
        obs s (lookup (readBack τ T) s b)), readBack τ T) : ProbComp _) =
          (fun r => (r.1.1, readBack r.1.2 r.2)) <$>
            pure ((decide (obs s (lookup T s ((τ s).getD a (z s))) =
              obs s (lookup T s ((τ s).getD b (z s)))), τ), T)
      simp only [map_pure, lookup_readBack hw]
  · simp only [virtualizeImpl, StateT.run]
    simp only [runGen, run, simulateQ_bind, simulateQ_pure, simulateQ_spec_query,
      StateT.run_bind, StateT.run_pure, QueryImpl.add_apply_inr]
    change (do let b ← (liftM (unifSpec.query n) : ProbComp _)
               pure (b, readBack τ T)) =
      (fun r => (r.1.1, readBack r.1.2 r.2)) <$>
        ((do let b ← (liftM (unifSpec.query n) : ProbComp _)
             pure (b, T)) >>= fun w => pure ((w.1, τ), w.2))
    simp only [bind_assoc, pure_bind, map_bind, map_pure]

/-- Every reachable virtualized run preserves the translation and zero-handle invariant. -/
theorem wellFormed_runGen_virtualize [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    {z : S → Handle} {α : Type} (A : OracleComp (genSpec F σ) α)
    {τ : Tbl (fun _ : S => Handle)} {T : Tbl V} (hw : WellFormed z τ T)
    (r : (α × Tbl (fun _ : S => Handle)) × Tbl V)
    (hr : r ∈ support (runGen M obs ((virtualize z A).run τ) T)) :
    WellFormed z r.1.2 r.2 := by
  induction A using OracleComp.inductionOn generalizing τ T with
  | pure a =>
    simp only [virtualize, simulateQ_pure, StateT.run_pure, runGen, run,
      simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact hw
  | query_bind t k ih =>
    rw [runGen_virtualize_bind, mem_support_bind_iff] at hr
    obtain ⟨w, hw', hr⟩ := hr
    have hs : WellFormed z w.1.2 w.2 := wellFormed_runGen_virtualizeImpl M obs hw t w
      (by simpa only [virtualize, simulateQ_spec_query] using hw')
    exact ih w.1.1 hs hr

/-- Reading back a virtualized run gives exactly the direct computation and its full final table. -/
theorem runGen_virtualize [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (M : Model F σ V) (obs : (s : S) → V s → U s)
    {z : S → Handle} {α : Type} (A : OracleComp (genSpec F σ) α)
    {τ : Tbl (fun _ : S => Handle)} {T : Tbl V} (hw : WellFormed z τ T) :
    runGen M obs A (readBack τ T) =
      (fun r => (r.1.1, readBack r.1.2 r.2)) <$>
        runGen M obs ((virtualize z A).run τ) T := by
  induction A using OracleComp.inductionOn generalizing τ T with
  | pure a => simp [virtualize, runGen, run]
  | query_bind t k ih =>
    rw [runGen_bind, runGen_virtualize_bind, virtualize_step_readBack M obs hw t]
    simp only [virtualize, simulateQ_spec_query, bind_map_left, map_bind]
    apply bind_congr_of_forall_mem_support
    intro w hw'
    exact ih w.1.1 (wellFormed_runGen_virtualizeImpl M obs hw t w hw')

/-- Virtualization preserves every group-operation budget; equality and coins remain free. -/
theorem isQueryBoundP_virtualize [DecidableEq S] (z : S → Handle)
    {α : Type} {A : OracleComp (genSpec F σ) α} {q : ℕ}
    (h : IsQueryBoundP A (fun i => isGroupOp i = true) q)
    (τ : Tbl (fun _ : S => Handle)) :
    IsQueryBoundP ((virtualize z A).run τ) (fun i => isGroupOp i = true) q := by
  apply h.simulateQ_run_of_step (impl := virtualizeImpl z) ?_ ?_ τ
  · rintro (t | n) ht τ
    · cases t <;> simp_all [virtualizeImpl, StateT.run, isGroupOp, Query.isOp]
    · simp [isGroupOp] at ht
  · rintro (t | n) ht τ
    · cases t <;> simp_all [virtualizeImpl, StateT.run, isGroupOp, Query.isOp]
    · simp [virtualizeImpl, StateT.run, isGroupOp]

end GroupModel
