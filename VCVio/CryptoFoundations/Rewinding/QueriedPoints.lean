/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.Rewinding.Finder

/-!
# A sound finder queries every point it vouches for

Run a finder against a fixed acceptance function while recording the queried challenge vectors
(`Rewinding.logCounted`). Along any possible run, the answers depend only on the acceptance
function's values at the recorded vectors (`Rewinding.mem_support_logCounted_of_eqOn`). So a finder
whose outputs are sound for every acceptance function (`Rewinding.IsFinder.sound`) has queried every
point of a returned output at which soundness requires acceptance: otherwise rejecting at that point
would leave the run possible and make its output unsound
(`Rewinding.IsFinder.mem_log_of_mem_support`).

Recovering transcripts from a cache of the finder's runs therefore needs no replay.
-/

public section

open OracleComp OracleSpec

namespace Rewinding

variable {Q : Type}

/-- Answer an acceptance query from a fixed function, record the query, and charge one complete
run. -/
@[expose] def logCounted (g : Q → Bool) :
    QueryImpl (rerunSpec Q Bool) (StateT (Set Q × ℕ) ProbComp) :=
  fun q => do
    modify fun s => (insert q s.1, s.2 + 1)
    pure (g q)

/-- The record of queried vectors only grows. -/
theorem log_subset_of_mem_support_logCounted (g : Q → Bool) {β : Type}
    (oa : OracleComp (unifSpec + rerunSpec Q Bool) β) (s : Set Q × ℕ) (z : β × (Set Q × ℕ))
    (hz : z ∈ support ((simulateQ (coins (S := Set Q × ℕ) + logCounted g) oa).run s)) :
    s.1 ⊆ z.2.1 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact subset_rfl
  | query_bind q k ih =>
    cases q with
    | inl n =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl, StateT.run_bind,
        coins, QueryImpl.liftTarget_apply_run, QueryImpl.ofLift_apply, bind_map_left,
        mem_support_bind_iff] at hz
      obtain ⟨u, -, hz⟩ := hz
      exact ih u s hz
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr, StateT.run_bind,
        logCounted, StateT.run_modify, StateT.run_pure, pure_bind] at hz
      exact (Set.subset_insert q s.1).trans (ih (g q) _ hz)

/-- Along a possible run, the answers depend only on the acceptance function's values at the
recorded vectors: the run stays possible against any function agreeing with it there. -/
theorem mem_support_logCounted_of_eqOn (g g' : Q → Bool) {β : Type}
    (oa : OracleComp (unifSpec + rerunSpec Q Bool) β) (s : Set Q × ℕ) (z : β × (Set Q × ℕ))
    (hz : z ∈ support ((simulateQ (coins (S := Set Q × ℕ) + logCounted g) oa).run s))
    (hg : ∀ q ∈ z.2.1, g' q = g q) :
    z ∈ support ((simulateQ (coins (S := Set Q × ℕ) + logCounted g') oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simpa only [simulateQ_pure] using hz
  | query_bind q k ih =>
    cases q with
    | inl n =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl, StateT.run_bind,
        coins, QueryImpl.liftTarget_apply_run, QueryImpl.ofLift_apply, bind_map_left,
        mem_support_bind_iff] at hz ⊢
      obtain ⟨u, hu, hz⟩ := hz
      exact ⟨u, hu, ih u s hz⟩
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr, StateT.run_bind,
        logCounted, StateT.run_modify, StateT.run_pure, pure_bind] at hz ⊢
      have hq : q ∈ z.2.1 :=
        log_subset_of_mem_support_logCounted g _ _ z hz (Set.mem_insert q s.1)
      rw [hg q hq]
      exact ih (g q) _ hz

/-- Forgetting the record leaves the counted run. -/
theorem map_run_simulateQ_logCounted (g : Q → Bool) {β : Type}
    (oa : OracleComp (unifSpec + rerunSpec Q Bool) β) (L : Set Q) (n : ℕ) :
    (fun z => (z.1, z.2.2)) <$> (simulateQ (coins (S := Set Q × ℕ) + logCounted g) oa).run (L, n) =
      (simulateQ (coins (S := ℕ) + counted g) oa).run n := by
  induction oa using OracleComp.inductionOn generalizing L n with
  | pure a => simp
  | query_bind q k ih =>
    cases q with
    | inl t =>
      simp only [coins] at ih
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl, StateT.run_bind,
        coins, QueryImpl.liftTarget_apply_run, QueryImpl.ofLift_apply, bind_map_left, map_bind, ih]
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr, StateT.run_bind,
        logCounted, counted, StateT.run_modify, StateT.run_pure, pure_bind]
      exact ih (g q) _ _

variable {R : Type} {C : R → Type}

/-- A sound finder queries every point of a returned output at which soundness requires
acceptance. -/
theorem IsFinder.mem_log_of_mem_support [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ENNReal}
    (h : IsFinder good find κ T) {m : ℕ} (points : Out → Fin m → ((r : R) → C r))
    (hpts : ∀ f o, good f o → ∀ i, f (points o i) = true) (g : ((r : R) → C r) → Bool)
    (z : Option Out × (Set ((r : R) → C r) × ℕ))
    (hz : z ∈ support
      ((simulateQ (coins (S := Set ((r : R) → C r) × ℕ) + logCounted g) find).run (∅, 0)))
    (o : Out) (ho : z.1 = some o) (i : Fin m) : points o i ∈ z.2.1 := by
  classical
  by_contra hmiss
  let g' := Function.update g (points o i) false
  have hagree : ∀ q ∈ z.2.1, g' q = g q := by
    intro q hq
    have hne : q ≠ points o i := fun h => hmiss (h ▸ hq)
    simp only [g', Function.update_of_ne hne]
  have hz' := mem_support_logCounted_of_eqOn g g' find _ z hz hagree
  have hcount : (z.1, z.2.2) ∈ support (runFinder find g') := by
    rw [runFinder, ← map_run_simulateQ_logCounted g' find ∅ 0, support_map]
    exact ⟨z, hz', rfl⟩
  have hacc := hpts g' o (h.sound g' _ hcount o ho) i
  simp [g'] at hacc

end Rewinding
