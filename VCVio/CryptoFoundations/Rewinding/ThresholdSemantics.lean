/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Threshold

/-!
# Interpretation of recursive threshold extraction

Threshold collection commutes with monad morphisms. Interpreting an acceptance oracle therefore
preserves the recursive structure, and discarding its counter gives the ordinary Boolean-table
interpretation.
-/

public section

open OracleComp OracleSpec

namespace Rewinding

/-- Collecting successful children commutes with monad morphisms. -/
theorem map_collectChildren {m n : Type → Type} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (φ : m →ᵐ n) {C W : Type}
    (sample : (j : ℕ) → m (Fin (j + 1))) (child : C → m (Option W)) (N : ℕ) :
    ∀ (r : ℕ) (pool : List C), pool.length = N →
      φ (collectChildren sample child r pool) =
        collectChildren (fun j => φ (sample j)) (fun c => φ (child c)) r pool := by
  induction N with
  | zero =>
    intro r pool hp
    obtain rfl := List.length_eq_zero_iff.mp hp
    simp
  | succ N ih =>
    intro r pool hp
    cases r with
    | zero => simp
    | succ r =>
      cases pool with
      | nil => simp
      | cons c cs =>
        rw [collectChildren_cons, collectChildren_cons, φ.mmap_bind]
        congr 1
        funext i
        rw [φ.mmap_bind]
        congr 1
        funext w
        have hlen : ((c :: cs).eraseIdx i).length = N := by
          rw [List.length_eraseIdx_of_lt (by simpa using i.isLt)]
          omega
        cases w <;> simp only [MonadHom.mmap_map, ih _ _ hlen]

/-- A complete threshold attempt commutes with monad morphisms. -/
theorem map_thresholdChildren {m n : Type → Type} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (φ : m →ᵐ n) {C W : Type}
    (sample : (j : ℕ) → m (Fin (j + 1))) (child : C → m (Option W))
    (k : ℕ) (pool : List C) :
    φ (thresholdChildren sample child k pool) =
      thresholdChildren (fun j => φ (sample j)) (fun c => φ (child c)) k pool := by
  cases k with
  | zero => simp [thresholdChildren]
  | succ r =>
    cases pool with
    | nil => simp [thresholdChildren]
    | cons c cs =>
      simp only [thresholdChildren, φ.mmap_bind]
      congr 1
      funext i
      congr 1
      funext w
      cases w with
      | none => exact φ.mmap_pure _
      | some w =>
        dsimp only
        simp only [MonadHom.toFun_bind', MonadHom.toFun_pure']
        exact congrArg (fun xs : n (List W) => xs >>= fun ws =>
          pure (if ws.length = r then some (w :: ws) else none))
          (map_collectChildren φ sample child _ _ _ rfl)

/-- Forgetting the counter leaves precisely the direct interpretation of the Boolean oracle. -/
theorem counted_fst {Q α β : Type} (f : Q → α)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (count : ℕ) :
    Prod.fst <$> (simulateQ (coins (S := ℕ) + counted f) alg).run count =
      simulateQ (QueryImpl.ofLift unifSpec ProbComp +
        (fun q => (pure (f q) : ProbComp α))) alg := by
  induction alg using OracleComp.inductionOn generalizing count with
  | pure a => simp
  | query_bind q next ih =>
    cases q with
    | inl q =>
      simp only [coins] at ih
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
        StateT.run_bind, coins, QueryImpl.liftTarget_apply_run, QueryImpl.ofLift_apply,
        bind_map_left, map_bind, ih]
      rfl
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
        StateT.run_bind, counted, StateT.run_modify, StateT.run_pure, pure_bind]
      exact ih (f q) (count + 1)

/-- An initial counter offset is added to the final counter without changing any answers. -/
theorem counted_run_add {Q α β : Type} (f : Q → α)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (count offset : ℕ) :
    (simulateQ (coins (S := ℕ) + counted f) alg).run (count + offset) =
      (fun z => (z.1, z.2 + offset)) <$>
        (simulateQ (coins (S := ℕ) + counted f) alg).run count := by
  induction alg using OracleComp.inductionOn generalizing count with
  | pure a => simp
  | query_bind q next ih =>
    cases q with
    | inl q =>
      simp only [coins] at ih
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
        StateT.run_bind, coins, QueryImpl.liftTarget_apply_run, QueryImpl.ofLift_apply,
        bind_map_left, map_bind, ih]
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
        StateT.run_bind, counted, StateT.run_modify, StateT.run_pure, pure_bind]
      simpa only [Nat.add_right_comm count offset 1] using ih (f q) (count + 1)

/-- Changing only the output preserves the expected complete-run counter. -/
theorem expectedCalls_map_output {α β : Type} (g : α → β) (mx : ProbComp (α × ℕ)) :
    expectedCalls ((fun z => (g z.1, z.2)) <$> mx) = expectedCalls mx := by
  simp only [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
    AddWriterT.costs_def, WriterT.run_mk, Functor.map_map]

/-- Recursive tree finding commutes with interpretation of its sampling and acceptance effects.
-/
theorem map_thresholdProgram {m n : Type → Type} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (φ : m →ᵐ n)
    (sample : (j : ℕ) → m (Fin (j + 1))) (μ : ℕ) (C : Fin μ → Type)
    (k : Fin μ → ℕ) (pools : (i : Fin μ) → List (C i))
    (accept : ((i : Fin μ) → C i) → m Bool) :
    φ (thresholdProgram sample μ C k pools accept) =
      thresholdProgram (fun j => φ (sample j)) μ C k pools (fun q => φ (accept q)) := by
  induction μ with
  | zero => simp [thresholdProgram]
  | succ μ ih =>
    rw [thresholdProgram, thresholdProgram, φ.mmap_bind]
    have hc := map_thresholdChildren φ sample
      (fun c => do
        let t ← thresholdProgram sample μ (fun i => C i.succ) (fun i => k i.succ)
          (fun i => pools i.succ) (fun q => accept (Fin.cons c q))
        pure (t.map (fun t => (c, t)))) (k 0) (pools 0)
    rw [hc]
    simp only [φ.mmap_bind, φ.mmap_pure, ih]

/-- Interpreting the acceptance oracle gives the recursive Boolean-table program. -/
theorem simulateQ_thresholdFinderWithPools {m : Type → Type} [Monad m] [LawfulMonad m]
    (μ : ℕ) (C : Fin μ → Type) (k : Fin μ → ℕ) (pools : (i : Fin μ) → List (C i))
    (impl : QueryImpl (unifSpec + accSpec C) m) :
    simulateQ impl (thresholdFinderWithPools μ C k pools) =
      thresholdProgram (fun j => impl (.inl j)) μ C k pools (fun q => impl (.inr q)) := by
  have hleft (j : ℕ) : simulateQ impl
      (liftM (unifSpec.query j) : OracleComp (unifSpec + accSpec C) _) = impl (.inl j) := by
    rw [OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query, simulateQ_spec_query]
  have hright (q : (i : Fin μ) → C i) : simulateQ impl
      (liftM ((accSpec C).query q) : OracleComp (unifSpec + accSpec C) _) = impl (.inr q) := by
    rw [OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_right_query, simulateQ_spec_query]
  simpa only [thresholdFinderWithPools, simulateQ'_apply, hleft, hright] using
    map_thresholdProgram (simulateQ' impl)
      (fun j => (liftM (unifSpec.query j) : OracleComp (unifSpec + accSpec C) _)) μ C k pools
      (fun q => (liftM ((accSpec C).query q) : OracleComp (unifSpec + accSpec C) _))

end Rewinding
