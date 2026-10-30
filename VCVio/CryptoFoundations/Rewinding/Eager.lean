/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Laws
public import Mathlib.Data.Fintype.EquivFin

/-!
# Eager representation of frozen reruns

On a finite input set, drawing the outputs of all runs once gives a random function. Freezing
makes its table stable under further executions; commutation permits drawing it before any
adaptive black-box algorithm without changing the algorithm's output or complete-run count.
-/

public section

open OracleComp OracleSpec

namespace Rewinding.ResetPolicy

variable {ι σ : Type} {spec : OracleSpec ι} {init : ProbComp σ}
  {impl : QueryImpl spec (StateT σ ProbComp)} (P : ResetPolicy init impl)
  {Q α : Type} (run : Q → OracleComp spec α)

/-- Execute a complete rerun, keeping only its output and persistent world. -/
@[expose] def runWorld (q : Q) : StateT P.World ProbComp α :=
  StateT.mk fun w => (fun z => (z.1, z.2.1)) <$>
    (simulateQ P.answer (run q)).run (w, P.begin)

/-- Complete reruns only extend the persistent world. -/
theorem grows_runWorld (q : Q) (w : P.World) (z : α × P.World)
    (hz : z ∈ support ((P.runWorld run q).run w)) : w ≤ z.2 := by
  rw [runWorld, StateT.run_mk, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact P.grows_run (run q) _ _ _ hy

/-- A previously completed rerun is a pure lookup in every larger world. -/
theorem frozen_runWorld (q : Q) (w w' : P.World) (z : α × P.World)
    (hz : z ∈ support ((P.runWorld run q).run w)) (hle : z.2 ≤ w') :
    (P.runWorld run q).run w' = pure (z.1, w') := by
  rw [runWorld, StateT.run_mk, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  simp only [runWorld, StateT.run_mk,
    P.frozen_run (run q) w w' P.begin y hy hle, map_pure]

/-- Complete reruns commute while retaining their outputs and final world. -/
theorem commute_runWorld {γ : Type} (q q' : Q) (w : P.World)
    (f : α → α → P.World → ProbComp γ) :
    (do let x ← (P.runWorld run q).run w
        let y ← (P.runWorld run q').run x.2
        f x.1 y.1 y.2) =ᵈ
    (do let y ← (P.runWorld run q').run w
        let x ← (P.runWorld run q).run y.2
        f x.1 y.1 x.2) := by
  simpa only [runWorld, StateT.run_mk, bind_map_left] using
    P.commute_run (run q) (run q') P.begin P.begin w (fun a _ b _ w' => f a b w')

/-- Draw all runs in an indexed finite list, sharing the persistent world between them. -/
@[expose] def draw {n : ℕ} (qs : Fin n → Q) : StateT P.World ProbComp (Fin n → α) :=
  (fun v i => v[i]) <$> Vector.ofFnM (fun i => P.runWorld run (qs i))

private theorem draw_zero (qs : Fin 0 → Q) :
    P.draw run qs = pure Fin.elim0 := by
  simp only [draw, Vector.ofFnM_zero, map_pure]
  congr 1
  funext i
  exact Fin.elim0 i

private theorem draw_succ {n : ℕ} (qs : Fin (n + 1) → Q) :
    P.draw run qs = (do
      let a ← P.runWorld run (qs 0)
      let f ← P.draw run (fun i => qs i.succ)
      pure (Fin.cons a f)) := by
  simp only [draw, Vector.ofFnM_succ', map_bind, map_pure, bind_map_left]
  congr 1
  funext a
  congr 1
  funext v
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- A finite eager draw extends the persistent world and settles every listed input. -/
theorem draw_support {n : ℕ} (qs : Fin n → Q) (w : P.World)
    (z : (Fin n → α) × P.World) (hz : z ∈ support ((P.draw run qs).run w)) :
    w ≤ z.2 ∧ ∀ i, (P.runWorld run (qs i)).run z.2 = pure (z.1 i, z.2) := by
  induction n generalizing w with
  | zero =>
    rw [draw_zero, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨le_rfl, fun i => Fin.elim0 i⟩
  | succ n ih =>
    rw [draw_succ, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨x, hx, hz⟩ := hz
    simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨hle, hf⟩ := ih _ _ _ hy
    refine ⟨(P.grows_runWorld run _ _ _ hx).trans hle, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact P.frozen_runWorld run _ _ _ _ hx hle
    · exact hf j

/-- A complete rerun commutes with the eager finite draw. -/
theorem commute_draw {n : ℕ} (qs : Fin n → Q) (q : Q) (w : P.World)
    {γ : Type} (f : α → (Fin n → α) → P.World → ProbComp γ) :
    (do let x ← (P.runWorld run q).run w
        let y ← (P.draw run qs).run x.2
        f x.1 y.1 y.2) =ᵈ
    (do let y ← (P.draw run qs).run w
        let x ← (P.runWorld run q).run y.2
        f x.1 y.1 x.2) := by
  induction n generalizing w with
  | zero => simp only [draw_zero, StateT.run_pure, pure_bind]; rfl
  | succ n ih =>
    simp only [draw_succ, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
    exact (P.commute_runWorld run q (qs 0) w (fun a b w' => do
      let z ← (P.draw run (fun i => qs i.succ)).run w'
      f a (Fin.cons b z.1) z.2)).trans
        (EvalDistEq.bind_right _ fun y => ih _ y.2 (fun a g w' => f a (Fin.cons y.1 g) w'))

/-- The counted rerun is the world-only rerun with its counter increased by one. -/
theorem rerun_run (q : Q) (w : P.World) (m : ℕ) :
    (P.rerun run q).run (w, m) =
      (fun z => (z.1, (z.2, m + 1))) <$> (P.runWorld run q).run w := by
  simp only [rerun, runWorld, StateT.run_mk, Functor.map_map]

/-- An eager finite draw commutes with an adaptive black-box algorithm, including its fresh
coins and complete-run count. -/
theorem commute_draw_algorithm {n : ℕ} (qs : Fin n → Q) {β γ : Type}
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (w : P.World) (m : ℕ)
    (f : β → ℕ → (Fin n → α) → P.World → ProbComp γ) :
    (do let z ← (simulateQ (coins (S := P.World × ℕ) + P.rerun run) alg).run (w, m)
        let y ← (P.draw run qs).run z.2.1
        f z.1 z.2.2 y.1 y.2) =ᵈ
    (do let y ← (P.draw run qs).run w
        let z ← (simulateQ (coins (S := P.World × ℕ) + P.rerun run) alg).run (y.2, m)
        f z.1 z.2.2 y.1 z.2.1) := by
  induction alg using OracleComp.inductionOn generalizing w m f with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]; rfl
  | query_bind t k ih =>
    cases t with
    | inl t =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
        StateT.run_bind, coins, QueryImpl.liftTarget_apply_run, bind_map_left, bind_assoc,
        QueryImpl.ofLift_apply]
      exact (EvalDistEq.bind_right _ fun a => ih a w m f).trans
        (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
        StateT.run_bind, P.rerun_run, bind_map_left, bind_assoc]
      exact (EvalDistEq.bind_right ((P.runWorld run q).run w) fun x =>
        ih x.1 x.2 (m + 1) f).trans
          (P.commute_draw run qs q w (fun a g w' => do
            let z ← (simulateQ (coins (S := P.World × ℕ) + P.rerun run) (k a)).run
              (w', m + 1)
            f z.1 z.2.2 g z.2.1))

/-- Once the whole input table is settled, every adaptive algorithm is answered by that
fixed function and preserves the world. -/
theorem algorithm_of_settled {β : Type} (f : Q → α) (w : P.World)
    (hf : ∀ q, (P.runWorld run q).run w = pure (f q, w))
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (m : ℕ) :
    (simulateQ (coins (S := P.World × ℕ) + P.rerun run) alg).run (w, m) =
      (fun z => (z.1, (w, z.2))) <$>
        (simulateQ (coins (S := ℕ) + counted f) alg).run m := by
  induction alg using OracleComp.inductionOn generalizing m with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    cases t with
    | inl t =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
        StateT.run_bind, coins, QueryImpl.liftTarget_apply_run, bind_map_left,
        QueryImpl.ofLift_apply, map_bind]
      exact bind_congr fun a => ih a m
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
        StateT.run_bind, P.rerun_run, hf, map_pure, pure_bind]
      simpa [counted] using ih (f q) (m + 1)

/-- Every coordinate of the eager table has the marginal of its complete frozen rerun. -/
theorem draw_marginal {n : ℕ} (qs : Fin n → Q) (i : Fin n) (w : P.World) :
    (do let z ← (P.draw run qs).run w; pure (z.1 i)) =ᵈ
      (P.runWorld run (qs i)).run' w := by
  have hswap := P.commute_draw run qs (qs i) w (fun a _ _ => pure a)
  have hleft :
      (do let x ← (P.runWorld run (qs i)).run w
          let y ← (P.draw run qs).run x.2
          pure x.1) =ᵈ (P.runWorld run (qs i)).run' w := by
    rw [StateT.run'_eq, map_eq_bind_pure_comp]
    exact EvalDistEq.bind_right _ fun x => OracleComp.EvalDistEq.bind_const _ _
  have hright :
      (do let y ← (P.draw run qs).run w
          let x ← (P.runWorld run (qs i)).run y.2
          pure x.1) =ᵈ (do let y ← (P.draw run qs).run w; pure (y.1 i)) := by
    apply OracleComp.EvalDistEq.bind_congr_of_support
    intro y hy
    rw [(P.draw_support run qs w y hy).2 i, pure_bind]
  exact hright.symm.trans (hswap.symm.trans hleft)

/-- Running an algorithm against frozen reruns agrees with first drawing a complete table and
then answering from that table, with the same complete-run count. -/
theorem attempt_draw {n : ℕ} (qs : Fin n → Q) (idx : Q → Fin n)
    (hidx : ∀ q, qs (idx q) = q) {β : Type}
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) :
    P.attempt run alg =ᵈ
      (do let y ← (P.draw run qs).run P.empty
          (simulateQ (coins (S := ℕ) + counted (fun q => y.1 (idx q))) alg).run 0) := by
  have hswap := P.commute_draw_algorithm run qs alg P.empty 0
    (fun a m _ _ => pure (a, m))
  have hleft :
      (do let z ← (simulateQ (coins (S := P.World × ℕ) + P.rerun run) alg).run (P.empty, 0)
          let y ← (P.draw run qs).run z.2.1
          pure (z.1, z.2.2)) =ᵈ P.attempt run alg := by
    rw [attempt, map_eq_bind_pure_comp]
    exact EvalDistEq.bind_right _ fun z => OracleComp.EvalDistEq.bind_const _ _
  refine hleft.symm.trans (hswap.trans ?_)
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro y hy
  have hf : ∀ q, (P.runWorld run q).run y.2 = pure (y.1 (idx q), y.2) := by
    intro q
    simpa only [hidx] using (P.draw_support run qs P.empty y hy).2 (idx q)
  rw [P.algorithm_of_settled run _ y.2 hf alg 0]
  simp [bind_pure_comp, Functor.map_map]

/-- On a finite input set, frozen reruns are distributed as a single random function with
honest marginals. Every black-box algorithm sees the same joint output and complete-run count
when answered by that function. -/
theorem rerun_eager [Finite Q] :
    ∃ F : ProbComp (Q → α),
      (∀ q, ((fun f => f q) <$> F) =ᵈ
        (do (simulateQ impl (run q)).run' (← init))) ∧
      ∀ {β : Type} (alg : OracleComp (unifSpec + rerunSpec Q α) β),
        P.attempt run alg =ᵈ
          (do let f ← F
              (simulateQ (coins (S := ℕ) + counted f) alg).run 0) := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  let e := Fintype.equivFin Q
  let F : ProbComp (Q → α) :=
    (fun z q => z.1 (e q)) <$> (P.draw run e.symm).run P.empty
  refine ⟨F, fun q => ?_, fun alg => ?_⟩
  · have hm := P.draw_marginal run e.symm (e q) P.empty
    simp only [Equiv.symm_apply_apply] at hm
    have hf := P.faithful (run q)
    have hf' : (P.runWorld run q).run' P.empty =ᵈ
        (do (simulateQ impl (run q)).run' (← init)) := by
      simpa only [runWorld, StateT.run'_eq, StateT.run_mk, Functor.map_map] using hf
    simpa only [F, Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_def] using hm.trans hf'
  · simpa only [F, bind_map_left] using
      P.attempt_draw run e.symm e (fun q => e.symm_apply_apply q) alg

end Rewinding.ResetPolicy
