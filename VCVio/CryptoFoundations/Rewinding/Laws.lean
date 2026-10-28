/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Basic

/-!
# Extension, replay, and commutation of complete runs

The local laws of a reset policy extend to adaptive computations. In particular, a completed
run can be replayed deterministically in every extension of its final world, and two complete
runs commute while retaining their outputs and final cursors.
-/

public section

open OracleComp OracleSpec

namespace Rewinding.ResetPolicy

variable {ι σ : Type} {spec : OracleSpec ι} {init : ProbComp σ}
  {impl : QueryImpl spec (StateT σ ProbComp)} (P : ResetPolicy init impl)

/-- A complete execution only extends the persistent world. -/
theorem grows_run {α : Type} (oa : OracleComp spec α) (w : P.World) (c : P.Cursor)
    (z : α × P.World × P.Cursor) (hz : z ∈ support ((simulateQ P.answer oa).run (w, c))) :
    w ≤ z.2.1 := by
  induction oa using OracleComp.inductionOn generalizing w c with
  | pure a =>
    simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using
      hz ▸ (show w ≤ w from le_rfl)
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    exact (P.grows q w c y hy).trans (ih y.1 y.2.1 y.2.2 hz)

/-- A completed execution is replayed identically from its original cursor in every extension
of its final world. -/
theorem frozen_run {α : Type} (oa : OracleComp spec α) (w w' : P.World) (c : P.Cursor)
    (z : α × P.World × P.Cursor) (hz : z ∈ support ((simulateQ P.answer oa).run (w, c)))
    (hle : z.2.1 ≤ w') :
    (simulateQ P.answer oa).run (w', c) = pure (z.1, (w', z.2.2)) := by
  induction oa using OracleComp.inductionOn generalizing w c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    simp only [simulateQ_pure, StateT.run_pure]
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz ⊢
    obtain ⟨y, hy, hz⟩ := hz
    rw [P.frozen q w w' c y hy ((P.grows_run (k y.1) _ _ _ hz).trans hle), pure_bind]
    exact ih y.1 y.2.1 y.2.2 hz

/-- The query commutation law allows an arbitrary continuation of both answers, both local
cursors, and the final world. -/
theorem commute_bind {γ : Type} (q₁ q₂ : spec.Domain) (c₁ c₂ : P.Cursor) (w : P.World)
    (f : spec.Range q₁ → P.Cursor → spec.Range q₂ → P.Cursor → P.World → ProbComp γ) :
    (do
      let z₁ ← (P.answer q₁).run (w, c₁)
      let z₂ ← (P.answer q₂).run (z₁.2.1, c₂)
      f z₁.1 z₁.2.2 z₂.1 z₂.2.2 z₂.2.1) =ᵈ
    (do
      let z₂ ← (P.answer q₂).run (w, c₂)
      let z₁ ← (P.answer q₁).run (z₂.2.1, c₁)
      f z₁.1 z₁.2.2 z₂.1 z₂.2.2 z₁.2.1) := by
  simpa only [bind_assoc, pure_bind] using
    (P.commute q₁ q₂ c₁ c₂ w).bind_left (fun z => f z.1.1 z.1.2 z.2.1.1 z.2.1.2 z.2.2)

/-- A single query commutes with an adaptive execution at an independent local cursor. -/
theorem commute_query_run {α γ : Type} (q : spec.Domain) (oa : OracleComp spec α)
    (c₁ c₂ : P.Cursor) (w : P.World)
    (f : spec.Range q → P.Cursor → α → P.Cursor → P.World → ProbComp γ) :
    (do
      let z₁ ← (P.answer q).run (w, c₁)
      let z₂ ← (simulateQ P.answer oa).run (z₁.2.1, c₂)
      f z₁.1 z₁.2.2 z₂.1 z₂.2.2 z₂.2.1) =ᵈ
    (do
      let z₂ ← (simulateQ P.answer oa).run (w, c₂)
      let z₁ ← (P.answer q).run (z₂.2.1, c₁)
      f z₁.1 z₁.2.2 z₂.1 z₂.2.2 z₁.2.1) := by
  induction oa using OracleComp.inductionOn generalizing c₂ w with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]; rfl
  | query_bind q₂ k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    exact (P.commute_bind q q₂ c₁ c₂ w (fun a c₁' b c₂' w' => do
      let z ← (simulateQ P.answer (k b)).run (w', c₂')
      f a c₁' z.1 z.2.2 z.2.1)).trans
        (EvalDistEq.bind_right _ fun y => ih y.1 y.2.2 y.2.1)

/-- Two adaptive executions commute, jointly in both outputs, local cursors, and final world. -/
theorem commute_run {α β γ : Type} (oa : OracleComp spec α) (ob : OracleComp spec β)
    (c₁ c₂ : P.Cursor) (w : P.World)
    (f : α → P.Cursor → β → P.Cursor → P.World → ProbComp γ) :
    (do
      let z₁ ← (simulateQ P.answer oa).run (w, c₁)
      let z₂ ← (simulateQ P.answer ob).run (z₁.2.1, c₂)
      f z₁.1 z₁.2.2 z₂.1 z₂.2.2 z₂.2.1) =ᵈ
    (do
      let z₂ ← (simulateQ P.answer ob).run (w, c₂)
      let z₁ ← (simulateQ P.answer oa).run (z₂.2.1, c₁)
      f z₁.1 z₁.2.2 z₂.1 z₂.2.2 z₁.2.1) := by
  induction oa using OracleComp.inductionOn generalizing c₁ w f with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]; rfl
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    exact (EvalDistEq.bind_right ((P.answer q).run (w, c₁)) fun y =>
      ih y.1 y.2.2 y.2.1 f).trans
      (P.commute_query_run q ob c₁ c₂ w (fun a c₁' b c₂' w' => do
        let z ← (simulateQ P.answer (k a)).run (w', c₁')
        f z.1 z.2.2 b c₂' z.2.1))

end Rewinding.ResetPolicy
