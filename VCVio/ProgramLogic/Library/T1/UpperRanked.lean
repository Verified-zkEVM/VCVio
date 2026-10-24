/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T1.Upper
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Ranked simulations and the union bound over queries

A bound that accumulates across the queries of a simulation is a potential carried in a ranked
invariant: `Φ (k + 1)` before a query and `Φ k` after it, with `k` the remaining query budget.

* `simulateQ_triple_ranked` lifts a per-query ranked triple to a whole simulation of a
  computation within `k` queries, in any reading; `simulateQ_triple_ranked_of_isQueryBoundP`
  charges only the queries in a predicate.
* `prEvent_simulateQ_run_le_of_ranked` reads a ranked triple of the upper reading off as a
  bad-event bound from one initial state.
* `prEvent_simulateQ_run_bad_le_of_step` is the union bound over queries: per-query bad
  probability `δ` from good states gives `n * δ` within `n` queries, with the potential
  `propInd (bad s) + k * δ` (`triple_propInd_bad_add`) built in;
  `prEvent_simulateQ_run_bad_le_of_step_isQueryBoundP` charges only the queries in a predicate.
-/

@[expose] public section

open ENNReal Std.WP OrderDual OracleSpec OracleComp

namespace OracleComp.ProgramLogic

open scoped OracleComp.Upper

/-! ## Ranked simulations -/

/-- **Ranked simulation.** A handler whose every query moves a potential from `Φ (k + 1)` to
`Φ k`, in any reading, runs a computation within `k` queries from `Φ k` to `Φ 0`. -/
theorem simulateQ_triple_ranked {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {n : Type → Type} [Monad n] {Pred EPred : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad n Pred EPred] (handler : QueryImpl spec n) (Φ : ℕ → Pred) (E : EPred)
    (hstep : ∀ t k, Std.WP.Triple (handler t) (Φ (k + 1)) (fun _ => Φ k) E)
    (hdrop : ∀ k, Lean.Order.PartialOrder.rel (Φ k) (Φ 0))
    (oa : OracleComp spec α) (k : ℕ) (hk : IsTotalQueryBound oa k) :
    Std.WP.Triple (simulateQ handler oa) (Φ k) (fun _ => Φ 0) E := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure x => exact Triple.pure x (hdrop k)
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [simulateQ_query_bind]
    exact Triple.bind _ _ _ (hstep t j) fun u => ih u j (hk.2 u)

/-- **Ranked simulation, charging only the queries in `P`.** Queries in `P` move the potential
from `Φ (k + 1)` to `Φ k`, the others keep `Φ k`. -/
theorem simulateQ_triple_ranked_of_isQueryBoundP {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {α : Type} {n : Type → Type} [Monad n] {Pred EPred : Type} [Assertion Pred]
    [Assertion EPred] [WPMonad n Pred EPred] (handler : QueryImpl spec n) (P : ι → Prop)
    [DecidablePred P] (Φ : ℕ → Pred) (E : EPred)
    (hstep : ∀ t k, P t → Std.WP.Triple (handler t) (Φ (k + 1)) (fun _ => Φ k) E)
    (hfree : ∀ t k, ¬P t → Std.WP.Triple (handler t) (Φ k) (fun _ => Φ k) E)
    (hdrop : ∀ k, Lean.Order.PartialOrder.rel (Φ k) (Φ 0))
    (oa : OracleComp spec α) (k : ℕ) (hk : IsQueryBoundP oa P k) :
    Std.WP.Triple (simulateQ handler oa) (Φ k) (fun _ => Φ 0) E := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure x => exact Triple.pure x (hdrop k)
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hk
    rw [simulateQ_query_bind]
    by_cases ht : P t
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 :=
        ⟨k - 1, by have := hk.1.resolve_left (not_not.2 ht); omega⟩
      exact Triple.bind _ _ _ (hstep t j ht) fun u => ih u j (by simpa [ht] using hk.2 u)
    · exact Triple.bind _ _ _ (hfree t k ht) fun u => ih u k (by simpa [ht] using hk.2 u)

/-- **Ranked bad-event bound.** A per-query ranked upper triple from `Φ (k + 1)` to `Φ k`, with
`Φ 0` above the bad indicator, bounds the bad event within `n` queries by `Φ n s₀`. -/
theorem prEvent_simulateQ_run_le_of_ranked {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec ι'} [AnswerMeasure spec'] {α σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (Φ : ℕ → σ → ℝ≥0∞)
    (hstep : ∀ t k, ⦃ fun s => toDual (Φ (k + 1) s) ⦄ impl t ⦃ fun _ s => toDual (Φ k s) ⦄)
    (hmono : ∀ k s, Φ 0 s ≤ Φ k s) (bad : σ → Prop) (hbad : ∀ s, propInd (bad s) ≤ Φ 0 s)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsTotalQueryBound oa n) (s₀ : σ) :
    Pr{let z ← (simulateQ impl oa).run s₀}[bad z.2] ≤ Φ n s₀ := by
  have h := simulateQ_triple_ranked impl (fun k s => toDual (Φ k s)) Lean.Order.bot
    (fun t k => hstep t k) (fun k s => hmono k s) oa n hn
  rw [OracleComp.Upper.triple_stateT_iff] at h
  rw [prEvent_eq_wp_propInd]
  exact (wp_mono _ fun z : α × σ => hbad z.2).trans (h s₀)

/-- One step of the union bound: a step that goes bad from a good state with probability `≤ c`
moves the potential `propInd (bad s) + (c + x)` to `propInd (bad s') + x`. -/
theorem triple_propInd_bad_add {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec ι'} [AnswerMeasure spec'] {σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop) (t : spec.Domain)
    {c : ℝ≥0∞} (hstep : ∀ s, ¬bad s → Pr{let z ← (impl t).run s}[bad z.2] ≤ c) (x : ℝ≥0∞) :
    ⦃ fun s => toDual (propInd (bad s) + (c + x)) ⦄ impl t
      ⦃ fun _ s => toDual (propInd (bad s) + x) ⦄ := by
  rw [OracleComp.Upper.triple_stateT_iff]
  intro s
  simp only [ofDual_toDual]
  rw [wp_add, wp_const, ← prEvent_eq_wp_propInd]
  by_cases hs : bad s
  · rw [show propInd (bad s) = 1 from propInd_eq_one_iff.2 hs, ← add_assoc]
    exact add_le_add ((prEvent_le_one _).trans le_self_add) le_rfl
  · rw [show propInd (bad s) = 0 from propInd_eq_zero_iff.2 hs, zero_add]
    exact add_le_add (hstep s hs) le_rfl

/-- **Union bound over the queries of a simulation.** Per-query bad probability `δ` from good
states gives bad probability `n * δ` within `n` queries from a good state. -/
theorem prEvent_simulateQ_run_bad_le_of_step {ι ι' : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec ι'} [AnswerMeasure spec'] {α σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop) (δ : ℝ≥0∞)
    (hstep : ∀ t s, ¬bad s → Pr{let z ← (impl t).run s}[bad z.2] ≤ δ)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsTotalQueryBound oa n) (s₀ : σ) (h₀ : ¬bad s₀) :
    Pr{let z ← (simulateQ impl oa).run s₀}[bad z.2] ≤ n * δ := by
  have h := prEvent_simulateQ_run_le_of_ranked impl (fun k s => propInd (bad s) + k * δ)
    (fun t k => by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm δ] using
        triple_propInd_bad_add impl bad t (hstep t) (k * δ))
    (fun k s => by simp) bad (fun s => by simp) oa n hn s₀
  simpa [propInd_eq_zero_iff.2 h₀] using h

/-- **Union bound over the charged queries.** Per-query bad probability `δ` for the queries in
`P`, and none for the others, gives `n * δ` within `n` queries in `P`. -/
theorem prEvent_simulateQ_run_bad_le_of_step_isQueryBoundP {ι ι' : Type}
    {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec ι'} [AnswerMeasure spec'] {α σ : Type}
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop) (δ : ℝ≥0∞)
    (P : ι → Prop) [DecidablePred P]
    (hstep : ∀ t, P t → ∀ s, ¬bad s → Pr{let z ← (impl t).run s}[bad z.2] ≤ δ)
    (hfree : ∀ t, ¬P t → ∀ s, ¬bad s → Pr{let z ← (impl t).run s}[bad z.2] = 0)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa P n) (s₀ : σ) (h₀ : ¬bad s₀) :
    Pr{let z ← (simulateQ impl oa).run s₀}[bad z.2] ≤ n * δ := by
  have h := simulateQ_triple_ranked_of_isQueryBoundP impl P
    (fun k s => toDual (propInd (bad s) + k * δ)) Lean.Order.bot
    (fun t k ht => by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm δ] using
        triple_propInd_bad_add impl bad t (hstep t ht) (k * δ))
    (fun t k ht => by
      simpa only [zero_add] using
        triple_propInd_bad_add impl bad t (fun s hs => (hfree t ht s hs).le) (k * δ))
    (fun k s => show propInd (bad s) + ((0 : ℕ) : ℝ≥0∞) * δ ≤ propInd (bad s) + k * δ by simp)
    oa n hn
  rw [OracleComp.Upper.triple_stateT_iff] at h
  rw [prEvent_eq_wp_propInd]
  simpa [propInd_eq_zero_iff.2 h₀] using
    (wp_mono _ fun z : α × σ => le_self_add).trans (h s₀)

end OracleComp.ProgramLogic

