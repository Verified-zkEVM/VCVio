/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Control.Do.Spec
public import VCVio.ProgramLogic.Unary.WP.Necessary
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import ToMathlib.Control.WriterT.WP

/-!
# Specifications of `simulateQ` for any handler

The generic layer of the handler program logic, below the concrete query-tracking handlers:

* `triple_stateT_iff_forall_support` and its writer analogues read a triple for a `StateT` or
  `WriterT` computation over `OracleComp` as a statement about the support of its run, the form
  consumed by the relational lifts in `VCVio.ProgramLogic.Relational.HandlerFromUnary`;
* `QueryImpl.Spec.add_inl` and `QueryImpl.Spec.add_inr` route a query to `impl₁ + impl₂` to its
  component at the component's value type;
* `Spec.simulateQ`, the registered rule that lifts a per-query handler invariant
  (`HandlerInvariant`) to `simulateQ handler oa`, for every reading of the handler's monad:
  under the necessary reading the invariant is a predicate on states, under the upper-bound
  reading a potential; `vcgen`'s `invariants` clause fills it;
* the whole-program lifts `simulateQ_triple_preserves_invariant`,
  `simulateQ_triple_of_state_and_invariant` and their `WriterT` analogues
  (`simulateQ_writerT_triple_preserves_invariant` for monoid logs,
  `simulateQ_writerT_append_triple_preserves_invariant` for append logs), by induction on `oa`
  with `Std.WP.Triple.pure` and `Std.WP.Triple.bind`; the handler may target any oracle world,
  such as `ProbComp`;
* `simulateQ_triple_ranked`, which ranks the invariant by a query budget spent one unit per call
  of a computation with `IsTotalQueryBound`: a union bound under the upper-bound reading. Its
  budget is a proof-side fact, so it is not registered; it is applied by hand or passed
  instantiated in brackets.

The specifications of the concrete handlers (`cachingOracle`, `seededOracle`, `loggingOracle`,
`countingOracle`, `costOracle`, `cachingLoggingOracle`) are in
`VCVio.ProgramLogic.Unary.HandlerSpecs`, which imports this file.
-/

@[expose] public section

open OracleSpec OracleComp Std.WP

open scoped WriterT.MonoidWP WriterT.AppendWP

namespace OracleComp.ProgramLogic

/- The handlers' state types (caches, seeds, logs, counts) live in `Type (max u v)` for
`spec : OracleSpec.{u, v} ι`, and `StateT` / `WriterT` over `OracleComp spec : Type v → Type _`
needs them in `Type v`; both universes are pinned to `Type`. -/
variable {ι : Type}
variable {spec : OracleSpec.{0, 0} ι}

/-! ## Reading triples against the support -/

/-- A triple for a `StateT` computation over `OracleComp` constrains every value-state pair
that its run can reach from a state satisfying the precondition. -/
theorem triple_stateT_iff_forall_support {σ α : Type}
    (mx : StateT σ (OracleComp spec) α) (P : σ → Prop) (Q : α → σ → Prop)
    (epost : EStack⟨⟩) :
    Std.WP.Triple mx P Q epost ↔
      ∀ s, P s → ∀ a s', (a, s') ∈ support (mx.run s) → Q a s' :=
  Std.WP.Triple.iff.trans <| forall_congr' fun s => imp_congr_right fun _ => by
    rw [StateT.wp_apply_eq, OracleComp.Necessary.wp_iff_forall_support]
    exact ⟨fun h a s' => h (a, s'), fun h p => h p.1 p.2⟩

/-- A triple for an append-based `WriterT` computation over `OracleComp`, read by
`WriterT.AppendWP`, constrains every value the run can return together with the incoming log
extended by the log written alongside it. -/
theorem triple_writerT_iff_forall_support {ω α : Type}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (mx : WriterT ω (OracleComp spec) α) (P : ω → Prop) (Q : α → ω → Prop)
    (epost : EStack⟨⟩) :
    Std.WP.Triple mx P Q epost ↔
      ∀ s, P s → ∀ a w, (a, w) ∈ support mx.run → Q a (s ++ w) :=
  Std.WP.Triple.iff.trans <| forall_congr' fun s => imp_congr_right fun _ => by
    rw [WriterT.wpInstOf_apply_eq, OracleComp.Necessary.wp_iff_forall_support]
    exact ⟨fun h a w => h (a, w), fun h p => h p.1 p.2⟩

/-- `Monoid` variant of `triple_writerT_iff_forall_support`, read by `WriterT.MonoidWP`: the
written log is multiplied onto the incoming one. -/
theorem triple_writerT_iff_forall_support_monoid {ω α : Type} [Monoid ω]
    (mx : WriterT ω (OracleComp spec) α) (P : ω → Prop) (Q : α → ω → Prop)
    (epost : EStack⟨⟩) :
    Std.WP.Triple mx P Q epost ↔
      ∀ s, P s → ∀ a w, (a, w) ∈ support mx.run → Q a (s * w) :=
  Std.WP.Triple.iff.trans <| forall_congr' fun s => imp_congr_right fun _ => by
    rw [WriterT.wp_apply_eq, OracleComp.Necessary.wp_iff_forall_support]
    exact ⟨fun h a w => h (a, w), fun h p => h p.1 p.2⟩

/-! ## Sum handlers

A query to `impl₁ + impl₂` at `.inl t` is a program over `(spec₁ + spec₂).Range (.inl t)`, while
`impl₁ t` is a program over `spec₁.Range t`. The two types agree only after unfolding the sum
specification, which `vcgen` does not do while it matches rules, so these rules route the query to
its component with the component's value type. They hold for every interpretation of the handler
monad. A handler defined as a sum is unfolded first, as in `vcgen [myHandler]`. The rules match a
handler whose specification is spelled `spec₁ + spec₂` up to reducible unfolding; a combined
specification introduced by a plain `def` hides the sum from them. -/

section addHandler

universe u v w z

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁} {spec₂ : OracleSpec.{u, v} ι₂}
  {m : Type v → Type w} [Monad m] {Pred EPred : Type z} [Assertion Pred] [Assertion EPred]
  [WPMonad m Pred EPred]

/-- A left query to a sum handler runs the left handler. -/
@[spec]
theorem _root_.QueryImpl.Spec.add_inl (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : spec₁.Domain) (post : (spec₁ + spec₂).Range (.inl t) → Pred) (epost : EPred) :
    Triple ((impl₁ + impl₂) (.inl t)) (wp (Value := spec₁.Range t) (impl₁ t) post epost) post
      epost :=
  ⟨Lean.Order.PartialOrder.rel_refl⟩

/-- A right query to a sum handler runs the right handler. -/
@[spec]
theorem _root_.QueryImpl.Spec.add_inr (impl₁ : QueryImpl spec₁ m) (impl₂ : QueryImpl spec₂ m)
    (t : spec₂.Domain) (post : (spec₁ + spec₂).Range (.inr t) → Pred) (epost : EPred) :
    Triple ((impl₁ + impl₂) (.inr t)) (wp (Value := spec₂.Range t) (impl₂ t) post epost) post
      epost :=
  ⟨Lean.Order.PartialOrder.rel_refl⟩

end addHandler

/-! ## Generic invariant preservation for `simulateQ`

The lifts take a handler from the simulated oracles `spec` into a state or writer layer over any
oracle world `spec'`: the simulated world itself for the query-tracking handlers of this file, and
typically `ProbComp` for the handlers of security games. The `StateT` lifts
`simulateQ_triple_preserves_invariant` and `simulateQ_triple_ranked` take any monad with a core
reading, so they serve the structural, expectation and upper-bound readings alike. -/

section simulateQ

variable {ι' : Type} {spec' : OracleSpec.{0, 0} ι'}

/-- The type of handler invariants used by the specification of `simulateQ`: an assertion on
the handler's state that every query preserves. `vcgen`'s `invariants` clause fills it. -/
@[spec_invariant_type, simp, grind =]
def HandlerInvariant (σ : Type) (Pred : Type _) := σ → Pred

/-- Generic simulation triple: if every handler call `handler t` preserves an invariant `I` on
the simulation state, then `simulateQ handler oa` preserves `I` for any `oa : OracleComp spec α`.
It holds for every reading of the handler's monad `m`: under the structural reading `I` is a
predicate on states, under the upper-bound reading (`OracleComp.Upper`) a potential. The
per-query triples are verification conditions, one for each query kind, which `vcgen` continues
into when the handler unfolds. -/
@[spec]
theorem Spec.simulateQ {m : Type → Type} [Monad m] {Pred EPred : Type _}
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {σ α : Type}
    (handler : QueryImpl spec (StateT σ m)) (oa : OracleComp spec α)
    (I : HandlerInvariant σ Pred) {epost : EPred}
    (hhandler : ∀ t : spec.Domain, ⦃ fun s => I s ⦄ handler t ⦃ fun _ s => I s; epost ⦄) :
    ⦃ fun s => I s ⦄ (simulateQ handler oa : StateT σ m α) ⦃ fun _ s => I s; epost ⦄ := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact Std.WP.Triple.pure x Lean.Order.PartialOrder.rel_refl
  | query_bind t oa ih =>
    rw [simulateQ_query_bind]
    exact Std.WP.Triple.bind _ _ _ (hhandler t) ih

/-- The invariant-only form of `Spec.simulateQ` (same `I` as pre- and postcondition, independent
of the return value) is the most common case; stronger per-call specifications follow by
instantiating `I` or by the consequence rules of `Std.WP.Triple`. -/
theorem simulateQ_triple_preserves_invariant {m : Type → Type} [Monad m] {Pred EPred : Type _}
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {σ α : Type}
    (handler : QueryImpl spec (StateT σ m)) (I : σ → Pred)
    (hhandler : ∀ t : spec.Domain, ⦃ I ⦄ handler t ⦃ fun _ => I ⦄)
    (oa : OracleComp spec α) :
    ⦃ I ⦄ (simulateQ handler oa : StateT σ m α) ⦃ fun _ => I ⦄ :=
  Spec.simulateQ handler oa I hhandler

/-- A handler invariant ranked by a query budget: a call admitted at budget `b` ends at budget
`cost t b`, the potential of every budget drops to the final potential `Φ₀`, and a simulation of
a computation whose queries are bounded at budget `b` ends at `Φ₀`. The budget type, the
admission test and the cost are those of `IsQueryBound`; `simulateQ_triple_ranked`,
`simulateQ_triple_ranked_of_queryBoundP` and `simulateQ_triple_ranked_of_perIndexQueryBound`
are its instances at the total, predicate and per-index bounds. Not registered: a bound is a
proof fact, so the theorem is applied by hand and its triple bridged by `Triple.le_wp`. -/
theorem simulateQ_triple_ranked_of_isQueryBound {m : Type → Type} [Monad m] {Pred EPred : Type _}
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {σ α : Type} {B : Type*}
    (handler : QueryImpl spec (StateT σ m)) {canQuery : spec.Domain → B → Prop}
    {cost : spec.Domain → B → B} (Φ : B → σ → Pred) (Φ₀ : σ → Pred)
    (hstep : ∀ (t : spec.Domain) (b : B), canQuery t b →
      ⦃ Φ b ⦄ handler t ⦃ fun _ => Φ (cost t b) ⦄)
    (hdrop : ∀ b, Lean.Order.PartialOrder.rel (Φ b) Φ₀) (oa : OracleComp spec α) (b : B)
    (hq : oa.IsQueryBound b canQuery cost) :
    ⦃ Φ b ⦄ (simulateQ handler oa : StateT σ m α) ⦃ fun _ => Φ₀ ⦄ := by
  induction oa using OracleComp.inductionOn generalizing b with
  | pure x => exact Std.WP.Triple.pure x (hdrop b)
  | query_bind t oa ih =>
    rw [isQueryBound_query_bind_iff] at hq
    rw [simulateQ_query_bind]
    exact Std.WP.Triple.bind _ _ _ (hstep t b hq.1) fun u => ih u (cost t b) (hq.2 u)

/-- A handler invariant ranked by the remaining query budget: if a call from a state with budget
`k + 1` ends in a state with budget `k`, and an unspent budget can be dropped, then a simulation
of a computation making at most `k` queries ends in budget `0`. Under the upper-bound reading
(`OracleComp.Upper`) with `Φ k s` the indicator of a bad state plus `k` times a per-query
probability, this is the union bound over the queries: `hstep` is the bound for one query. -/
theorem simulateQ_triple_ranked {m : Type → Type} [Monad m] {Pred EPred : Type _}
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {σ α : Type}
    (handler : QueryImpl spec (StateT σ m)) (Φ : ℕ → σ → Pred)
    (hstep : ∀ (t : spec.Domain) (k : ℕ), ⦃ Φ (k + 1) ⦄ handler t ⦃ fun _ => Φ k ⦄)
    (hdrop : ∀ k, Lean.Order.PartialOrder.rel (Φ k) (Φ 0)) (oa : OracleComp spec α) (k : ℕ)
    (hq : oa.IsTotalQueryBound k) :
    ⦃ Φ k ⦄ (simulateQ handler oa : StateT σ m α) ⦃ fun _ => Φ 0 ⦄ :=
  simulateQ_triple_ranked_of_isQueryBound handler (canQuery := fun _ b => 0 < b)
    (cost := fun _ b => b - 1) Φ (Φ 0)
    (fun t k hk => by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact hstep t j)
    hdrop oa k hq

/-- `simulateQ_triple_ranked_of_isQueryBound` at a bound on the queries satisfying `p`: a call
at such an index spends one unit of the budget, any other call keeps it. -/
theorem simulateQ_triple_ranked_of_queryBoundP {m : Type → Type} [Monad m] {Pred EPred : Type _}
    [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {σ α : Type}
    (handler : QueryImpl spec (StateT σ m)) (p : spec.Domain → Prop) [DecidablePred p]
    (Φ : ℕ → σ → Pred)
    (hstep : ∀ (t : spec.Domain) (k : ℕ), p t → ⦃ Φ (k + 1) ⦄ handler t ⦃ fun _ => Φ k ⦄)
    (hskip : ∀ (t : spec.Domain) (k : ℕ), ¬ p t → ⦃ Φ k ⦄ handler t ⦃ fun _ => Φ k ⦄)
    (hdrop : ∀ k, Lean.Order.PartialOrder.rel (Φ k) (Φ 0)) (oa : OracleComp spec α) (n : ℕ)
    (hq : oa.IsQueryBoundP p n) :
    ⦃ Φ n ⦄ (simulateQ handler oa : StateT σ m α) ⦃ fun _ => Φ 0 ⦄ :=
  simulateQ_triple_ranked_of_isQueryBound handler Φ (Φ 0)
    (fun t k hk => by
      by_cases ht : p t
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 :=
          ⟨k - 1, by have := hk.resolve_left (not_not.mpr ht); omega⟩
        simpa [ht] using hstep t j ht
      · simpa [ht] using hskip t k ht)
    hdrop oa n hq

/-- `simulateQ_triple_ranked_of_isQueryBound` at a per-index bound: a call at `t` spends one unit
of the budget of `t`. -/
theorem simulateQ_triple_ranked_of_perIndexQueryBound {m : Type → Type} [Monad m]
    {Pred EPred : Type _} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [DecidableEq ι] {σ α : Type}
    (handler : QueryImpl spec (StateT σ m)) (Φ : (spec.Domain → ℕ) → σ → Pred)
    (hstep : ∀ (t : spec.Domain) (qb : spec.Domain → ℕ), 0 < qb t →
      ⦃ Φ qb ⦄ handler t ⦃ fun _ => Φ (Function.update qb t (qb t - 1)) ⦄)
    (hdrop : ∀ qb, Lean.Order.PartialOrder.rel (Φ qb) (Φ 0)) (oa : OracleComp spec α)
    (qb : spec.Domain → ℕ) (hq : oa.IsPerIndexQueryBound qb) :
    ⦃ Φ qb ⦄ (simulateQ handler oa : StateT σ m α) ⦃ fun _ => Φ 0 ⦄ :=
  simulateQ_triple_ranked_of_isQueryBound handler Φ (Φ 0) hstep hdrop oa qb hq

/-- Specialized simulation triple: combine a starting-state precondition `s = s₀` with an
invariant that holds of `s₀`. The invariant is threaded through the entire simulation. -/
theorem simulateQ_triple_of_state_and_invariant {σ α : Type}
    (handler : QueryImpl spec (StateT σ (OracleComp spec')))
    (I : σ → Prop)
    (hhandler : ∀ t : spec.Domain, ⦃ fun s => I s ⦄ handler t ⦃ fun _ s' => I s' ⦄)
    (oa : OracleComp spec α) (s₀ : σ) (hI : I s₀) :
    ⦃ fun s => s = s₀ ⦄ (simulateQ handler oa : StateT σ (OracleComp spec') α)
      ⦃ fun _ s' => I s' ⦄ :=
  ⟨fun _ hs => hs ▸ (simulateQ_triple_preserves_invariant handler I hhandler oa).le_wp s₀ hI⟩

/-- `WriterT` analogue of `simulateQ_triple_preserves_invariant` for monoid logs, read by
`WriterT.MonoidWP`: if every per-query handler call preserves an invariant `I` on the accumulated
writer log, then the whole simulation `simulateQ handler oa` preserves `I`. Typical `handler`
values are `countingOracle` and `costOracle costFn`. -/
theorem simulateQ_writerT_triple_preserves_invariant {ω α : Type} [Monoid ω]
    (handler : QueryImpl spec (WriterT ω (OracleComp spec')))
    (I : ω → Prop)
    (hhandler : ∀ t : spec.Domain, ⦃ fun s => I s ⦄ handler t ⦃ fun _ s' => I s' ⦄)
    (oa : OracleComp spec α) :
    ⦃ fun s => I s ⦄ (simulateQ handler oa : WriterT ω (OracleComp spec') α)
      ⦃ fun _ s' => I s' ⦄ := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact Std.WP.Triple.pure x fun _ h => h
  | query_bind t oa ih =>
    rw [simulateQ_query_bind]
    exact Std.WP.Triple.bind _ _ _ (hhandler t) ih

/-- `WriterT` analogue of `simulateQ_triple_preserves_invariant` for append logs such as
`QueryLog`, read by `WriterT.AppendWP`: if every per-query handler call preserves an invariant `I`
on the accumulated log, then the whole simulation `simulateQ handler oa` preserves `I`. Typical
`handler` values are `loggingOracle` and `so.withLogging`. -/
theorem simulateQ_writerT_append_triple_preserves_invariant {ω α : Type}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (handler : QueryImpl spec (WriterT ω (OracleComp spec')))
    (I : ω → Prop)
    (hhandler : ∀ t : spec.Domain, ⦃ fun s => I s ⦄ handler t ⦃ fun _ s' => I s' ⦄)
    (oa : OracleComp spec α) :
    ⦃ fun s => I s ⦄ (simulateQ handler oa : WriterT ω (OracleComp spec') α)
      ⦃ fun _ s' => I s' ⦄ := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact Std.WP.Triple.pure x fun _ h => h
  | query_bind t oa ih =>
    rw [simulateQ_query_bind]
    exact Std.WP.Triple.bind _ _ _ (hhandler t) ih

end simulateQ

end OracleComp.ProgramLogic
