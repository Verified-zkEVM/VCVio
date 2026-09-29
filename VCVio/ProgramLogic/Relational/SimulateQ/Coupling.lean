/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Relational `simulateQ` rules

Couplings of oracle simulations: two stateful or writer-transformed implementations whose
per-query runs are coupled preserve the coupling through the simulation of any computation.
Stochastic dominance of a bad-state event transports through a simulation from a marginal or
distribution-level per-query step.
-/

public section

open ENNReal OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

universe u

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type u} {spec : OracleSpec ι}
variable {α : Type}
variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{u, 0} ι₂}
  [OracleSpec.IsMeasureSpec spec₁] [OracleSpec.IsMeasureSpec spec₂]

section coupling

variable [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]

/-! ## Relational simulateQ rules -/

/-- **Core relational `simulateQ` rule.** If two stateful oracle implementations answer every
query with equal outputs while preserving a state invariant `R_state`, then simulating any
computation `oa` under either implementation preserves both: the two runs are coupled so that
their outputs agree and their final states remain `R_state`-related.

`R_state` is an arbitrary heterogeneous relation between the two state spaces `σ₁` and `σ₂`, not
an equivalence on a shared one, so the two simulations may carry entirely different bookkeeping
(a cache on one side against a lazily sampled table on the other, say).

Applying it: all the probabilistic content sits in `himpl`, a per-query coupling that has to be
re-established from `R_state s₁ s₂` alone; `oa` is universally quantified, so no hypothesis about
the simulated program is needed. The postcondition constrains the full `(output, state)` pair,
which is what `prEvent_le_of_relTriple_simulateQ_run` consumes to transport an event bound.

`relTriple_simulateQ_run_mono` weakens `himpl` to let the two handlers return *different* answers,
paying for it with a self-referential recoupling hypothesis on the continuation.
`relTriple_simulateQ_run'` is this rule with the state component projected away, keeping only
output equality, and `relTriple_simulateQ_run'_of_impl_evalDistEq` specializes that to a shared
state space with `Eq` as the invariant. -/
theorem relTriple_simulateQ_run
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run s₁)
      ((simulateQ impl₂ oa).run s₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure x =>
    simpa using hs
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    exact relTriple_bind (himpl t s₁ s₂ hs) fun ⟨u₁, s₁'⟩ ⟨u₂, s₂'⟩ ⟨rfl, hs'⟩ => ih _ s₁' s₂' hs'

/-- **Monotone relational `simulateQ`.** A generalization of `relTriple_simulateQ_run` that
does *not* require equal per-query outputs. Instead, each per-query coupling must (a) preserve
the state invariant and (b) supply, for the *same* free-monad continuation applied to the two
(possibly different) coupled outputs, a recoupling of the two continued simulations preserving
the invariant. This is the right shape when the two handlers genuinely diverge on the answer
returned to the caller (e.g. an eager vs. deferred-sampling random-oracle read), so output
equality cannot be maintained and the coupling must be rebuilt across the branch point.

The continuation hypothesis is self-referential by design: discharging it is exactly the
construction of the divergent-branch coupling, which is the hard probabilistic content this
lemma isolates from the free-monad bookkeeping. -/
theorem relTriple_simulateQ_run_mono
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => R_state p₁.2 p₂.2 ∧
          ∀ (ob : spec.Range t → OracleComp spec α),
            RelTriple ((simulateQ impl₁ (ob p₁.1)).run p₁.2)
                      ((simulateQ impl₂ (ob p₂.1)).run p₂.2)
              (fun q₁ q₂ => R_state q₁.2 q₂.2)))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run s₁)
      ((simulateQ impl₂ oa).run s₂)
      (fun p₁ p₂ => R_state p₁.2 p₂.2) := by
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure x => simpa using hs
  | query_bind t ob _ =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    -- the induction hypothesis is unused: `himpl`'s continuation clause recouples directly
    exact relTriple_bind (himpl t s₁ s₂ hs) fun _ _ h => h.2 ob

/-- **Output-projected relational `simulateQ`.** Under the per-query coupling of
`relTriple_simulateQ_run` — equal answers while the state invariant `R_state` is preserved — the
two simulations of `oa` produce equal outputs, the final states being discarded by `run'`.

The hypotheses are exactly those of `relTriple_simulateQ_run`, so all the probabilistic content
still sits in `himpl`; only the conclusion changes shape, from a relation on `(output, state)`
pairs to an `EqRel` between two plain computations. That is the form the transport lemmas
`prEvent_eq_of_relTriple_eqRel` and `evalDistEq_of_relTriple_eqRel` consume, so reach for it
whenever the residual states are bookkeeping the statement should not mention; keep
`relTriple_simulateQ_run` when the conclusion must still constrain them, since the projection
cannot be undone. `rvcgen` applies this rule on its own, first specializing `R_state` to `Eq`.

`relTriple_simulateQ_run'_of_impl_evalDistEq` specializes it to a shared state space with `Eq`
as the invariant, trading `himpl` for a per-query equality in distribution. -/
theorem relTriple_simulateQ_run'
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run' s₁)
      ((simulateQ impl₂ oa).run' s₂)
      (EqRel α) := by
  have h := relTriple_simulateQ_run impl₁ impl₂ R_state oa himpl s₁ s₂ hs
  have h_weak : RelTriple ((simulateQ impl₁ oa).run s₁) ((simulateQ impl₂ oa).run s₂)
      (fun p₁ p₂ => (EqRel α) (Prod.fst p₁) (Prod.fst p₂)) := by
    apply relTriple_post_mono h
    intro p₁ p₂ hp
    exact hp.1
  exact relTriple_map h_weak

/-- **Event bound through a relational `simulateQ` run.** If two `StateT` implementations answer
every query with equal outputs while preserving the state invariant `rState` (hypothesis `himpl`),
then any event implication valid along the run postcondition `z₁.1 = z₂.1 ∧ rState z₁.2 z₂.2`
transports to an event inequality between the two simulations of the same computation `oa`.

Applying it: `himpl` is verbatim the per-query coupling `relTriple_simulateQ_run` demands, and
`himp` receives output equality and the state relation as separate arguments rather than as one
conjunction. The events range over full `(output, state)` pairs, so output events, state events
and their conjunctions are all in scope (the output type `α` is shared; the state spaces `σ₁` and
`σ₂` need not be).

`prEvent_le_of_relTriple` states the same event bound for an arbitrary coupling of two
arbitrary computations; here the coupling is built from a per-query one, so no relational triple
about `oa` itself has to be supplied. -/
theorem prEvent_le_of_relTriple_simulateQ_run
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (rState : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      rState s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ rState p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : rState s₁ s₂)
    {p : α × σ₁ → Prop} {q : α × σ₂ → Prop}
    (himp : ∀ z₁ z₂, z₁.1 = z₂.1 → rState z₁.2 z₂.2 → p z₁ → q z₂) :
    Pr{let z ← (simulateQ impl₁ oa).run s₁}[p z] ≤
      Pr{let z ← (simulateQ impl₂ oa).run s₂}[q z] :=
  prEvent_le_of_relTriple (relTriple_simulateQ_run impl₁ impl₂ rState oa himpl s₁ s₂ hs)
    fun z₁ z₂ h => himp z₁ z₂ h.1 h.2

/-- Exact-distribution specialization of `relTriple_simulateQ_run'`.

If corresponding oracle calls have identical full `(output, state)` distributions whenever the
states are equal, then the simulated computations have identical output distributions. This
packages the common pattern "prove per-query output-measure equality, then use `Eq` as the state
invariant" into a single theorem.

Applying it leaves `himpl` as the only real side goal: `σ`, the two implementations and `oa` are
fixed by unification against the conclusion, and `hs` is `rfl` whenever both runs start from the
same state. `rvcgen` reaches for this rule on its own once both sides of an `EqRel` goal are `run'`
simulations.

The neighbouring rules tie the two state spaces together differently — `relTriple_simulateQ_run'`
through an arbitrary state invariant plus a per-query relational triple, and
`relTriple_simulateQ_run'_of_query_map_eq` through a projection of the first state space onto the
second. Reach for this one when both simulations share a state space and per-query agreement is an
equality of distributions rather than of computations.
`OracleComp.evalDist_simulateQ_run_congr_of_forall` draws the same conclusion as a bare
output-measure equality on `run`, but only when both implementations also share the ambient
spec they simulate into. -/
theorem relTriple_simulateQ_run'_of_impl_evalDistEq
    {σ : Type}
    (impl₁ : QueryImpl spec (StateT σ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ (OracleComp spec₂)))
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s : σ), (impl₁ t).run s =ᵈ (impl₂ t).run s)
    (s₁ s₂ : σ) (hs : s₁ = s₂) :
    RelTriple
      ((simulateQ impl₁ oa).run' s₁)
      ((simulateQ impl₂ oa).run' s₂)
      (EqRel α) :=
  relTriple_simulateQ_run' impl₁ impl₂ Eq oa
    (fun t s _ h => h ▸ relTriple_of_evalDistEq (himpl t s) fun _ => ⟨rfl, rfl⟩) s₁ s₂ hs

/-! ### `WriterT` analogue -/

/-- `WriterT` analogue of `relTriple_simulateQ_run`.

If two writer-transformed oracle implementations produce outputs related by a reflexive-and-closed
relation `R_writer` on the accumulated logs, then the full simulation preserves output equality
together with the accumulated-log relation.

`hR_one` witnesses reflexivity at the empty accumulator (the run-start value), and `hR_mul`
closes `R_writer` under the monoid multiplication used by `WriterT`'s bind. Together these make
`R_writer` a *monoid congruence* on the two writer spaces, which is precisely the structural
requirement for whole-program accumulation.

Applying it: `himpl` carries all of the probabilistic content, so discharge it first; `hR_one`
and `hR_mul` are pure monoid bookkeeping. `hR_mul` is quantified over *all* pairs of logs, not
only the reachable ones, so a relation that merely happens to hold along reachable runs will not
serve — pick `R_writer` as weak as the downstream consumer tolerates.

`relTriple_simulateQ_run_writerT_of_impl_eq` is the collapsed case where a single writer space is
shared and the two handlers agree pointwise on `.run`, so the congruence degenerates to equality
and no monoid hypotheses need supplying. `relTriple_simulateQ_run_writerT'` takes exactly these
hypotheses but projects the conclusion onto output equality alone, discarding the log relation. -/
theorem relTriple_simulateQ_run_writerT
    {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂]
    (impl₁ : QueryImpl spec (WriterT ω₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (WriterT ω₂ (OracleComp spec₂)))
    (R_writer : ω₁ → ω₂ → Prop)
    (hR_one : R_writer 1 1)
    (hR_mul : ∀ w₁ w₁' w₂ w₂', R_writer w₁ w₂ → R_writer w₁' w₂' →
      R_writer (w₁ * w₁') (w₂ * w₂'))
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain),
      RelTriple ((impl₁ t).run) ((impl₂ t).run)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_writer p₁.2 p₂.2)) :
    RelTriple
      (simulateQ impl₁ oa).run
      (simulateQ impl₂ oa).run
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_writer p₁.2 p₂.2) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using hR_one
  | query_bind t _ ih =>
    -- each `WriterT` bind multiplies the query's log into the continuation's, so `hR_mul`
    -- rebuilds the coupling from the per-query relation and the induction hypothesis
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, WriterT.run_bind]
    exact relTriple_bind (himpl t) fun ⟨u₁, w₁⟩ ⟨u₂, w₂⟩ ⟨rfl, hw⟩ => relTriple_map
      (relTriple_post_mono (ih _) fun _ _ ⟨hab, hv⟩ => ⟨hab, hR_mul _ _ _ _ hw hv⟩)

/-- `WriterT` analogue of `relTriple_simulateQ_run_of_impl_eq_preservesInv`.

If two writer-transformed oracle implementations agree pointwise on
`.run` (i.e. every per-query increment is identical as an `OracleComp`),
then the whole simulations yield identical `(output, accumulator)`
distributions.

`WriterT` handlers are stateless (`.run` takes no argument), so the
hypothesis is a plain equality rather than an invariant-gated
implication. The postcondition is strict equality on `α × ω`. -/
theorem relTriple_simulateQ_run_writerT_of_impl_eq
    {ω : Type} [Monoid ω]
    (impl₁ impl₂ : QueryImpl spec (WriterT ω (OracleComp spec₁)))
    (himpl_eq : ∀ (t : spec.Domain), (impl₁ t).run = (impl₂ t).run)
    (oa : OracleComp spec α) :
    RelTriple
      (simulateQ impl₁ oa).run
      (simulateQ impl₂ oa).run
      (EqRel (α × ω)) := by
  -- `WriterT.run` is the identity on the underlying computation, so pointwise agreement of the
  -- two handlers' `.run`s already is equality of the handlers themselves
  obtain rfl : impl₁ = impl₂ := QueryImpl.ext himpl_eq
  exact relTriple_refl _

/-- Output projection of `relTriple_simulateQ_run_writerT`: the same monoid-congruence
hypotheses couple the two `WriterT` simulations, but the conclusion retains only equality of the
returned values, discarding the accumulated logs entirely.

Applying it: the hypotheses are exactly those of `relTriple_simulateQ_run_writerT`, so `R_writer`
must still be a monoid congruence even though it no longer appears in the conclusion — it is what
carries the coupling across each bind. Reach for this form when the accumulator is bookkeeping
(a query counter, a transcript) whose value is irrelevant downstream, and keep the unprojected
rule when a later step still needs the log relation.

Unlike `relTriple_simulateQ_run_writerT_of_impl_eq`, the two handlers here may differ, may run
over different oracle specs, and may accumulate in different monoids; the price is the explicit
congruence `R_writer` in place of a pointwise equality of handlers. -/
theorem relTriple_simulateQ_run_writerT'
    {ω₁ ω₂ : Type} [Monoid ω₁] [Monoid ω₂]
    (impl₁ : QueryImpl spec (WriterT ω₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (WriterT ω₂ (OracleComp spec₂)))
    (R_writer : ω₁ → ω₂ → Prop)
    (hR_one : R_writer 1 1)
    (hR_mul : ∀ w₁ w₁' w₂ w₂', R_writer w₁ w₂ → R_writer w₁' w₂' →
      R_writer (w₁ * w₁') (w₂ * w₂'))
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain),
      RelTriple ((impl₁ t).run) ((impl₂ t).run)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_writer p₁.2 p₂.2)) :
    RelTriple
      (Prod.fst <$> (simulateQ impl₁ oa).run)
      (Prod.fst <$> (simulateQ impl₂ oa).run)
      (EqRel α) :=
  relTriple_map (relTriple_post_mono
    (relTriple_simulateQ_run_writerT impl₁ impl₂ R_writer hR_one hR_mul oa himpl)
    fun _ _ hp => hp.1)

/-- If two stateful oracle implementations agree on every query while `Inv` holds, and the
second implementation preserves `Inv`, then the full simulations have identical `(output, state)`
distributions from any invariant-satisfying initial state. -/
theorem relTriple_simulateQ_run_of_impl_eq_preservesInv
    {ι : Type} {spec : OracleSpec ι} {σ : Type _}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop)
    (oa : OracleComp spec α)
    (himpl_eq : ∀ (t : spec.Domain) (s : σ), Inv s → (impl₁ t).run s = (impl₂ t).run s)
    (hpres₂ : ∀ (t : spec.Domain) (s : σ), Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (s : σ) (hs : Inv s) :
    RelTriple
      ((simulateQ impl₁ oa).run s)
      ((simulateQ impl₂ oa).run s)
      (fun p₁ p₂ => p₁ = p₂ ∧ Inv p₁.2) := by
  have hrel :
      RelTriple
        ((simulateQ impl₁ oa).run s)
        ((simulateQ impl₂ oa).run s)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ p₁.2 = p₂.2 ∧ Inv p₁.2) := by
    refine relTriple_simulateQ_run (spec := spec) (spec₁ := unifSpec) (spec₂ := unifSpec)
      impl₁ impl₂ (fun s₁ s₂ => s₁ = s₂ ∧ Inv s₁) oa ?_ s s
      ⟨rfl, hs⟩
    intro t s₁ s₂ hs'
    rcases hs' with ⟨rfl, hs₁⟩
    rw [himpl_eq t s₁ hs₁]
    refine relTriple_refl_of_mem_support ((impl₂ t).run s₁) ?_
    intro a ha
    exact ⟨rfl, rfl, hpres₂ t s₁ hs₁ a ha⟩
  refine relTriple_post_mono hrel ?_
  intro p₁ p₂ hp
  exact ⟨Prod.ext hp.1 hp.2.1, hp.2.2⟩

/-- Exact-equality specialization of `relTriple_simulateQ_run_of_impl_eq_preservesInv`.

This weakens the stronger invariant-carrying postcondition to plain equality on `(output, state)`,
which is the shape consumed directly by probability-transport lemmas and theorem-driven
`rvcgen` steps. -/
theorem relTriple_simulateQ_run_eqRel_of_impl_eq_preservesInv
    {ι : Type} {spec : OracleSpec ι} {σ : Type _}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → Prop)
    (oa : OracleComp spec α)
    (himpl_eq : ∀ (t : spec.Domain) (s : σ), Inv s → (impl₁ t).run s = (impl₂ t).run s)
    (hpres₂ : ∀ (t : spec.Domain) (s : σ), Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (s : σ) (hs : Inv s) :
    RelTriple
      ((simulateQ impl₁ oa).run s)
      ((simulateQ impl₂ oa).run s)
      (EqRel (α × σ)) := by
  refine relTriple_post_mono
    (relTriple_simulateQ_run_of_impl_eq_preservesInv
      impl₁ impl₂ Inv oa himpl_eq hpres₂ s hs) ?_
  intro p₁ p₂ hp
  exact hp.1

/-- Relational form of `OracleComp.run'_simulateQ_eq_of_query_map_eq`: if every oracle call under
`impl₁` becomes the corresponding `impl₂` call after mapping the state along `proj`, then running
`oa` from `s` under `impl₁` and from `proj s` under `impl₂` gives outputs related by equality.

Registered as a `@[vcspec]` rule, so `rvcgen` / `rvcstep` can close an output-equality goal between
two `StateT` simulations and leave `hproj` as the only side goal: the state spaces and `proj` are
already determined by unification against the goal.

The neighbouring rules tie the two state spaces together more loosely — `relTriple_simulateQ_run'`
through an arbitrary state invariant plus a per-query relational triple, and
`relTriple_simulateQ_run'_of_impl_evalDistEq` through per-query equality in distribution on a shared
state space. Reach for this one when the second implementation is the first one read through a
state projection, so that `hproj` is an equality of computations rather than of distributions. -/
theorem relTriple_simulateQ_run'_of_query_map_eq
    {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ : Type _}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s, Prod.map id proj <$> (impl₁ t).run s = (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) :
    RelTriple
      ((simulateQ impl₁ oa).run' s)
      ((simulateQ impl₂ oa).run' (proj s))
      (EqRel α) :=
  relTriple_eqRel_of_eq <| OracleComp.run'_simulateQ_eq_of_query_map_eq impl₁ impl₂ proj hproj oa s

end coupling

/-- Query-bounded exact-output transport for `simulateQ`.

If `oa` satisfies a structural query bound `IsQueryBound budget canQuery cost`, the two
implementations agree on every query that the bound permits, and the second implementation
preserves a budget-indexed invariant `Inv`, then the full simulated computations have the same
output-state measure from any initial state satisfying `Inv`. -/
theorem evalDistEq_simulateQ_run_of_impl_eq_queryBound
    {ι : Type} {spec : OracleSpec ι} {σ : Type} {B : Type _}
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (Inv : σ → B → Prop)
    (canQuery : spec.Domain → B → Prop)
    (cost : spec.Domain → B → B)
    (oa : OracleComp spec α)
    (budget : B)
    (hbound : oa.IsQueryBound budget canQuery cost)
    (himpl_eq : ∀ (t : spec.Domain) (s : σ) (b : B),
      Inv s b → canQuery t b → (impl₁ t).run s = (impl₂ t).run s)
    (hpres₂ : ∀ (t : spec.Domain) (s : σ) (b : B), Inv s b → canQuery t b →
      ∀ z ∈ support ((impl₂ t).run s), Inv z.2 (cost t b))
    (s : σ) (hs : Inv s budget) :
    (simulateQ impl₁ oa).run s =ᵈ (simulateQ impl₂ oa).run s := by
  refine evalDistEq_iff_evalDist_eq.mpr ?_
  let : MeasurableSpace (α × σ) := ⊤
  induction oa using OracleComp.inductionOn generalizing s budget with
  | pure x => rfl
  | query_bind t oa ih =>
      rw [isQueryBound_query_bind_iff] at hbound
      rcases hbound with ⟨hcan, hcont⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [himpl_eq t s budget hs hcan]
      exact evalDist_bind_congr_of_support _ _ _ fun p hp =>
        ih p.1 (cost t budget) (hcont p.1) p.2 (hpres₂ t s budget hs hcan p hp)

/-! ## Stochastic dominance through `simulateQ` -/

/-- **Marginal stochastic dominance through `simulateQ` (self-referential / Fubini form).**

The marginal counterpart of `relTriple_simulateQ_run_mono`. Where the latter demands a
*pointwise* per-step coupling whose support respects an output-and-state relation, this lemma
demands only a *marginal* per-step inequality: at every query and every pair of `R`-related
states, the one-step run of `impl₁` followed by *any* left tail `k₁` has bad-marginal at most
the one-step run of `impl₂` followed by *any* right tail `k₂`, provided the two tails are
themselves marginally bad-dominated from every pair of `R`-related successor states.

This is the right shape when the two handlers genuinely diverge on the answer distribution at a
single step (e.g. an eager deterministic ghost read vs. a deferred-sampling read), so no
pointwise coupling can dominate the bad flag at that step, yet the *marginal* bad mass — the
`tsum` over the deferred draw, taken before the divergent continuation is applied — is still
ordered (Fubini / tsum-swap). The per-step premise is self-referential by design: discharging
it at the divergent step is exactly the marginal draw-commutation, the hard content this lemma
isolates from the free-monad bookkeeping.

The base hypothesis `h_base` (`R s₁ s₂ → bad₁ s₁ → bad₂ s₂`) discharges the `pure` leaf, where no
further step can repair the bad flag: there the bad marginal is exactly the indicator of the
current state, so `R` must already carry the bad implication.

Applying it: `h_step` carries the entire probabilistic obligation, and it is quantified over
*arbitrary* tails, so it may be discharged query-by-query — trivially wherever the two handlers
agree, and by the marginal draw-commutation at the one query where they diverge. Reach instead
for the sibling `prEvent_dist_simulateQ_mono` when no pointwise state relation exists at all:
that version uses a relation on the two *run distributions*, which applies when the successor
states are related only through a coupling over a deferred draw, at the price of also having to
seed the relation at every `pure` leaf. -/
theorem prEvent_marginal_simulateQ_mono
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (R : σ₁ → σ₂ → Prop)
    (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (h_base : ∀ (s₁ : σ₁) (s₂ : σ₂), R s₁ s₂ → bad₁ s₁ → bad₂ s₂)
    (h_step : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂), R s₁ s₂ →
      ∀ {γ : Type} (k₁ : (spec.Range t × σ₁) → OracleComp spec₁ (γ × σ₁))
        (k₂ : (spec.Range t × σ₂) → OracleComp spec₂ (γ × σ₂)),
        (∀ (u : spec.Range t) (s₁' : σ₁) (s₂' : σ₂), R s₁' s₂' →
          Pr{let z ← k₁ (u, s₁')}[bad₁ z.2] ≤ Pr{let z ← k₂ (u, s₂')}[bad₂ z.2]) →
        Pr{let z ← (impl₁ t).run s₁ >>= k₁}[bad₁ z.2] ≤
          Pr{let z ← (impl₂ t).run s₂ >>= k₂}[bad₂ z.2])
    (oa : OracleComp spec α) (s₁ : σ₁) (s₂ : σ₂) (hR : R s₁ s₂) :
    Pr{let z ← (simulateQ impl₁ oa).run s₁}[bad₁ z.2] ≤
      Pr{let z ← (simulateQ impl₂ oa).run s₂}[bad₂ z.2] := by
  classical
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure a =>
    -- both sides are point masses on `(a, s₁)` / `(a, s₂)`; reduce to the base implication.
    simp only [simulateQ_pure, StateT.run_pure]
    rw [prEvent_pure, prEvent_pure]
    by_cases hb : bad₁ s₁
    · simp [hb, h_base s₁ s₂ hR hb]
    · simp [hb]
  | query_bind t ob ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    exact h_step t s₁ s₂ hR _ _ ih

/-- **Distribution-level stochastic dominance through `simulateQ`.**

The *distribution-level* sibling of `prEvent_marginal_simulateQ_mono`. Where the latter carries
a **pointwise** state relation `R : σ₁ → σ₂ → Prop` and discharges the per-query step at every pair
of `R`-related *states*, this lemma carries a relation `Rrun` directly on the two run
**distributions** (the whole `OracleComp spec₁ (γ × σ₁)` / `OracleComp spec₂ (γ × σ₂)`
computations), generic over the output type `γ`. This is the shape needed when the per-step
recoupling is inherently *joint-law* — e.g. an eager handler that has already committed sampled
keys into its state versus a deferred-sampling handler that only carries a pending *count*, so that
no pointwise state predicate relates the two successor states yet the two run distributions are
related by a coupling over the deferred draw.

The entire probabilistic content is isolated into the three premises:

* `h_pure` seeds the relation at the `pure` leaves (the run distributions are the two point masses
  `pure (a, s₁)` / `pure (a, s₂)`);
* `h_bind` is the distribution-level bind congruence: given a query `t` and any two tails `k₁ k₂`
  whose per-output continuations are already `Rrun`-related, the one-step runs followed by those
  tails are again `Rrun`-related. Discharging `h_bind` at a divergent step *is* the marginal
  draw-commutation, the hard content this lemma isolates;
* `h_bad` reads the ordered bad marginals off any `Rrun`-related pair of run distributions.

Applying it: nothing relates the initial states `s₁ s₂`, because `h_pure` is quantified over *all*
leaves and so already seeds `Rrun` wherever the induction reaches one. That is the trade against
`prEvent_marginal_simulateQ_mono`, which seeds only from its `R`-related base but must then
exhibit a pointwise `R` relating the successor states at every step. -/
theorem prEvent_dist_simulateQ_mono
    {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂)))
    (Rrun : ∀ {γ : Type}, OracleComp spec₁ (γ × σ₁) → OracleComp spec₂ (γ × σ₂) → Prop)
    (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (h_pure : ∀ {γ : Type} (a : γ) (s₁ : σ₁) (s₂ : σ₂),
      Rrun (pure (a, s₁)) (pure (a, s₂)))
    (h_bind : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      ∀ {γ : Type} (k₁ : (spec.Range t × σ₁) → OracleComp spec₁ (γ × σ₁))
        (k₂ : (spec.Range t × σ₂) → OracleComp spec₂ (γ × σ₂)),
        (∀ (u : spec.Range t) (s₁' : σ₁) (s₂' : σ₂), Rrun (k₁ (u, s₁')) (k₂ (u, s₂'))) →
        Rrun ((impl₁ t).run s₁ >>= k₁) ((impl₂ t).run s₂ >>= k₂))
    (h_bad : ∀ {γ : Type} (r₁ : OracleComp spec₁ (γ × σ₁)) (r₂ : OracleComp spec₂ (γ × σ₂)),
      Rrun r₁ r₂ → Pr{let z ← r₁}[bad₁ z.2] ≤ Pr{let z ← r₂}[bad₂ z.2])
    (oa : OracleComp spec α) (s₁ : σ₁) (s₂ : σ₂) :
    Pr{let z ← (simulateQ impl₁ oa).run s₁}[bad₁ z.2] ≤
      Pr{let z ← (simulateQ impl₂ oa).run s₂}[bad₂ z.2] := by
  -- the induction is pure free-monad bookkeeping; `h_bad` reads the marginals off `Rrun`
  refine h_bad _ _ ?_
  induction oa using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure a =>
    -- both run distributions are the point masses `pure (a, s₁)` / `pure (a, s₂)`
    simpa using h_pure a s₁ s₂
  | query_bind t ob ih =>
    simpa using h_bind t s₁ s₂ _ _ ih

end OracleComp.ProgramLogic.Relational
