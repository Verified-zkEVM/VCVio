/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Deferred sampling: tape factorization of answer-irrelevant draws

This module collects the reusable, scheme-independent kernels behind the
*deferred-sampling* technique: rewriting a probabilistic computation whose per-step
draws do not influence the control flow into one where those draws are *front-loaded*
into a single independent "tape", drawn ahead of time and then consumed.

The technique underlies several proofs in this library (Fiat–Shamir with abort, GPV
preimage sampling, collision/birthday bounds). Those proofs each instantiate a bespoke
state machine; what is genuinely generic — and lives here — is:

* **i.i.d. bind-commutation**: an answer-irrelevant draw commutes past its continuation at the
  level of output measures (`OracleComp.evalDist_bind_bind_swap`), a lossless value-irrelevant
  prefix can be dropped, and continuations with equal output measures on every reachable value
  give equal output measures after a draw (`OracleComp.evalDist_bind_congr_of_support`).
* **The list-multiplicity ε-kernel** (`lintegral_count_le`): one fresh draw, independent of a
  value-free list `rl`, contributes expected multiplicity `E[rl.count key] ≤ ε · rl.length`
  whenever each slot is hit with probability `≤ ε`. This is the single source of the `ε` in
  deferred-sampling read bounds.
* **The general factorization statement** (`DeferredTape.Factorizes`): an abstract
  predicate packaging "the read-recording run distributes as a single front draw block
  followed by a tape-consuming run". Scheme-specific factorizations are instances of this shape;
  the predicate names the target so downstream consumers share vocabulary.

The genuinely hard, scheme-specific glue — proving a particular state machine's run *is*
a tape factorization — is not generic and stays with each scheme. What this module
provides is the toolbox that those proofs are built out of.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleComp.DeferredSampling

/-! ## The list-multiplicity ε-kernel

The single source of the `ε` in a deferred-sampling read bound: one fresh draw,
independent of a value-free list, hits each list slot with probability `≤ ε`. -/

/-- **The atomic value-free charge.** One fresh draw `w ← oa : ProbComp (C × P)`,
*independent of* a value-free list `rl : List C`, contributes expected multiplicity
`E[rl.count (key w)] ≤ ε · rl.length`: each of the `rl.length` slots of `rl` is hit by the
fresh draw's key with probability at most `ε`.

Stated for `key = Prod.fst` (a draw of a `(C × P)`-pair, of which only the `C`-component is
matched against the list), as it arises when a commitment draw carries an auxiliary private
state. This is the irreducible probabilistic kernel of a deferred-sampling read bound. -/
lemma lintegral_count_le {C P : Type} [DecidableEq C] [MeasurableSpace C]
    [DiscreteMeasurableSpace C] (oa : ProbComp (C × P)) (rl : List C) (ε : ℝ≥0∞)
    (hGuess : ∀ cm : C, Pr{let w ← oa}[w.1 = cm] ≤ ε) :
    ∫⁻ c, (rl.count c : ℝ≥0∞) ∂𝒟[Prod.fst <$> oa] ≤ ε * rl.length := by
  induction rl with
  | nil => simp
  | cons a rl ih =>
    have hsplit : (fun c => ((a :: rl).count c : ℝ≥0∞)) =
        fun c => ({a} : Set C).indicator 1 c + (rl.count c : ℝ≥0∞) := by
      funext c
      by_cases h : c = a
      · subst h; simp [add_comm]
      · simp [h, Ne.symm h]
    have hmass : 𝒟[Prod.fst <$> oa] {a} ≤ ε := by
      rw [← prEvent_eq_evalDist_singleton, prEvent_map]
      exact hGuess a
    rw [hsplit, lintegral_add_left (measurable_one.indicator (MeasurableSet.singleton a)),
      lintegral_indicator_one (MeasurableSet.singleton a)]
    calc 𝒟[Prod.fst <$> oa] {a} + ∫⁻ c, (rl.count c : ℝ≥0∞) ∂𝒟[Prod.fst <$> oa]
        ≤ ε + ε * rl.length := add_le_add hmass ih
      _ = ε * (a :: rl).length := by rw [List.length_cons]; push_cast; ring

/-! ## The general factorization shape

The hard, scheme-specific content of deferred sampling is proving that a particular
read-recording run *equals* a front-tape factorization. The shape of that target is
generic and named here, so that scheme instances and downstream consumers share a single
vocabulary. -/

/-- **The deferred-tape factorization predicate.** `Factorizes run tape tapeRun` asserts
that running the deferred-draw computation `run : ProbComp γ` is distributionally identical
to first drawing an independent front tape `tape : ProbComp τ` and then running the
tape-consuming variant `tapeRun : τ → ProbComp γ` that reads its per-step draws off the
tape head-first: the two computations agree on every event.

A scheme establishes this by induction on its adversary computation: at an
*answer-irrelevant* step the front tape commutes past the query (`evalDistEq_step_commute_tape`),
and at a *drawing* step the inline draw block is split off the front tape. -/
def Factorizes {γ τ : Type} (run : ProbComp γ) (tape : ProbComp τ)
    (tapeRun : τ → ProbComp γ) : Prop :=
  run =ᵈ (tape >>= tapeRun)

/-- A factorization may be rewritten through any continuation: if `run` factorizes through
`tape`/`tapeRun`, then binding a continuation `k` after `run` factorizes through `tape` and
`tapeRun >=> k`. This is the recombination step used when a factorized head feeds a fold. -/
theorem Factorizes.bind {γ τ δ : Type} {run : ProbComp γ} {tape : ProbComp τ}
    {tapeRun : τ → ProbComp γ} (h : Factorizes run tape tapeRun) (k : γ → ProbComp δ) :
    Factorizes (run >>= k) tape (fun t => tapeRun t >>= k) := by
  unfold Factorizes at h ⊢
  rw [← bind_assoc]
  exact h.bind_left k

/-! ## The answer-irrelevant step commute (the framework induction step)

The inductive heart of a tape factorization is: at a query whose per-step draw does *not* consult
the tape, the front tape commutes past the step. This is the abstract, state-shape-independent form
of that step — it takes the per-continuation factorization as a hypothesis (the inductive
hypothesis) and concludes the factorization for one more leading answer-irrelevant step. Drawing and
read steps are handled by their own (scheme-specific) splice/commute; this is the
*answer-irrelevant* case, which is fully generic. -/

/-- **Answer-irrelevant step commutes past the front tape.** An answer-irrelevant step
`step : ProbComp (Ans × S)` (a query whose answer-draw does not consult the front tape) composed
with a deferred continuation `defCont` factors as the front tape `tape : ProbComp τ` drawn first,
followed by a tape-threaded continuation:

* `defCont a s' : ProbComp (γ × S)` is the deferred continuation after the step;
* `tapeCont a (s', t) : ProbComp (γ × ρ)` is its tape-consuming variant, threading the tape `t`;
* `proj : γ × ρ → γ × S` discards the spent-tape suffix on output.

Given the per-continuation factorization `hcont` (supplied by the inductive hypothesis), the leading
answer-irrelevant step commutes past the front draw block: the continuation is rewritten by `hcont`
under the step bind, the front tape commutes past the answer-irrelevant step, and the inner step
bind is re-associated into the mapped tape-step form. -/
theorem evalDistEq_step_commute_tape {γ S Ans τ ρ : Type}
    (step : ProbComp (Ans × S)) (tape : ProbComp τ)
    (proj : γ × ρ → γ × S)
    (defCont : Ans → S → ProbComp (γ × S))
    (tapeCont : Ans → S × τ → ProbComp (γ × ρ))
    (hcont : ∀ (a : Ans) (s' : S),
      defCont a s' =ᵈ (tape >>= fun t => proj <$> tapeCont a (s', t))) :
    (step >>= fun p => defCont p.1 p.2) =ᵈ
      (tape >>= fun t =>
          proj <$>
            (((fun p : Ans × S => (p.1, (p.2, t))) <$> step) >>= fun p => tapeCont p.1 p.2)) := by
  refine evalDistEq_iff_evalDist_eq.mpr ?_
  let : MeasurableSpace (γ × S) := ⊤
  rw [evalDist_bind_congr_of_support step (fun p => defCont p.1 p.2)
      (fun p => tape >>= fun t => proj <$> tapeCont p.1 (p.2, t))
      fun p _ => (hcont p.1 p.2).evalDist_eq,
    OracleComp.evalDist_bind_bind_swap step tape]
  refine evalDist_bind_congr_of_support tape _ _ fun t _ => ?_
  rw [bind_map_left, map_bind]

/-! ## State-relation transfer for expected output functionals

The value-substitution lemmas of deferred sampling (e.g. "the recorded read list of the run is
independent of the rejected-draw content of the start state") are instances of a single generic
fact: an expected output functional through `simulateQ impl` of a `StateT σ ProbComp` handler is
equal at two start states related by `Rel`, provided every query step transfers `Rel` to its
continuation and the functional is `Rel`-invariant. -/

/-- **State-relation transfer for an expected output functional.** Let
`impl : QueryImpl spec (StateT σ ProbComp)` and let `Rel : σ → σ → Prop` be a relation on the
handler state. Suppose:

* every query step transfers `Rel`: for `Rel`-related start states and any `Rel`-invariant
  continuation functional `K`, the per-query expected `K` agrees at the two states (`hstep`);
* the output functional `F : γ → σ → ℝ≥0∞` is `Rel`-invariant (`hF`).

Then the run-level expected output `wp⟦(simulateQ impl oa).run s⟧ fun z => F z.1 z.2` agrees at
`Rel`-related start states. The proof inducts on `oa`: at `pure` the output is the start state
(`hF` applies); at a query bind the step's expected continuation functional is itself
`Rel`-invariant by the inductive hypothesis, so `hstep` closes the step. -/
theorem wp_simulateQ_run_eq_of_rel
    {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    {γ : Type} (oa : OracleComp spec γ)
    (Rel : σ → σ → Prop)
    (hstep : ∀ (t : spec.Domain) (s₁ s₂ : σ), Rel s₁ s₂ →
      ∀ (K : spec.Range t → σ → ℝ≥0∞),
        (∀ (b : spec.Range t) (t₁ t₂ : σ), Rel t₁ t₂ → K b t₁ = K b t₂) →
        wp⟦(impl t).run s₁⟧ (fun p => K p.1 p.2) = wp⟦(impl t).run s₂⟧ (fun p => K p.1 p.2)) :
    ∀ (F : γ → σ → ℝ≥0∞), (∀ (g : γ) (s₁ s₂ : σ), Rel s₁ s₂ → F g s₁ = F g s₂) →
      ∀ (s₁ s₂ : σ), Rel s₁ s₂ →
        wp⟦(simulateQ impl oa).run s₁⟧ (fun z => F z.1 z.2) =
          wp⟦(simulateQ impl oa).run s₂⟧ (fun z => F z.1 z.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro F hF s₁ s₂ hs
      simp only [simulateQ_pure, StateT.run_pure, ExpectationWP.wp_pure]
      exact hF a s₁ s₂ hs
  | query_bind t ob ih =>
      intro F hF s₁ s₂ hs
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, ExpectationWP.wp_bind]
      exact hstep t s₁ s₂ hs _ fun b t₁ t₂ ht => ih b F hF t₁ t₂ ht

end OracleComp.DeferredSampling
