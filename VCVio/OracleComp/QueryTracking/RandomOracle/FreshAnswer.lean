/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.ProbabilityNotation

/-!
# The potential engine for random-oracle runs

A bad event of a random-oracle run is typically a predicate on the state that, once it holds,
keeps holding, and that a step makes fire with mass at most what the step adds to a potential: a
*fresh* answer of a lazy random oracle, for instance, pays `ε` to the cache-size potential
`enncard · * ε`.  This module turns such per-step charges into a bound on a whole run followed by
a continuation.

A handler `so : QueryImpl spec (StateT σ ProbComp)` charges a state predicate `P` to a potential
`Φ` (`IsPotentialStep so P Φ`) when no step lowers `Φ` and every step out of a non-firing state is
either deterministic and still non-firing, or a sample whose firing mass is at most the increment
of `Φ` that the step pays.  The engine is `evalDist_bind_apply_setOf_and_le_of_potential`: the run
is followed by a terminal continuation `g` on its final output and state, charged by its own
hypothesis: from a final state where `P` fails, `g` fires its event below the budget `K` with mass
at most `K - Φ`, and never lowers the potential.  Then from a state `s` where `P` fails, the run
followed by `g` fires below `K` with mass at most `K - Φ s`.  Taking `g` to be a second run, under
a second handler and with its own bad predicate and potential on its own state, gives the
two-phase bound `evalDist_bind_run_apply_setOf_and_le_of_potential`: both phases are charged
against one budget, the second through the engine itself, provided the handover from the first
final state to the second start state keeps the bad predicate failing and does not lower the
potential.  Taking `g` to be an independent draw `x ← mx`, whose hazard `H x` fires at each final
state with probability at most a weight `c`, gives `prEvent_bind_draw_and_le_of_potential`, which
charges the draw `c` on top of the potential.

## Scope

* No bad event is defined here and no union bound over several bad events is taken.  `P` is an
  arbitrary predicate on the state and `Φ` an arbitrary `ℝ≥0∞`-valued potential.
* The measurable-space arguments of the `𝒟[…] {z | …}` statements are pinned to `⊤` by a `letI`
  inside the statement rather than taken as instance arguments: the induction of the engine
  changes the result type, so no instance argument could be fixed across it.  Pinning `⊤` is
  lossless wherever `DiscreteMeasurableSpace` holds, since that instance makes every set
  measurable and so equals `⊤`; the statement is therefore the one a
  `[MeasurableSpace] [DiscreteMeasurableSpace]` formulation would give, and strictly stronger in
  general.  A consumer must fix `⊤` as well, and rewriting a set equality under such a `𝒟[…]`
  needs `simp [h]` rather than `rw [h]`, since the instance is not syntactically the ambient one.
  The `prEvent_…` forms state the same bounds with the events observed in `Prop` by
  `Pr{…}[…]`, and take no measurable-space argument at all.
* In the two-phase bound the second handler `so₂`, its bad predicate `P₂` and its potential `Φ₂`
  are fixed independently of the handover: they cannot depend on the first phase's output or
  final state.  When the second phase's predicate depends on the first phase's result, or a
  third phase follows, either use the continuation form with the dependence inside `g` (the
  continuation forms nest), or lift the second phase's state so that it carries the first
  phase's data.
* Nothing here is quantum: the handlers are classical stateful samplers.

## Labels

Seven declarations.

*The potential engine*:

* `OracleComp.le_of_mem_support_run_simulateQ_of_step`, `OracleComp.IsPotentialStep`,
  `OracleComp.evalDist_bind_apply_setOf_and_le_of_potential`,
  `OracleComp.prEvent_bind_and_le_of_potential`,
  `OracleComp.prEvent_bind_draw_and_le_of_potential`.

*Two phases*:

* `OracleComp.evalDist_bind_run_apply_setOf_and_le_of_potential`,
  `OracleComp.prEvent_bind_run_and_le_of_potential`.
-/

public section

open OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleComp

/-! ## The potential engine -/

section Potential

variable {ι : Type} {spec : OracleSpec ι} {σ α τ : Type}

/-- A potential that never decreases along a step never decreases along a whole run. -/
theorem le_of_mem_support_run_simulateQ_of_step (so : QueryImpl spec (StateT σ ProbComp))
    (Φ : σ → ℝ≥0∞) (hmono : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s), Φ s ≤ Φ z.2)
    (oa : OracleComp spec α) (s : σ) {z : α × σ} (hz : z ∈ support ((simulateQ so oa).run s)) :
    Φ s ≤ Φ z.2 :=
  simulateQ_run_preservesInv so (Φ s ≤ Φ ·) (fun t s' hs' z hz => hs'.trans (hmono t s' z hz))
    oa s le_rfl z hz

/-- A handler `so` charges the bad predicate `P` to the potential `Φ`: no step lowers `Φ`, and
every step out of a state where `P` fails is either deterministic and lands again where `P`
fails, or a sample `samp` with state update `upd` that fires `P` with probability at most a
weight `w` that the step adds to `Φ`. -/
structure IsPotentialStep (so : QueryImpl spec (StateT σ ProbComp)) (P : σ → Prop)
    (Φ : σ → ℝ≥0∞) : Prop where
  /-- No step lowers the potential. -/
  mono : ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((so t).run s), Φ s ≤ Φ z.2
  /-- A step out of a state where `P` fails is deterministic and lands again where `P` fails, or
  is a sample whose probability of firing `P` is at most a weight that it adds to `Φ`. -/
  step : ∀ (t : spec.Domain) (s : σ), ¬ P s →
    (∃ a s', (so t).run s = pure (a, s') ∧ ¬ P s') ∨
    (∃ (samp : ProbComp (spec.Range t)) (upd : spec.Range t → σ) (w : ℝ≥0∞),
      (so t).run s = (fun u => (u, upd u)) <$> samp ∧
      Pr{let u ← samp}[P (upd u)] ≤ w ∧
      ∀ u, w + Φ s ≤ Φ (upd u))

/-- **The potential-charged first-fire bound with a terminal continuation.**  The handler `so`
charges the bad predicate `P` to the potential `Φ` (`IsPotentialStep`).  The run is followed by a
continuation `g` on its final output and state, whose result carries an event `Q` and a potential
`Ψ`: `g` never yields a `Ψ` below the `Φ` of the state it starts from, and from a final state
where `P` fails it fires `Q` with `Ψ ≤ K` with mass at most `K - Φ`.  Then from a state where
`P` fails the run followed by `g` fires `Q` with `Ψ ≤ K` with mass at most `K - Φ s`.

The measurable-space instance on `τ` is pinned to `⊤` inside the statement; a consumer must fix
`⊤` too. -/
theorem evalDist_bind_apply_setOf_and_le_of_potential {so : QueryImpl spec (StateT σ ProbComp)}
    {P : σ → Prop} {Φ : σ → ℝ≥0∞} (h : IsPotentialStep so P Φ)
    (g : α × σ → ProbComp τ) (Q : τ → Prop) (Ψ : τ → ℝ≥0∞) (K : ℝ≥0∞) (hK' : K ≠ ⊤)
    (hgmono : ∀ z, ∀ y ∈ support (g z), Φ z.2 ≤ Ψ y)
    (hg : ∀ z, ¬ P z.2 →
      (letI : MeasurableSpace τ := ⊤; 𝒟[g z] {y | Q y ∧ Ψ y ≤ K} ≤ K - Φ z.2))
    (oa : OracleComp spec α) :
    ∀ s : σ, ¬ P s →
      (letI : MeasurableSpace τ := ⊤;
        𝒟[(simulateQ so oa).run s >>= g] {y | Q y ∧ Ψ y ≤ K} ≤ K - Φ s) := by
  let _ : MeasurableSpace τ := ⊤
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s hs
    rw [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hg (x, s) hs
  | query_bind t k ih =>
    intro s hs
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases h.step t s hs with ⟨a, s', hrun, hs'⟩ | ⟨samp, upd, w, hrun, hw, hΦ⟩
    · rw [hrun, pure_bind]
      exact (ih a s' hs').trans (tsub_le_tsub_left (h.mono t s (a, s')
        (by rw [hrun, support_pure]; exact Set.mem_singleton _)) K)
    · rw [hrun]
      let _ : MeasurableSpace (spec.Range t) := ⊤
      let _ : MeasurableSpace (spec.Range t × σ) := ⊤
      rw [prEvent_eq_evalDist_of_discrete] at hw
      have hpath : ∀ y ∈ support (((fun u => (u, upd u)) <$> samp) >>= fun p =>
          (simulateQ so (k p.1)).run p.2 >>= g), w + Φ s ≤ Ψ y := by
        intro y hy
        rw [mem_support_bind_iff] at hy
        obtain ⟨p, hp, hy⟩ := hy
        rw [support_map] at hp
        obtain ⟨u, -, rfl⟩ := hp
        rw [mem_support_bind_iff] at hy
        obtain ⟨z, hz, hy⟩ := hy
        exact (hΦ u).trans ((le_of_mem_support_run_simulateQ_of_step so Φ h.mono (k u) (upd u)
          hz).trans (hgmono z y hy))
      by_cases hK : w + Φ s ≤ K
      · have hbadBound : 𝒟[(fun u => (u, upd u)) <$> samp]
            {p : spec.Range t × σ | P p.2 ∨ ∀ u, p ≠ (u, upd u)} ≤ w := by
          rw [evalDist_map_of_discrete, Measure.map_apply Measurable.of_discrete
            MeasurableSet.of_discrete]
          refine le_trans (le_of_eq (congrArg _ ?_)) hw
          ext u
          exact ⟨fun h => h.elim id fun h => absurd rfl (h u), Or.inl⟩
        refine (evalDist_bind_apply_le_add_of_bad _ _ Measurable.of_discrete
          MeasurableSet.of_discrete MeasurableSet.of_discrete hbadBound (ε₂ := K - (w + Φ s))
          ?_).trans (le_of_eq ?_)
        · rintro ⟨u, s'⟩ hgood
          have hP : ¬ P s' := fun h => hgood (Or.inl h)
          obtain ⟨u', hu'⟩ : ∃ u', (u, s') = (u', upd u') := by
            by_contra h
            exact hgood (Or.inr fun u' hu' => h ⟨u', hu'⟩)
          obtain ⟨h1, h2⟩ := Prod.mk.inj hu'
          subst h1 h2
          exact (ih u (upd u) hP).trans (tsub_le_tsub_left (hΦ u) K)
        · rw [tsub_add_eq_tsub_tsub_swap, add_tsub_cancel_of_le (ENNReal.le_sub_of_add_le_right
            (ne_top_of_le_ne_top hK' (le_add_self.trans hK)) hK)]
      · rw [evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete]
        · exact zero_le
        · exact fun y hy hmem => hK ((hpath y hy).trans hmem.2)

/-- **The potential-charged first-fire bound with a terminal continuation, as an event
probability.**  The handler `so` charges the bad predicate `P` to the potential `Φ`
(`IsPotentialStep`).  The run is followed by a continuation `g` on its final output and state,
whose result carries an event `Q` and a potential `Ψ`: `g` never yields a `Ψ` below the `Φ` of
the state it starts from, and from a final state where `P` fails it fires `Q` with `Ψ ≤ K` with
probability at most `K - Φ`.  Then from a state where `P` fails the run followed by `g` fires `Q`
with `Ψ ≤ K` with probability at most `K - Φ s`. -/
theorem prEvent_bind_and_le_of_potential {so : QueryImpl spec (StateT σ ProbComp)}
    {P : σ → Prop} {Φ : σ → ℝ≥0∞} (h : IsPotentialStep so P Φ)
    (g : α × σ → ProbComp τ) (Q : τ → Prop) (Ψ : τ → ℝ≥0∞) (K : ℝ≥0∞) (hK' : K ≠ ⊤)
    (hgmono : ∀ z, ∀ y ∈ support (g z), Φ z.2 ≤ Ψ y)
    (hg : ∀ z, ¬ P z.2 → Pr{let y ← g z}[Q y ∧ Ψ y ≤ K] ≤ K - Φ z.2)
    (oa : OracleComp spec α) (s : σ) (hs : ¬ P s) :
    Pr{let z ← (simulateQ so oa).run s; let y ← g z}[Q y ∧ Ψ y ≤ K] ≤ K - Φ s := by
  let _ : MeasurableSpace τ := ⊤
  rw [← bind_assoc, prEvent_eq_evalDist_of_discrete]
  refine evalDist_bind_apply_setOf_and_le_of_potential h g Q Ψ K hK' hgmono (fun z hz => ?_) oa
    s hs
  rw [← prEvent_eq_evalDist_of_discrete]
  exact hg z hz

/-- **The potential-charged first-fire bound with a terminal draw.**  The handler `so` charges
the bad predicate `P` to the potential `Φ` (`IsPotentialStep`).  The run is followed by an
independent draw `x ← mx`, and a hazard `H x` of the final state fires with probability at most
`c` of that state.  Then from a state where `P` fails, the run and the draw fire `P` or the
hazard, with `Φ + c ≤ K` at the final state, with probability at most `K - Φ s`: the draw is
charged its weight `c` on top of the potential. -/
theorem prEvent_bind_draw_and_le_of_potential {so : QueryImpl spec (StateT σ ProbComp)}
    {P : σ → Prop} {Φ : σ → ℝ≥0∞} (h : IsPotentialStep so P Φ) {S : Type} (mx : ProbComp S)
    (H : S → σ → Prop) (c : σ → ℝ≥0∞) (hH : ∀ s, Pr{let x ← mx}[H x s] ≤ c s) (K : ℝ≥0∞)
    (hK' : K ≠ ⊤) (oa : OracleComp spec α) (s : σ) (hs : ¬ P s) :
    Pr{let z ← (simulateQ so oa).run s; let x ← mx}[(P z.2 ∨ H x z.2) ∧ Φ z.2 + c z.2 ≤ K] ≤
      K - Φ s := by
  have key := prEvent_bind_and_le_of_potential h (fun z => (fun x => (z, x)) <$> mx)
    (fun y => P y.1.2 ∨ H y.2 y.1.2) (fun y => Φ y.1.2 + c y.1.2) K hK' (fun z y hy => ?_)
    (fun z hz => ?_) oa s hs
  · simpa only [bind_map_left] using key
  · rw [support_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact le_self_add
  · rw [prEvent_map]
    by_cases hle : Φ z.2 + c z.2 ≤ K
    · refine (prEvent_mono _ _ (fun x => H x z.2) fun x hx => hx.1.resolve_left hz).trans
        ((hH z.2).trans (ENNReal.le_sub_of_add_le_left
          (ne_top_of_le_ne_top hK' (le_self_add.trans hle)) hle))
    · rw [prEvent_eq_zero_of_forall_not _ _ fun x hx => hle hx.2]
      exact zero_le

end Potential

/-! ## Two phases -/

section TwoPhase

variable {ι ι₂ : Type} {spec : OracleSpec ι} {spec₂ : OracleSpec ι₂} {σ σ₂ α β : Type}
  {so₁ : QueryImpl spec (StateT σ ProbComp)} {P₁ : σ → Prop} {Φ₁ : σ → ℝ≥0∞}
  {so₂ : QueryImpl spec₂ (StateT σ₂ ProbComp)} {P₂ : σ₂ → Prop} {Φ₂ : σ₂ → ℝ≥0∞}

/-- **The potential-charged first-fire bound across two phases.**  A run under the handler `so₁`
is followed by a run of a program `ob z` under a second handler `so₂`, started from a state
`init z` computed from the first run's final output and state `z`.  Each handler charges its own
bad predicate to its own potential (`IsPotentialStep`; `P₁`, `Φ₁` on `σ` and `P₂`, `Φ₂` on `σ₂`),
and the handover preserves both: a state where `P₁` fails starts the second phase where `P₂`
fails, and `Φ₁` never exceeds the starting `Φ₂`.  Then from a state where `P₁` fails the two
phases end in a state firing `P₂` with `Φ₂ ≤ K` with mass at most `K - Φ₁ s`: the firing mass of
both phases is charged against the one budget `K`.

The measurable-space instance on `β × σ₂` is pinned to `⊤` inside the statement; a consumer must
fix `⊤` too. -/
theorem evalDist_bind_run_apply_setOf_and_le_of_potential
    (h₁ : IsPotentialStep so₁ P₁ Φ₁) (h₂ : IsPotentialStep so₂ P₂ Φ₂)
    (init : α × σ → σ₂) (hinitP : ∀ z, ¬ P₁ z.2 → ¬ P₂ (init z))
    (hinitΦ : ∀ z, Φ₁ z.2 ≤ Φ₂ (init z))
    (oa : OracleComp spec α) (ob : α × σ → OracleComp spec₂ β) (K : ℝ≥0∞) (hK' : K ≠ ⊤) :
    ∀ s : σ, ¬ P₁ s →
      (letI : MeasurableSpace (β × σ₂) := ⊤;
        𝒟[(simulateQ so₁ oa).run s >>= fun z => (simulateQ so₂ (ob z)).run (init z)]
          {y | P₂ y.2 ∧ Φ₂ y.2 ≤ K} ≤ K - Φ₁ s) := by
  let _ : MeasurableSpace (β × σ₂) := ⊤
  refine evalDist_bind_apply_setOf_and_le_of_potential h₁
    (fun z => (simulateQ so₂ (ob z)).run (init z)) (fun y => P₂ y.2) (fun y => Φ₂ y.2) K hK'
    (fun z y hy => ?_) (fun z hz => ?_) oa
  · exact (hinitΦ z).trans
      (le_of_mem_support_run_simulateQ_of_step so₂ Φ₂ h₂.mono (ob z) (init z) hy)
  · rw [← bind_pure ((simulateQ so₂ (ob z)).run (init z))]
    refine (evalDist_bind_apply_setOf_and_le_of_potential h₂ pure (fun y => P₂ y.2)
      (fun y => Φ₂ y.2) K hK' (fun _ y hy => ?_) (fun y hy => ?_) (ob z) (init z)
      (hinitP z hz)).trans (tsub_le_tsub_left (hinitΦ z) K)
    · rw [support_pure, Set.mem_singleton_iff] at hy
      rw [hy]
    · rw [evalDist_pure, Measure.dirac_apply' _ MeasurableSet.of_discrete,
        Set.indicator_of_notMem (fun h => hy h.1)]
      exact zero_le

/-- **The potential-charged first-fire bound across two phases, as an event probability.**  A
run under the handler `so₁` is followed by a run of a program `ob z` under a second handler
`so₂`, started from a state `init z` computed from the first run's final output and state `z`.
Each handler charges its own bad predicate to its own potential (`IsPotentialStep`; `P₁`, `Φ₁` on
`σ` and `P₂`, `Φ₂` on `σ₂`), and the handover preserves both: a state where `P₁` fails starts the
second phase where `P₂` fails, and `Φ₁` never exceeds the starting `Φ₂`.  Then from a state where
`P₁` fails the two phases end in a state firing `P₂` with `Φ₂ ≤ K` with probability at most
`K - Φ₁ s`. -/
theorem prEvent_bind_run_and_le_of_potential
    (h₁ : IsPotentialStep so₁ P₁ Φ₁) (h₂ : IsPotentialStep so₂ P₂ Φ₂)
    (init : α × σ → σ₂) (hinitP : ∀ z, ¬ P₁ z.2 → ¬ P₂ (init z))
    (hinitΦ : ∀ z, Φ₁ z.2 ≤ Φ₂ (init z))
    (oa : OracleComp spec α) (ob : α × σ → OracleComp spec₂ β) (K : ℝ≥0∞) (hK' : K ≠ ⊤)
    (s : σ) (hs : ¬ P₁ s) :
    Pr{let z ← (simulateQ so₁ oa).run s; let y ← (simulateQ so₂ (ob z)).run (init z)}[
      P₂ y.2 ∧ Φ₂ y.2 ≤ K] ≤ K - Φ₁ s := by
  let _ : MeasurableSpace (β × σ₂) := ⊤
  rw [← bind_assoc, prEvent_eq_evalDist_of_discrete]
  exact evalDist_bind_run_apply_setOf_and_le_of_potential h₁ h₂ init hinitP hinitΦ oa ob K hK' s hs

end TwoPhase

end OracleComp
