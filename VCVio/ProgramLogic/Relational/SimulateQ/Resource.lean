/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.SimulateQ.StateDependent

/-!
# Resource-charged and averaged-state bad-event bounds

Over a state `σ × Bool` whose flag records a bad event, these results bound the probability that
the flag is set at the end of a run, rather than leaving it as an additive remainder the way the
identical-until-bad bounds do.

* `prEvent_bad_simulateQ_run_le_expectedQuerySlack` charges each charged query a flip cost
  `R s · ε` at the state it fires from, and bounds the bad mass by the resulting
  `expectedQuerySlack`.
* `avgBadM` averages the bad mass against a state measure `ν` instead of a fixed state. It
  telescopes through the free monad like `expectedQuerySlack`, with the read charge taken
  against the law of the state rather than at a single state.
-/

public section

open ENNReal OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic.Relational

/-! ## Single-world resource-charged bad accumulator

A charged query from a good state `(s, false)` may raise the flag with mass at most `R s · ε`;
a free query never raises it. The bad mass at the end of a run is then at most
`expectedQuerySlack impl charged (fun s => R s · ε)`, which the resource folds
`expectedQuerySlack_resource_le` / `expectedQuerySlack_expected_resource_le` turn into a
closed form. -/

section SingleWorldResourceBad

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [IsMeasureSpec spec']
variable {σ γ : Type}

/-- **Single-world resource-charged bad accumulator.**

For `simulateQ impl oa` over a state `σ × Bool` (resource `σ`, never-reset bad flag), if

* every charged step from `(s, false)` raises the flag with mass at most `R s · ε` beyond the
  bad mass its good post-states carry forward (`h_charged_step`), while
* every free step carries forward only the bad mass of its good post-states
  (`h_free_step`),

then the probability the flag is set after the whole run from a good state is at most the
resource-weighted query slack `expectedQuerySlack impl charged (fun s => R s * ε) oa qS (s, false)`.

Both step premises quantify over an *arbitrary* continuation `k`, so a concrete handler
discharges them once per query kind rather than once per computation. `R` and `ε` enter only
through the product `R s * ε`, so a purely state-dependent charge can be supplied through `R`
alone with `ε = 1`. -/
theorem prEvent_bad_simulateQ_run_le_expectedQuerySlack
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec'))) (charged : spec.Domain → Prop)
    [DecidablePred charged] (R : σ → ℝ≥0∞) (ε : ℝ≥0∞)
    (h_charged_step : ∀ (t : spec.Domain) (s : σ), charged t →
      ∀ (k : spec.Range t × σ × Bool → OracleComp spec' (γ × σ × Bool)),
        Pr{let z ← (impl t).run (s, false) >>= k}[z.2.2 = true] ≤ R s * ε +
          wp ((impl t).run (s, false)) fun z =>
            if z.2.2 then 0 else Pr{let w ← k z}[w.2.2 = true])
    (h_free_step : ∀ (t : spec.Domain) (s : σ), ¬ charged t →
      ∀ (k : spec.Range t × σ × Bool → OracleComp spec' (γ × σ × Bool)),
        Pr{let z ← (impl t).run (s, false) >>= k}[z.2.2 = true] ≤
          wp ((impl t).run (s, false)) fun z =>
            if z.2.2 then 0 else Pr{let w ← k z}[w.2.2 = true])
    (oa : OracleComp spec γ) {qS : ℕ} (h_qb : oa.IsQueryBoundP charged qS) (s : σ) :
    Pr{let z ← (simulateQ impl oa).run (s, false)}[z.2.2 = true] ≤
      expectedQuerySlack impl charged (fun s => R s * ε) oa qS (s, false) := by
  induction oa using OracleComp.inductionOn generalizing qS s with
  | pure x => simp
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at h_qb
      obtain ⟨hvalid, hcont⟩ := h_qb
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [expectedQuerySlack_query_bind]
      -- Each good post-state forwards its bad mass to the inductive hypothesis.
      have hpt : ∀ z : spec.Range t × σ × Bool,
          (if z.2.2 then 0 else
            Pr{let w ← (simulateQ impl (cont z.1)).run z.2}[w.2.2 = true]) ≤
          expectedQuerySlack impl charged (fun s => R s * ε) (cont z.1)
            (if charged t then qS - 1 else qS) z.2 := by
        rintro ⟨u, s', b⟩
        cases b with
        | true => simp
        | false => exact ih u (hcont u) s'
      by_cases h : charged t
      · rw [expectedQuerySlackStep_costly_pos _ _ _ _ _ _ _ h (hvalid.resolve_left (· h))]
        refine (h_charged_step t s h _).trans (add_le_add le_rfl (wp_mono _ fun z => ?_))
        simpa only [h, ↓reduceIte] using hpt z
      · rw [expectedQuerySlackStep_free _ _ _ _ _ _ _ h]
        refine (h_free_step t s h _).trans (wp_mono _ fun z => ?_)
        simpa only [h, ↓reduceIte] using hpt z

end SingleWorldResourceBad

/-! ## Averaged-state-measure bad accumulator

The single-world accumulator charges a flip cost `R s · ε` **at a fixed reachable state** `s`.
That is the right shape for a handler that *draws the hidden randomness at the read* (the lazy /
deferred-sampling handler), where the per-state read charge is the averaged guessing mass
`R s · ε < 1`.

It is the *wrong* shape for an **eager** handler that *commits the hidden draw upstream*
(at signing time) and then reads it back deterministically: at a committed state `s` the
read-hit indicator `1_{mc ∈ slot(s)}` is `0` or `1`, never `ε`. The averaging that produces `ε`
happened earlier, at the commit draw, and cannot be localized to any fixed read state.

The fix carried here is to average not over a single fixed state but over a **state measure**
`ν : σ × Bool → ℝ≥0∞`, the law of the eager handler's slot under the pending upstream draws.
The averaged bad mass

  `avgBadM impl ν oa := ∑' p, ν p · Pr{let z ← (simulateQ impl oa).run p}[z.2.2 = true]`

telescopes through the free monad like `expectedQuerySlack`, but the read step's charge is now
`∑' p, ν p · 1_{mc ∈ slot(p)}`, a probability over the state law.

The scaffold is stated over a **bare measure** `ν`: the telescoping identities and the
free-monad induction only use `ν p` as an `ℝ≥0∞` weight, so an **aborting** signing step, whose
post-step state law loses the rejection mass, is carried as it is. The telescoping splits a
query step over its answers and successor states, so it assumes countable answer and state
types. -/

section AveragedStateMeasureBad

variable {ι : Type} {spec : OracleSpec ι}
variable {ι' : Type} {spec' : OracleSpec ι'} [IsMeasureSpec spec']
variable {σ γ : Type}

/-- **Bare-measure averaged bad mass.** The per-state bad mass of a run, averaged against an
arbitrary measure `ν : σ × Bool → ℝ≥0∞` rather than a probability law. No total-mass constraint
is needed by the telescoping, so the average carries the sub-probability post-step laws emitted
by an aborting step. -/
@[expose] noncomputable def avgBadM
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (oa : OracleComp spec γ) : ℝ≥0∞ :=
  ∑' p : σ × Bool, ν p * Pr{let z ← (simulateQ impl oa).run p}[z.2.2 = true]

open scoped Classical in
/-- `avgBadM` at a Dirac (single-point indicator) measure is the plain per-state bad
probability. -/
lemma avgBadM_pure_state
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (p₀ : σ × Bool) (oa : OracleComp spec γ) :
    avgBadM impl (fun p => if p = p₀ then 1 else 0) oa =
      Pr{let z ← (simulateQ impl oa).run p₀}[z.2.2 = true] := by
  rw [avgBadM, tsum_eq_single p₀ (by intro p hp; rw [ite_eq_right hp, zero_mul]),
    ite_eq_left rfl, one_mul]

open scoped Classical in
/-- **Linearity of `avgBadM` in the state measure.** The averaged bad mass over `ν` is the
`ν`-weighted sum of the per-state (Dirac) bad masses. -/
lemma avgBadM_eq_tsum_pure
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (oa : OracleComp spec γ) :
    avgBadM impl ν oa =
      ∑' s' : σ × Bool, ν s' * avgBadM impl (fun p => if p = s' then 1 else 0) oa := by
  rw [avgBadM]
  exact tsum_congr fun s' => by rw [avgBadM_pure_state]

/-- **Pure base case of `avgBadM`.** With no queries, the bad mass is exactly the carried
bad mass of the measure `ν`: the `ν`-mass on states with the flag already set. -/
lemma avgBadM_pure
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (x : γ) :
    avgBadM impl ν (pure x : OracleComp spec γ) =
      ∑' p : σ × Bool, ν p * (if p.2 = true then 1 else 0) := by
  rw [avgBadM]
  refine tsum_congr fun p => ?_
  rw [simulateQ_pure, StateT.run_pure, prEvent_pure]

/-- **One-step telescoping of `avgBadM` (joint-law form).** Moves one query off the front
and exposes the post-step joint law, holding for any handler and any measure `ν`.

The right-hand side is the double `tsum`, over the starting state `p` and then the step outcome
`z`, with the per-state step mass `Pr{(impl t).run p}[= z]` left exposed; apply this form when
that step law itself has to be manipulated. `avgBadM_telescope_eq_tsum_postStep` regroups the
same right-hand side as a single `tsum` against `postStepJointM`, and
`avgBadM_query_bind_eq_tsum_output` chains the two into the output-indexed form that a
free-monad induction consumes. -/
lemma avgBadM_query_bind_eq
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) [Countable (spec.Range t)] [Countable σ]
    (cont : spec.Range t → OracleComp spec γ) :
    avgBadM impl ν (query t >>= cont) =
      ∑' p : σ × Bool, ν p *
        ∑' z : spec.Range t × σ × Bool, Pr{(impl t).run p}[= z] *
          Pr{let w ← (simulateQ impl (cont z.1)).run z.2}[w.2.2 = true] := by
  simp only [avgBadM, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind, prEvent_bind_eq_tsum_of_countable]

/-- **Post-step joint measure of a query step (bare-measure form).** The measure over
`(output, post-state)` produced by averaging the per-state step mass `Pr{(impl t).run p}[= z]`
against the state measure `ν`. Stated as a `tsum` since `ν` need not be a probability law. -/
@[expose] noncomputable def postStepJointM
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (z : spec.Range t × σ × Bool) : ℝ≥0∞ :=
  ∑' p : σ × Bool, ν p * Pr{(impl t).run p}[= z]

open scoped Classical in
/-- **Output-grouped telescoping of the bare-measure average.** The telescoped one-step
average regroups as a single `tsum` over the post-step joint measure `postStepJointM impl ν t`,
weighting each `(output, post-state)` pair by the Dirac bad mass at the post-state. -/
lemma avgBadM_telescope_eq_tsum_postStep
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (cont : spec.Range t → OracleComp spec γ) :
    (∑' p : σ × Bool, ν p *
        ∑' z : spec.Range t × σ × Bool, Pr{(impl t).run p}[= z] *
          Pr{let w ← (simulateQ impl (cont z.1)).run z.2}[w.2.2 = true]) =
      ∑' z : spec.Range t × σ × Bool,
        postStepJointM impl ν t z *
          avgBadM impl (fun p => if p = z.2 then 1 else 0) (cont z.1) := by
  classical
  have hstep : (∑' p : σ × Bool, ν p *
        ∑' z : spec.Range t × σ × Bool, Pr{(impl t).run p}[= z] *
          Pr{let w ← (simulateQ impl (cont z.1)).run z.2}[w.2.2 = true]) =
      ∑' p : σ × Bool, ∑' z : spec.Range t × σ × Bool,
          ν p * (Pr{(impl t).run p}[= z] *
            avgBadM impl (fun q => if q = z.2 then 1 else 0) (cont z.1)) := by
    refine tsum_congr fun p => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun z => ?_
    rw [avgBadM_pure_state]
  rw [hstep, ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  rw [postStepJointM, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun p => ?_
  rw [mul_assoc]

/-- **Per-output post-step state measure.** Grouping the post-step joint measure
`postStepJointM impl ν t` by the query *output* `u`: the resulting state measure assigns to
each post-state `s` the joint mass of producing `(u, s)`. -/
@[expose] noncomputable def postStepOutM
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (u : spec.Range t) (s : σ × Bool) : ℝ≥0∞ :=
  postStepJointM impl ν t (u, s)

open scoped Classical in
/-- **Output-grouped one-step telescoping of `avgBadM`.** The telescoped one-step average
regroups as a `tsum` over the query *output* `u`, each weighted by the averaged bad mass of
the continuation `cont u` run from the per-output post-step state measure
`postStepOutM impl ν t u`. This is the form the threaded-charge induction consumes: it applies
the inductive hypothesis once per output, at a genuine state *measure* (not a Dirac), so the
per-target charge of the post-step measure can be bounded as a measure. -/
lemma avgBadM_query_bind_eq_tsum_output
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) [Countable (spec.Range t)] [Countable σ]
    (cont : spec.Range t → OracleComp spec γ) :
    avgBadM impl ν (query t >>= cont) =
      ∑' u : spec.Range t, avgBadM impl (postStepOutM impl ν t u) (cont u) := by
  classical
  rw [avgBadM_query_bind_eq, avgBadM_telescope_eq_tsum_postStep, ENNReal.tsum_prod']
  refine tsum_congr fun u => ?_
  rw [avgBadM_eq_tsum_pure]
  refine tsum_congr fun s => ?_
  rw [postStepOutM]

/-- **Weighted post-step rearrangement.** Summing any post-state functional `F` against the
post-step measure (over output `u` and post-state `s`) equals the `ν`-average of the per-state
expected value of `F` after one step. The Fubini bridge used to push a per-state charge bound
(e.g. ghost-size or membership-charge growth) through the post-step measure.

Unlike `avgBadM_query_bind_eq_tsum_output`, which regroups the bad mass of one specific
continuation, this carries an arbitrary `ℝ≥0∞`-valued functional `F` of the post-state and
mentions no run at all; instantiate `F` at the charge being tracked. -/
lemma tsum_tsum_postStepOutM_mul
    (impl : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    (ν : σ × Bool → ℝ≥0∞) (t : spec.Domain) (F : σ × Bool → ℝ≥0∞) :
    (∑' u : spec.Range t, ∑' s : σ × Bool, postStepOutM impl ν t u s * F s)
      = ∑' p : σ × Bool, ν p *
          ∑' z : spec.Range t × σ × Bool, Pr{(impl t).run p}[= z] * F z.2 := by
  rw [← ENNReal.tsum_prod]
  simp only [postStepOutM, postStepJointM, ← ENNReal.tsum_mul_right, mul_assoc]
  exact ENNReal.tsum_comm.trans (tsum_congr fun p => ENNReal.tsum_mul_left)

end AveragedStateMeasureBad

end OracleComp.ProgramLogic.Relational
