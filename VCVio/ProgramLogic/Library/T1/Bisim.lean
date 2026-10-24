/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
public import VCVio.OracleComp.SimSemantics.StateT.Measure
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Bisimulation rules for `simulateQ`

Handler-agnostic rules that identify two simulations of the same computation, one per shape of
the agreement between the two handlers. Each rule comes as an equation, an equality in
distribution (`=ᵈ`), or a relational triple, matching the form of the goal it closes.

* **On an invariant.** Handlers that agree from every state satisfying `Inv`, where the second
  handler preserves `Inv`, give equal runs from an `Inv` state:
  `simulateQ_run_eq_of_impl_eq_on_inv` (equal computations) and
  `evalDistEq_simulateQ_run_of_impl_evalDistEq_on_inv` (equal in distribution), with `run'`
  forms and the relational forms `relTriple_simulateQ_run_of_impl_evalDistEq_on_inv`.
* **Through a state relation.** A per-query coupling with equal answers that preserves a
  relation `R` between the two state spaces gives equal outputs:
  `evalDistEq_simulateQ_run'_of_relTriple`, the `=ᵈ` form of `relTriple_simulateQ_run'`.
* **Through a projection.** If projecting the first handler's state along `proj` gives the
  second handler, in distribution and on an invariant, the projected runs agree:
  `evalDistEq_map_run_simulateQ_of_query_map_evalDistEq` and its `run'` and relational forms.
  `OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'` is the exact-equation form.
* **Identical until bad.** Event and real-valued forms of the fundamental lemma of
  `VCVio.ProgramLogic.Relational.SimulateQ.UntilBad`, the shapes game hops consume:
  `prEvent_simulateQ_run'_le_add_prEvent_bad` (`Pr[E | G₁] ≤ Pr[E | G₂] + Pr[bad | G₁]`) and
  `abs_toReal_prEvent_simulateQ_run'_sub_le`.
* **Cross-type bijections.** `relTriple_uniformSample_bij_cross` couples uniform samples on two
  types along a bijection, and `relTriple_bind_uniformSample_bij_cross` is its bind rule.

The relational rules are not registered with `rvcgen`: they are applied with
`rvcstep with rule` or `rvcgen with rule`, or by `exact`.
-/

@[expose] public section

open OracleSpec OracleComp MeasureTheory
open scoped OracleSpec.PrimitiveQuery ENNReal

universe u u'

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} {ι' : Type u'} {spec' : OracleSpec.{u', 0} ι'}
  {α σ : Type}

/-! ## Bisimulation on an invariant -/

/-- **Bisimulation on an invariant.** Handlers that agree from every `Inv` state, the second of
which preserves `Inv`, give equal simulations from every `Inv` state. -/
theorem simulateQ_run_eq_of_impl_eq_on_inv
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (himpl : ∀ t s, Inv s → (impl₁ t).run s = (impl₂ t).run s)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s) :
    (simulateQ impl₁ oa).run s = (simulateQ impl₂ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [himpl t s hs]
    exact bind_congr_of_forall_mem_support _ fun z hz => ih z.1 z.2 (hpres t s hs z hz)

/-- Output form of `simulateQ_run_eq_of_impl_eq_on_inv`. -/
theorem simulateQ_run'_eq_of_impl_eq_on_inv
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (himpl : ∀ t s, Inv s → (impl₁ t).run s = (impl₂ t).run s)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s) :
    (simulateQ impl₁ oa).run' s = (simulateQ impl₂ oa).run' s :=
  congrArg (Prod.fst <$> ·) (simulateQ_run_eq_of_impl_eq_on_inv impl₁ impl₂ Inv himpl hpres oa s hs)

variable [AnswerMeasure spec']

/-- **Bisimulation in distribution on an invariant.** Handlers equal in distribution from every
`Inv` state, the second of which preserves `Inv`, give simulations equal in distribution. -/
theorem evalDistEq_simulateQ_run_of_impl_evalDistEq_on_inv
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (himpl : ∀ t s, Inv s → (impl₁ t).run s =ᵈ (impl₂ t).run s)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s) :
    (simulateQ impl₁ oa).run s =ᵈ (simulateQ impl₂ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => exact EvalDistEq.rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    exact ((himpl t s hs).bind_left _).trans
      (EvalDistEq.bind_congr_of_support _ fun z hz => ih z.1 z.2 (hpres t s hs z hz))

/-- Output form of `evalDistEq_simulateQ_run_of_impl_evalDistEq_on_inv`. -/
theorem evalDistEq_simulateQ_run'_of_impl_evalDistEq_on_inv
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (himpl : ∀ t s, Inv s → (impl₁ t).run s =ᵈ (impl₂ t).run s)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s) :
    (simulateQ impl₁ oa).run' s =ᵈ (simulateQ impl₂ oa).run' s :=
  (evalDistEq_simulateQ_run_of_impl_evalDistEq_on_inv impl₁ impl₂ Inv himpl hpres oa s hs).map
    Prod.fst

/-! ## Bisimulation through a projection -/

/-- **Bisimulation through a projection, in distribution.** If the first handler read through
`proj` is the second in distribution on an `Inv` it preserves, so are the simulations. -/
theorem evalDistEq_map_run_simulateQ_of_query_map_evalDistEq {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (Inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support ((impl₁ t).run s), Inv z.2)
    (hproj : ∀ t s, Inv s → Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : Inv s) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s =ᵈ (simulateQ impl₂ oa).run (proj s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
    exact EvalDistEq.rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    calc _ =ᵈ ((impl₁ t).run s >>= fun z => (simulateQ impl₂ (k z.1)).run (proj z.2)) :=
          EvalDistEq.bind_congr_of_support _ fun z hz => ih z.1 z.2 (hpres t s hs z hz)
      _ = (Prod.map id proj <$> (impl₁ t).run s) >>= fun z =>
          (simulateQ impl₂ (k z.1)).run z.2 := by rw [bind_map_left]; rfl
      _ =ᵈ _ := (hproj t s hs).bind_left _

/-- Output form of `evalDistEq_map_run_simulateQ_of_query_map_evalDistEq`. -/
theorem evalDistEq_run'_simulateQ_of_query_map_evalDistEq {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (Inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support ((impl₁ t).run s), Inv z.2)
    (hproj : ∀ t s, Inv s → Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : Inv s) :
    (simulateQ impl₁ oa).run' s =ᵈ (simulateQ impl₂ oa).run' (proj s) := by
  have h := (evalDistEq_map_run_simulateQ_of_query_map_evalDistEq impl₁ impl₂ Inv proj hpres
    hproj oa s hs).map Prod.fst
  simpa only [Functor.map_map, Prod.map_fst, id_eq, ← StateT.run'_eq] using h

/-! ## Identical until bad, as event bounds -/

/-- **Identical until bad**, as a game hop: an event of the first simulation is at most as
likely as under the second plus the probability of ending in a bad state. -/
theorem prEvent_simulateQ_run'_le_add_prEvent_bad
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) (p : α → Prop) :
    Pr{let x ← (simulateQ impl₁ oa).run' s₀}[p x] ≤
      Pr{let x ← (simulateQ impl₂ oa).run' s₀}[p x] +
        Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] := by
  let : MeasurableSpace α := ⊤
  exact (prEvent_le_prEvent_add_measureETVDist _ _ p measurable_from_top).trans
    (add_le_add le_rfl (ProgramLogic.Relational.measureETVDist_simulateQ_run'_le_prEvent_bad
      impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀))

/-- **Identical until bad** for handlers whose runs coincide off bad states, as a game hop. -/
theorem prEvent_simulateQ_run'_le_add_prEvent_bad_of_run_eq
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) (p : α → Prop) :
    Pr{let x ← (simulateQ impl₁ oa).run' s₀}[p x] ≤
      Pr{let x ← (simulateQ impl₂ oa).run' s₀}[p x] +
        Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2] :=
  prEvent_simulateQ_run'_le_add_prEvent_bad impl₁ impl₂ bad
    (fun t s hs q => by rw [h_agree t s hs]) h_mono₁ h_mono₂ oa s₀ p

/-- **Identical until bad** in real numbers: the probabilities of an event under the two
simulations differ by at most the probability of ending in a bad state. -/
theorem abs_toReal_prEvent_simulateQ_run'_sub_le
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (bad : σ → Prop)
    (h_agree : ∀ t s, ¬bad s → ∀ q : spec.Range t × σ → Prop,
      Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
        Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2])
    (h_mono₁ : ∀ t s, bad s → ∀ z ∈ support ((impl₁ t).run s), bad z.2)
    (h_mono₂ : ∀ t s, bad s → ∀ z ∈ support ((impl₂ t).run s), bad z.2)
    (oa : OracleComp spec α) (s₀ : σ) (p : α → Prop) :
    |(Pr{let x ← (simulateQ impl₁ oa).run' s₀}[p x]).toReal -
        (Pr{let x ← (simulateQ impl₂ oa).run' s₀}[p x]).toReal| ≤
      (Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2]).toReal := by
  let : MeasurableSpace α := ⊤
  refine (abs_prEvent_toReal_sub_le_measureTVDist _ _ p measurable_from_top).trans ?_
  rw [measureTVDist_eq_toReal_measureETVDist]
  exact ENNReal.toReal_mono (prEvent_ne_top _)
    (ProgramLogic.Relational.measureETVDist_simulateQ_run'_le_prEvent_bad
      impl₁ impl₂ bad h_agree h_mono₁ h_mono₂ oa s₀)

end OracleComp

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} {ι' : Type u'} {spec' : OracleSpec.{u', 0} ι'}
  [AnswerMeasure spec'] [∀ t, Finite (spec'.Range t)] {α σ : Type}

/-! ## Relational forms -/

/-- `RelTriple` form of `evalDistEq_simulateQ_run_of_impl_evalDistEq_on_inv`. -/
theorem relTriple_simulateQ_run_of_impl_evalDistEq_on_inv
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (himpl : ∀ t s, Inv s → (impl₁ t).run s =ᵈ (impl₂ t).run s)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s) :
    RelTriple ((simulateQ impl₁ oa).run s) ((simulateQ impl₂ oa).run s) (EqRel (α × σ)) :=
  relTriple_eqRel_of_evalDistEq
    (evalDistEq_simulateQ_run_of_impl_evalDistEq_on_inv impl₁ impl₂ Inv himpl hpres oa s hs)

/-- `RelTriple` form of `evalDistEq_simulateQ_run'_of_impl_evalDistEq_on_inv`. -/
theorem relTriple_simulateQ_run'_of_impl_evalDistEq_on_inv
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec'))) (Inv : σ → Prop)
    (himpl : ∀ t s, Inv s → (impl₁ t).run s =ᵈ (impl₂ t).run s)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support ((impl₂ t).run s), Inv z.2)
    (oa : OracleComp spec α) (s : σ) (hs : Inv s) :
    RelTriple ((simulateQ impl₁ oa).run' s) ((simulateQ impl₂ oa).run' s) (EqRel α) :=
  relTriple_eqRel_of_evalDistEq
    (evalDistEq_simulateQ_run'_of_impl_evalDistEq_on_inv impl₁ impl₂ Inv himpl hpres oa s hs)

/-- `RelTriple` form of `evalDistEq_run'_simulateQ_of_query_map_evalDistEq`: the projected
handler couples the outputs, from `s` on the left and `proj s` on the right. -/
theorem relTriple_simulateQ_run'_of_query_map_evalDistEq {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec')))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec')))
    (Inv : σ₁ → Prop) (proj : σ₁ → σ₂)
    (hpres : ∀ t s, Inv s → ∀ z ∈ support ((impl₁ t).run s), Inv z.2)
    (hproj : ∀ t s, Inv s → Prod.map id proj <$> (impl₁ t).run s =ᵈ (impl₂ t).run (proj s))
    (oa : OracleComp spec α) (s : σ₁) (hs : Inv s) :
    RelTriple ((simulateQ impl₁ oa).run' s) ((simulateQ impl₂ oa).run' (proj s)) (EqRel α) :=
  relTriple_eqRel_of_evalDistEq
    (evalDistEq_run'_simulateQ_of_query_map_evalDistEq impl₁ impl₂ Inv proj hpres hproj oa s hs)

/-- **Bisimulation through a state relation, in distribution.** A per-query coupling with equal
answers that preserves `R` gives equal output distributions from `R`-related states. -/
theorem evalDistEq_simulateQ_run'_of_relTriple {ι₁ ι₂ : Type u}
    {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{u, 0} ι₂}
    [AnswerMeasure spec₁] [AnswerMeasure spec₂]
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)] {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec₁)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec₂))) (R : σ₁ → σ₂ → Prop)
    (himpl : ∀ t s₁ s₂, R s₁ s₂ → RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R p₁.2 p₂.2))
    (oa : OracleComp spec α) (s₁ : σ₁) (s₂ : σ₂) (hs : R s₁ s₂) :
    (simulateQ impl₁ oa).run' s₁ =ᵈ (simulateQ impl₂ oa).run' s₂ :=
  evalDistEq_of_relTriple_eqRel (relTriple_simulateQ_run' impl₁ impl₂ R oa himpl s₁ s₂ hs)

/-! ## Uniform samples on two types -/

section cross

variable {α β γ δ : Type} [SampleableType α] [SampleableType β]

/-- **Cross-type bijection coupling.** Uniform samples on two types are coupled along a
bijection `f`, under every relation containing its graph. -/
theorem relTriple_uniformSample_bij_cross {f : α → β} (hf : Function.Bijective f)
    (R : RelPost α β) (hR : ∀ x, R x (f x)) :
    RelTriple ($ᵗ α : ProbComp α) ($ᵗ β : ProbComp β) R := by
  have h : RelTriple ($ᵗ α : ProbComp α) (f <$> ($ᵗ α : ProbComp α)) R := by
    simpa only [id_map] using relTriple_map (f := id) (g := f) (R := R)
      (relTriple_refl_of_mem_support ($ᵗ α : ProbComp α) (R := fun a b => R a (f b))
        fun a _ => hR a)
  exact relTriple_of_evalDistEq_right
    (SampleableType.map_uniformSample_evalDistEq_of_bijective hf) h

/-- Bind rule for uniform samples on two types coupled by a bijection: the continuation is
stated over the left sample, with the right sample rewritten to `f a`. -/
theorem relTriple_bind_uniformSample_bij_cross {f : α → β}
    {fa : α → ProbComp γ} {fb : β → ProbComp δ} {S : RelPost γ δ}
    (hfg : ∀ a, RelTriple (fa a) (fb (f a)) S) (hf : Function.Bijective f) :
    RelTriple (($ᵗ α : ProbComp α) >>= fa) (($ᵗ β : ProbComp β) >>= fb) S :=
  relTriple_bind (relTriple_uniformSample_bij_cross hf (fun a b => b = f a) fun _ => rfl)
    fun a _ hb => hb ▸ hfg a

end cross

end OracleComp.ProgramLogic.Relational
