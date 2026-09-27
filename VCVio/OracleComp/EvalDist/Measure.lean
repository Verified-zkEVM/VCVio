/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Support
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.MeasureSpec
public import VCVio.EvalDist.Monad.Option
import ToMathlib.Probability.UniformOn
import ToMathlib.MeasureTheory.Measure.Bounds

/-!
# Measure reasoning from structural support

Continuations that denote the same measure on all syntactically reachable outputs may
be interchanged. The proof inducts on the free program, so no probability/support bridge
or positivity assumption on query answers is necessary.

If every query answer has positive singleton mass, a second induction identifies structural
support with positive output mass. Native uniform oracle specifications satisfy that condition,
so their events of probability one, zero, or positive probability are exactly the events holding
on all, none, or some structurally reachable outputs; wrapped optional computations are observed
through their present values.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

namespace OracleComp

/-- Equal continuation measures on structural support give equal composed measures. -/
theorem evalDist_bind_congr_of_support {ι : Type u} {α β : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [MeasurableSpace β]
    [EvalDistSemantics (OracleComp spec)] [LawfulEvalDistSemantics (OracleComp spec)]
    (mx : OracleComp spec α) (f g : α → OracleComp spec β)
    (h : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, bind_assoc, evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro u
    exact ih u fun a ha => h a ((MonadAttach.mem_support_bind).mpr ⟨u, by simp, ha⟩)

private theorem evalDist_query_bind_bind_swap
    {ι : Type u} {β γ : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [∀ t, Countable (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec] [MeasurableSpace γ]
    (t : spec.Domain) (my : OracleComp spec β) (f : spec.Range t → β → OracleComp spec γ) :
    𝒟[query t >>= fun a ↦ my >>= fun b ↦ f a b] =
      𝒟[my >>= fun b ↦ query t >>= fun a ↦ f a b] := by
  induction my using OracleComp.inductionOn with
  | pure b => simp only [pure_bind]
  | query_bind s l ih =>
    simp only [bind_assoc]
    calc
      _ = 𝒟[query s >>= fun v ↦ query t >>= fun a ↦ l v >>= fun b ↦ f a b] :=
        _root_.evalDist_bind_bind_swap (query t) (query s)
          (fun a v ↦ l v >>= fun b ↦ f a b) Measurable.of_discrete
      _ = _ := evalDist_bind_congr_of_support (query s) _ _ fun v _ ↦ ih v

/-- Independent oracle computations commute before any measurably observed continuation.
Only the actual query answers must be countable; the two unobserved output types require
neither countability nor measurable-space instances. -/
theorem evalDist_bind_bind_swap
    {ι : Type u} {α β γ : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [∀ t, Countable (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec] [MeasurableSpace γ]
    (mx : OracleComp spec α) (my : OracleComp spec β) (f : α → β → OracleComp spec γ) :
    𝒟[mx >>= fun a ↦ my >>= fun b ↦ f a b] =
      𝒟[my >>= fun b ↦ mx >>= fun a ↦ f a b] := by
  induction mx using OracleComp.inductionOn with
  | pure a => simp only [pure_bind]
  | query_bind t k ih =>
    simp only [bind_assoc]
    calc
      _ = 𝒟[query t >>= fun v ↦ my >>= fun b ↦ k v >>= fun a ↦ f a b] :=
        evalDist_bind_congr_of_support (query t) _ _ fun v _ ↦ ih v
      _ = _ := evalDist_query_bind_bind_swap t my (fun v b ↦ k v >>= fun a ↦ f a b)

/-- Independent oracle computations commute under a uniform oracle specification; the
countability of the response types follows from uniformity. -/
theorem evalDist_bind_bind_swap_of_uniform
    {ι : Type u} {α β γ : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsUniformMeasureSpec spec]
    [MeasurableSpace γ]
    (mx : OracleComp spec α) (my : OracleComp spec β) (f : α → β → OracleComp spec γ) :
    𝒟[mx >>= fun a ↦ my >>= fun b ↦ f a b] =
      𝒟[my >>= fun b ↦ mx >>= fun a ↦ f a b] :=
  have : ∀ t, Countable (spec.Range t) := fun t ↦
    have := OracleSpec.IsUniformMeasureSpec.finite_range (spec := spec) t
    Finite.to_countable
  evalDist_bind_bind_swap mx my f

/-- Compare measurable valuations of continuation outputs on structural support. The common
computation's unobserved intermediate result needs no measurable-space instance. -/
theorem lintegral_evalDist_bind_mono_of_support
    {ι : Type u} {α β γ : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    [MeasurableSpace β] [MeasurableSpace γ]
    (mx : OracleComp spec α) (f : α → OracleComp spec β) (g : α → OracleComp spec γ)
    {v : β → ENNReal} {w : γ → ENNReal} (hv : Measurable v) (hw : Measurable w)
    (hfg : ∀ a ∈ support mx, (∫⁻ y, v y ∂𝒟[f a]) ≤ ∫⁻ z, w z ∂𝒟[g a]) :
    (∫⁻ y, v y ∂𝒟[mx >>= f]) ≤ ∫⁻ z, w z ∂𝒟[mx >>= g] := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using hfg a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, bind_assoc, lintegral_evalDist_bind_of_discrete _ _ hv,
      lintegral_evalDist_bind_of_discrete _ _ hw]
    exact lintegral_mono fun u ↦ ih u fun a ha ↦
      hfg a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

/-- Compare event masses after a common oracle computation when the continuation bound only
needs to hold on structurally reachable outputs. This is the operational specialization of
`evalDist_bind_apply_mono`: structural reachability supplies its almost-everywhere premise. -/
theorem evalDist_bind_apply_mono_of_support
    {ι : Type u} {α β : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec]
    [MeasurableSpace β]
    (mx : OracleComp spec α) (f g : α → OracleComp spec β)
    {event : Set β} (hevent : MeasurableSet event)
    (hfg : ∀ a ∈ support mx, 𝒟[f a] event ≤ 𝒟[g a] event) :
    𝒟[mx >>= f] event ≤ 𝒟[mx >>= g] event := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using hfg a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, bind_assoc, evalDist_bind_of_discrete, evalDist_bind_of_discrete,
      Measure.bind_apply hevent Measurable.of_discrete.aemeasurable,
      Measure.bind_apply hevent Measurable.of_discrete.aemeasurable]
    exact lintegral_mono fun u ↦ ih u fun a ha ↦
      hfg a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

/-- Additive continuation bounds on reachable outputs lift through a common oracle computation.
No measurable space is required on the hidden common result type. -/
theorem evalDist_bind_apply_le_add_of_support
    {ι : Type u} {α β : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    [MeasurableSpace β]
    (mx : OracleComp spec α) (f g h : α → OracleComp spec β)
    {event : Set β} (hevent : MeasurableSet event)
    (hfg : ∀ a ∈ support mx, 𝒟[f a] event ≤ 𝒟[g a] event + 𝒟[h a] event) :
    𝒟[mx >>= f] event ≤ 𝒟[mx >>= g] event + 𝒟[mx >>= h] event := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using hfg a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply hevent Measurable.of_discrete.aemeasurable]
    calc
      _ ≤ ∫⁻ x, (𝒟[k x >>= g] event + 𝒟[k x >>= h] event) ∂𝒟[query t] :=
        lintegral_mono fun x ↦ ih x fun a ha ↦
          hfg a (MonadAttach.mem_support_bind.mpr ⟨x, by simp, ha⟩)
      _ = _ := lintegral_add_left Measurable.of_discrete _

/-- A uniform lower bound on reachable continuation events bounds their composed event.
The common computation need not carry a measurable-space instance on its output type. -/
theorem le_evalDist_bind_apply_of_support
    {ι : Type u} {α β : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    [MeasurableSpace β]
    (mx : OracleComp spec α) (f : α → OracleComp spec β)
    {event : Set β} (hevent : MeasurableSet event) {r : ℝ≥0∞}
    (h : ∀ a ∈ support mx, r ≤ 𝒟[f a] event) :
    r ≤ 𝒟[mx >>= f] event := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply hevent Measurable.of_discrete.aemeasurable]
    calc
      r = ∫⁻ _u, r ∂𝒟[(query t : OracleComp spec (spec.Range t))] := by
        rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]
      _ ≤ _ := lintegral_mono fun u ↦ ih u fun a ha ↦
        h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

/-- Continuations whose event masses agree on structurally reachable outputs give equal composed
event masses. No measurable space is needed on the hidden common result type. -/
theorem evalDist_bind_apply_congr_of_support
    {ι : Type u} {α β : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    [MeasurableSpace β]
    (mx : OracleComp spec α) (f g : α → OracleComp spec β)
    {event : Set β} (hevent : MeasurableSet event)
    (h : ∀ a ∈ support mx, 𝒟[f a] event = 𝒟[g a] event) :
    𝒟[mx >>= f] event = 𝒟[mx >>= g] event :=
  le_antisymm
    (evalDist_bind_apply_mono_of_support mx f g hevent fun a ha ↦ (h a ha).le)
    (evalDist_bind_apply_mono_of_support mx g f hevent fun a ha ↦ (h a ha).ge)

/-- Continuation events with equal probability on every structurally reachable output give equal
composed event probabilities. The continuations may have different output types, and neither the
common result nor the continuation outputs need a measurable space. -/
theorem prEvent_bind_congr_of_support
    {ι : Type u} {α β γ : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    (mx : OracleComp spec α) (f : α → OracleComp spec β) (g : α → OracleComp spec γ)
    (p : β → Prop) (q : γ → Prop)
    (h : ∀ a ∈ support mx, Pr{let y ← f a}[p y] = Pr{let z ← g a}[q z]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] := by
  simpa only [bind_assoc] using
    evalDist_bind_apply_congr_of_support mx (fun a ↦ f a >>= fun y ↦ pure (p y))
      (fun a ↦ g a >>= fun z ↦ pure (q z)) (measurableSet_singleton True) h

/-- Almost-sure probability-one continuation events remain probability one after sequencing a
lossless oracle computation. -/
theorem evalDist_bind_apply_eq_one_of_ae
    {ι : Type u} {α β : Type v} {spec : OracleSpec.{u, v} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (mx : OracleComp spec α) (f : α → OracleComp spec β)
    {event : Set β} (hevent : MeasurableSet event)
    (h : ∀ᵐ a ∂𝒟[mx], 𝒟[f a] event = 1) :
    𝒟[mx >>= f] event = 1 := by
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply hevent Measurable.of_discrete.aemeasurable,
    lintegral_congr_ae h, lintegral_const, evalDist_apply_univ_eq_one, one_mul]

/-- Structural support is positive singleton mass when every oracle response has positive
singleton mass. The full-support hypothesis belongs to the chosen measure interpretation;
finiteness alone does not determine it. -/
theorem mem_support_iff_evalDist_singleton_pos_of_fullSupport
    {ι : Type u} {spec : OracleSpec.{u, v} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec]
    (hfull : ∀ t (u : spec.Range t),
      0 < OracleSpec.IsMeasureSpec.toMeasure t {u})
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : OracleComp spec α) (x : α) :
    x ∈ support mx ↔ 0 < 𝒟[mx] {x} := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
      change x = a ↔ 0 < (Measure.dirac a) {x}
      constructor
      · intro h
        subst x
        simp
      · intro h
        have ha : a ∈ ({x} : Set α) := by
          by_contra hn
          rw [Measure.dirac_apply a {x}, Set.indicator_of_notMem hn] at h
          exact (not_lt_of_ge le_rfl) h
        exact (Set.mem_singleton_iff.mp ha).symm
  | query_bind t k ih =>
      rw [MonadAttach.mem_support_bind]
      change (∃ u, u ∈ support (query t : OracleComp spec _) ∧ x ∈ support (k u)) ↔
        0 < 𝒟[(query t : OracleComp spec _) >>= k] {x}
      rw [evalDist_bind_of_discrete,
        Measure.bind_apply (measurableSet_singleton x)
          (Measurable.of_discrete).aemeasurable,
        evalDist_query,
        lintegral_pos_iff_support (Measurable.of_discrete)]
      constructor
      · rintro ⟨u, _, hu⟩
        apply lt_of_lt_of_le (hfull t u)
        apply measure_mono
        intro v hv
        have h : v = u := Set.mem_singleton_iff.mp hv
        subst v
        exact ne_of_gt ((ih u).1 hu)
      · intro hpos
        have hs : (Function.support fun u => 𝒟[k u] {x}).Nonempty := by
          by_contra hn
          have he : (Function.support fun u => 𝒟[k u] {x}) = ∅ :=
            Set.not_nonempty_iff_eq_empty.mp hn
          rw [he, measure_empty] at hpos
          exact (not_lt_of_ge le_rfl) hpos
        obtain ⟨u, hu⟩ := hs
        exact ⟨u, mem_support_query t u, (ih u).2 (pos_iff_ne_zero.mpr hu)⟩

/-- An event has probability one exactly when it contains every structurally reachable output,
provided every oracle response has positive singleton mass. -/
theorem evalDist_apply_setOf_eq_one_iff_forall_mem_support_of_fullSupport
    {ι : Type u} {α : Type v} {spec : OracleSpec.{u, v} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec]
    (hfull : ∀ t (u : spec.Range t),
      0 < OracleSpec.IsMeasureSpec.toMeasure t {u})
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : OracleComp spec α) (p : α → Prop) :
    𝒟[mx] {x | p x} = 1 ↔ ∀ x ∈ support mx, p x := by
  rw [← MeasureTheory.ae_iff_prob_eq_one Measurable.of_discrete]
  constructor
  · intro hp x hx
    by_contra hpx
    have hxzero : 𝒟[mx] {x} = 0 :=
      measure_mono_null (by
        intro y hy
        simpa [Set.mem_singleton_iff.mp hy] using hpx)
        (MeasureTheory.ae_iff.mp hp)
    exact (ne_of_gt
      ((mem_support_iff_evalDist_singleton_pos_of_fullSupport hfull mx x).mp hx)) hxzero
  · exact evalDist.ae_of_forall_mem_support mx p MeasurableSet.of_discrete

/-- Under native uniform oracle semantics, structural reachability is positive singleton mass. -/
theorem mem_support_iff_evalDist_singleton_pos
    {ι : Type u} {spec : OracleSpec.{u, v} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsUniformMeasureSpec spec]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : OracleComp spec α) (x : α) :
    x ∈ support mx ↔ 0 < 𝒟[mx] {x} :=
  mem_support_iff_evalDist_singleton_pos_of_fullSupport
    (fun t u => OracleSpec.IsUniformMeasureSpec.toMeasure_singleton_pos t u) mx x

/-- Under native uniform oracle semantics, an event has probability one exactly when it contains
every structurally reachable output. It is not a default `grind` rule: its unbounded support
quantifier saturates `grind`. -/
theorem evalDist_apply_setOf_eq_one_iff_forall_mem_support
    {ι : Type u} {α : Type v} {spec : OracleSpec.{u, v} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsUniformMeasureSpec spec]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : OracleComp spec α) (p : α → Prop) :
    𝒟[mx] {x | p x} = 1 ↔ ∀ x ∈ support mx, p x :=
  evalDist_apply_setOf_eq_one_iff_forall_mem_support_of_fullSupport
    (fun t u => OracleSpec.IsUniformMeasureSpec.toMeasure_singleton_pos t u) mx p

/-! ## Events in `Pr{}` form -/

section measureSpec

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [OracleSpec.IsMeasureSpec spec] {α : Type}

/-- Oracle computations with a measure interpretation are lossless. -/
theorem prEvent_true_eq_one (mx : OracleComp spec α) : Pr{let _ ← mx}[True] = 1 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  simp

/-- An event containing every structurally reachable output has probability one. -/
theorem prEvent_eq_one_of_forall_mem_support (mx : OracleComp spec α) (p : α → Prop)
    (h : ∀ x ∈ support mx, p x) : Pr{let x ← mx}[p x] = 1 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, ← MeasureTheory.ae_iff_prob_eq_one Measurable.of_discrete]
  exact evalDist.ae_of_forall_mem_support mx p MeasurableSet.of_discrete h

/-- When `x` is the only reachable intermediate value that can lead to `y`, the point mass of a
bind at `y` factors as the point mass of the first draw at `x` times that of its continuation. -/
theorem prEvent_bind_eq_mul_of_unique {β : Type} (mx : OracleComp spec α)
    (my : α → OracleComp spec β) (x : α) (y : β)
    (h : ∀ x' ∈ support mx, y ∈ support (my x') → x' = x) :
    Pr{let z ← mx >>= my}[z = y] = Pr{let z ← mx}[z = x] * Pr{let z ← my x}[z = y] := by
  classical
  let : MeasurableSpace α := ⊤
  calc Pr{let z ← mx >>= my}[z = y]
      = ∫⁻ a, Pr{let z ← my a}[z = y] ∂𝒟[mx] := prEvent_bind_eq_lintegral_of_discrete mx my _
    _ = ∫⁻ a, ({x} : Set α).indicator (fun _ => Pr{let z ← my x}[z = y]) a ∂𝒟[mx] := by
        refine lintegral_congr_ae ((evalDist.ae_of_forall_mem_support mx (· ∈ support mx)
          MeasurableSet.of_discrete fun _ ha => ha).mono fun a ha => ?_)
        by_cases hax : a = x
        · subst hax
          simp
        · rw [Set.indicator_of_notMem (by simpa using hax)]
          exact prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hzy =>
            hax (h a ha (hzy ▸ hz))
    _ = Pr{let z ← my x}[z = y] * 𝒟[mx] {x} :=
        lintegral_indicator_const (measurableSet_singleton x) _
    _ = _ := by rw [← prEvent_eq_evalDist_singleton mx x, mul_comm]

/-- Over finite oracle responses, computations with equal point masses have equal output measures
in the discrete structure: both measures are carried by the finite union of their supports. -/
theorem evalDist_eq_of_forall_prEvent_eq [∀ t, Finite (spec.Range t)]
    {mx my : OracleComp spec α} (h : ∀ x, Pr{let z ← mx}[z = x] = Pr{let z ← my}[z = x]) :
    (letI : MeasurableSpace α := ⊤; 𝒟[mx] = 𝒟[my]) := by
  classical
  let : MeasurableSpace α := ⊤
  let T : Finset α := ((support_finite mx).union (support_finite my)).toFinset
  have key : ∀ oz : OracleComp spec α, support oz ⊆ ↑T → ∀ s : Set α,
      𝒟[oz] s = ∑ x ∈ T.filter (· ∈ s), Pr{let z ← oz}[z = x] := by
    intro oz hsub s
    simp_rw [prEvent_eq_evalDist_singleton]
    rw [MeasureTheory.sum_measure_singleton]
    refine measure_congr ((evalDist.ae_of_forall_mem_support oz (· ∈ support oz)
      MeasurableSet.of_discrete fun _ ha => ha).mono fun a ha => ?_)
    have haT : a ∈ T := hsub ha
    change (a ∈ s) = (a ∈ (↑(T.filter (· ∈ s)) : Set α))
    simp [haT]
  ext s -
  rw [key mx (fun a ha => by simp [T, ha]) s, key my (fun a ha => by simp [T, ha]) s]
  exact Finset.sum_congr rfl fun x _ => h x

end measureSpec

section uniformMeasureSpec

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι}
  [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
  [OracleSpec.IsUniformMeasureSpec spec] {α : Type}

/-- Under native uniform oracle semantics, an event has probability one exactly when it holds on
every structurally reachable output. -/
theorem prEvent_eq_one_iff (mx : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 1 ↔ ∀ x ∈ support mx, p x := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  exact evalDist_apply_setOf_eq_one_iff_forall_mem_support mx p

/-- Under native uniform oracle semantics, an event has probability zero exactly when it fails on
every structurally reachable output. -/
theorem prEvent_eq_zero_iff (mx : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 0 ↔ ∀ x ∈ support mx, ¬ p x := by
  let : MeasurableSpace α := ⊤
  refine ⟨fun h x hx hp ↦ ?_, prEvent_eq_zero_of_forall_mem_support mx p⟩
  rw [prEvent_eq_evalDist_of_discrete] at h
  have hpos : 0 < 𝒟[mx] {x} := (mem_support_iff_evalDist_singleton_pos mx x).mp hx
  have hle : 𝒟[mx] {x} ≤ 𝒟[mx] {y | p y} :=
    measure_mono (by rintro _ rfl; exact hp)
  rw [h] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hpos)

/-- Under native uniform oracle semantics, an event has positive probability exactly when some
structurally reachable output satisfies it. -/
theorem prEvent_pos_iff (mx : OracleComp spec α) (p : α → Prop) :
    0 < Pr{let x ← mx}[p x] ↔ ∃ x ∈ support mx, p x := by
  rw [pos_iff_ne_zero, ne_eq, prEvent_eq_zero_iff]
  push Not
  rfl

/-- Under native uniform oracle semantics, computations with the same output measure in the
discrete structure reach the same outputs. -/
theorem support_eq_of_evalDist_eq {mx my : OracleComp spec α}
    (h : (letI : MeasurableSpace α := ⊤; 𝒟[mx] = 𝒟[my])) : support mx = support my := by
  let : MeasurableSpace α := ⊤
  ext x
  rw [mem_support_iff_evalDist_singleton_pos, mem_support_iff_evalDist_singleton_pos, h]

/-- Under native uniform oracle semantics, an event of a single lifted query has the
proportion of satisfying responses as its probability. -/
theorem prEvent_liftM_query_eq_card_div (t : spec.Domain) [Fintype (spec.Range t)]
    (p : spec.Range t → Prop) [DecidablePred p] :
    Pr{let u ← (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))}[p u] =
      ((Finset.univ.filter p).card : ℝ≥0∞) / Fintype.card (spec.Range t) := by
  rw [prEvent_eq_evalDist_of_discrete, evalDist_liftM_query,
    show OracleSpec.IsMeasureSpec.toMeasure (spec := spec) t = uniformOn Set.univ from
      OracleSpec.IsUniformMeasureSpec.toMeasure_eq_uniform t, uniformOn_univ_apply_setOf]

/-- Under native uniform oracle semantics, an event of a single query has the proportion of
satisfying responses as its probability. -/
theorem prEvent_query_eq_card_div (t : spec.Domain) [Fintype (spec.Range t)]
    (p : spec.Range t → Prop) [DecidablePred p] :
    Pr{let u ← (query t : OracleComp spec (spec.Range t))}[p u] =
      ((Finset.univ.filter p).card : ℝ≥0∞) / Fintype.card (spec.Range t) := by
  rw [prEvent_eq_evalDist_of_discrete, evalDist_query_uniform, uniformOn_univ_apply_setOf]

/-- A wrapped optional oracle computation has a probability-one event exactly when every
structurally reachable output is a present value satisfying the event. -/
theorem OptionT.prEvent_mk_eq_one_iff (mx : OracleComp spec (Option α)) (p : α → Prop) :
    Pr{let x ← OptionT.mk mx}[p x] = 1 ↔ ∀ o ∈ support mx, ∃ x, o = some x ∧ p x := by
  rw [OptionT.prEvent_mk, prEvent_eq_one_iff]
  refine forall₂_congr fun o _ ↦ ?_
  cases o <;> simp

/-- A wrapped optional oracle computation has a probability-zero event exactly when no
structurally reachable present value satisfies the event. -/
theorem OptionT.prEvent_mk_eq_zero_iff (mx : OracleComp spec (Option α)) (p : α → Prop) :
    Pr{let x ← OptionT.mk mx}[p x] = 0 ↔ ∀ x, some x ∈ support mx → ¬ p x := by
  rw [OptionT.prEvent_mk, prEvent_eq_zero_iff]
  constructor
  · intro h x hx
    simpa using h (some x) hx
  · intro h o ho
    cases o with
    | none => simp
    | some x => simpa using h x ho

/-- A wrapped optional oracle computation has a positive-probability event exactly when some
structurally reachable present value satisfies the event. -/
theorem OptionT.prEvent_mk_pos_iff (mx : OracleComp spec (Option α)) (p : α → Prop) :
    0 < Pr{let x ← OptionT.mk mx}[p x] ↔ ∃ x, some x ∈ support mx ∧ p x := by
  rw [pos_iff_ne_zero, ne_eq, OptionT.prEvent_mk_eq_zero_iff]
  push Not
  rfl

/-- A wrapped optional oracle computation is lossless exactly when `none` is unreachable. -/
theorem OptionT.isProbabilityMeasure_mk_iff (mx : OracleComp spec (Option α))
    [MeasurableSpace α] [DiscreteMeasurableSpace α] :
    IsProbabilityMeasure 𝒟[OptionT.mk mx] ↔ none ∉ support mx := by
  rw [isProbabilityMeasure_iff, OptionT.evalDist_apply_univ, OptionT.run_mk]
  rw [show ({value | value.isSome} : Set (Option α)) = {value | value ≠ none} by
    ext o; cases o <;> simp]
  rw [evalDist_apply_setOf_eq_one_iff_forall_mem_support]
  constructor
  · intro h hnone
    exact h none hnone rfl
  · intro h o ho
    rintro rfl
    exact h ho

/-- A uniform draw of an answer, in any lawful measure semantics, followed by a continuation has
the output measure of the matching query followed by a continuation with the same per-answer
output measures. -/
theorem evalDist_bind_eq_query_bind_of_uniform {m : Type → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {β : Type} [MeasurableSpace β]
    (t : spec.Domain) (sample : m (spec.Range t)) (hsample : 𝒟[sample] = uniformOn Set.univ)
    (g : spec.Range t → m β) (f : spec.Range t → OracleComp spec β)
    (h : ∀ u, 𝒟[g u] = 𝒟[f u]) :
    𝒟[sample >>= g] =
      𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)) >>= f] := by
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, hsample, evalDist_liftM_query,
    OracleSpec.IsMeasureSpec.toMeasure_eq_uniformOn]
  simp_rw [h]

end uniformMeasureSpec

/-! ## Event masses under different measurable structures -/

/-- The mass of an event does not depend on the measurable structure that makes it measurable:
it is the mass under the discrete structure `⊤`. Statements proved at `⊤` therefore apply under
any chosen measurable space on the output, such as a Borel structure. -/
theorem evalDist_apply_eq_top_apply
    {ι : Type u} {α : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    [MeasurableSpace α] (mx : OracleComp spec α) {s : Set α} (hs : MeasurableSet s) :
    𝒟[mx] s = (letI : MeasurableSpace α := ⊤; 𝒟[mx]) s := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    rw [evalDist_pure, Measure.dirac_apply' a hs]
    let : MeasurableSpace α := ⊤
    rw [evalDist_pure, Measure.dirac_apply' a MeasurableSpace.measurableSet_top]
  | query_bind t k ih =>
    rw [evalDist_bind_of_discrete, Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
    let : MeasurableSpace α := ⊤
    rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSpace.measurableSet_top
      Measurable.of_discrete.aemeasurable]
    exact lintegral_congr fun u ↦ ih u

/-- Under uniform oracle semantics a query, observed in the discrete structure on its response
type, is the uniform measure. The response type's own measurable structure is discrete, so the
query law does not depend on which of the two structures observes it. -/
theorem evalDist_liftM_query_eq_uniformOn_top
    {ι : Type u} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsUniformMeasureSpec spec]
    (t : spec.Domain) :
    (letI : MeasurableSpace (spec.Range t) := ⊤;
      𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))] = uniformOn Set.univ) := by
  have := OracleSpec.IsUniformMeasureSpec.finite_range (spec := spec) t
  have := OracleSpec.IsUniformMeasureSpec.nonempty_range (spec := spec) t
  let : Fintype (spec.Range t) := Fintype.ofFinite _
  have hq (u : spec.Range t) :
      (letI : MeasurableSpace (spec.Range t) := ⊤;
        𝒟[(liftM (OracleSpec.query t) : OracleComp spec (spec.Range t))] {u}) =
        (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
    rw [← evalDist_apply_eq_top_apply _ MeasurableSet.of_discrete, evalDist_liftM_query,
      OracleSpec.IsUniformMeasureSpec.toMeasure_singleton]
  let : MeasurableSpace (spec.Range t) := ⊤
  exact Measure.ext_of_singleton fun u ↦ by rw [hq, uniformOn_univ_apply_singleton]

end OracleComp
