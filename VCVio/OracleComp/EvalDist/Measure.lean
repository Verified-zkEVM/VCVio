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

universe u

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

/-- Events agreeing on every possible output have equal successful probability. -/
theorem prEvent_congr_of_support
    {ι : Type u} {α : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    (mx : OracleComp spec α) (p q : α → Prop)
    (h : ∀ a ∈ support mx, p a ↔ q a) :
    Pr{let a ← mx}[p a] = Pr{let a ← mx}[q a] := by
  exact congrArg (fun μ : Measure Prop ↦ μ {True})
    (evalDist_bind_congr_of_support mx (pure ∘ p) (pure ∘ q)
      fun a ha ↦ by simp [propext (h a ha)])

/-- Structural support is positive singleton mass when every oracle response has positive
singleton mass. The full-support hypothesis belongs to the chosen measure interpretation;
finiteness alone does not determine it. -/
theorem mem_support_iff_evalDist_singleton_pos_of_fullSupport
    {ι : Type u} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec]
    (hfull : ∀ t (u : spec.Range t),
      0 < OracleSpec.IsMeasureSpec.toMeasure t {u})
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
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
    {ι : Type u} {α : Type} {spec : OracleSpec.{u, 0} ι}
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
    {ι : Type u} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsUniformMeasureSpec spec]
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : OracleComp spec α) (x : α) :
    x ∈ support mx ↔ 0 < 𝒟[mx] {x} := by
  apply mem_support_iff_evalDist_singleton_pos_of_fullSupport
    (fun t u => ?_) mx x
  have heq : OracleSpec.IsMeasureSpec.toMeasure (spec := spec) t =
      uniformOn (Set.univ : Set (spec.Range t)) :=
    OracleSpec.IsUniformMeasureSpec.toMeasure_eq_uniform t
  rw [heq, ProbabilityTheory.uniformOn_univ_apply_singleton]
  exact ENNReal.inv_pos.mpr (by simp)

/-- Under native uniform oracle semantics, an event has probability one exactly when it contains
every structurally reachable output. -/
@[grind =]
theorem evalDist_apply_setOf_eq_one_iff_forall_mem_support
    {ι : Type u} {α : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsUniformMeasureSpec spec]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : OracleComp spec α) (p : α → Prop) :
    𝒟[mx] {x | p x} = 1 ↔ ∀ x ∈ support mx, p x := by
  apply evalDist_apply_setOf_eq_one_iff_forall_mem_support_of_fullSupport
  intro t u
  have heq : OracleSpec.IsMeasureSpec.toMeasure (spec := spec) t =
      uniformOn (Set.univ : Set (spec.Range t)) :=
    OracleSpec.IsUniformMeasureSpec.toMeasure_eq_uniform t
  rw [heq, ProbabilityTheory.uniformOn_univ_apply_singleton]
  exact ENNReal.inv_pos.mpr (by simp)

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

/-- An event avoiding every structurally reachable output has probability zero. -/
theorem prEvent_eq_zero_of_forall_mem_support (mx : OracleComp spec α) (p : α → Prop)
    (h : ∀ x ∈ support mx, ¬ p x) : Pr{let x ← mx}[p x] = 0 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  exact evalDist.apply_eq_zero_of_disjoint_support mx MeasurableSet.of_discrete h

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

end uniformMeasureSpec

end OracleComp
