/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.EvalDist.Monad.Support
public import ToMathlib.MeasureTheory.Integral.Quadratic
public import ToMathlib.MeasureTheory.Measure.Option
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Probability bounds for computation observations

Union bounds, event splitting, and conditioning on a common draw are stated for events observed
in `Prop`, so intermediate types need no measurable-space arguments in the public statements. The
common draw may lose mass; lower bounds ask for its losslessness as the trivially true event.
An observation bounded by one has expectation one exactly when it equals one almost surely, which
passes a probability-one event through the nested normal form of a bind. Bounds that only need to
hold on structurally reachable outputs go through core attachment. Conditional independent draws
bound the squared probability of a single event.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v

/-- Two independent executions after a common draw bound the squared single-execution event. -/
theorem prEvent_bind_sq_le_bind_pair
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} (source : m α) (f : α → m β) (p : β → Prop) :
    Pr{let x ← source; let y ← f x}[p y] ^ 2 ≤
      Pr{let x ← source; let a ← f x; let b ← f x}[p a ∧ p b] := by
  let : MeasurableSpace α := ⊤
  have hpair :
      Pr{let x ← source; let a ← f x; let b ← f x}[p a ∧ p b] =
        ∫⁻ x, Pr{let a ← f x}[p a] ^ 2 ∂𝒟[source] := by
    rw [ExpectationWP.wp_eq_lintegral source _ Measurable.of_discrete]
    simp only [prEvent_bind_bind_and, sq]
  rw [prEvent_bind_eq_lintegral_of_discrete, hpair]
  exact ENNReal.sq_lintegral_le_lintegral_sq Measurable.of_discrete.aemeasurable

/-- Finite selector events in an optional output have total probability at most the event that
an output is present. Intermediate values need no measurable-space argument. -/
theorem sum_prEvent_option_map_eq_some_le_isSome
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α γ : Type} [Fintype γ] (mx : m (Option α)) (select : α → Option γ) :
    ∑ k : γ, Pr{let r ← mx}[r.map select = some (some k)] ≤ Pr{let r ← mx}[r.isSome] := by
  let : MeasurableSpace α := ⊤
  simpa only [prEvent_eq_evalDist_of_discrete] using
    (Measure.sum_apply_option_map_eq_some_le_isSome 𝒟[mx] select
      fun _ ↦ MeasurableSet.of_discrete)

/-! ## Event algebra and union bounds -/

section eventAlgebra

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}

/-- Union bound for two events after a common draw. -/
theorem prEvent_or_le (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x ∨ q x] ≤ Pr{let x ← mx}[p x] + Pr{let x ← mx}[q x] := by
  let : MeasurableSpace α := ⊤
  simp only [prEvent_eq_evalDist_of_discrete]
  exact (measure_mono (by intro x hx; exact hx)).trans (measure_union_le {x | p x} {x | q x})

/-- Union bound over a finite index set. -/
theorem prEvent_exists_finset_le {ι : Type} (s : Finset ι) (mx : m α) (p : ι → α → Prop) :
    Pr{let x ← mx}[∃ i ∈ s, p i x] ≤ ∑ i ∈ s, Pr{let x ← mx}[p i x] := by
  let : MeasurableSpace α := ⊤
  simp only [prEvent_eq_evalDist_of_discrete]
  refine (measure_mono ?_).trans (measure_biUnion_finset_le s fun i ↦ {x | p i x})
  intro x hx
  obtain ⟨i, hi, hp⟩ := hx
  exact Set.mem_biUnion hi hp

/-- Over a finite type of values, the event that an optional observation is present has the total
probability of its individual values. -/
theorem prEvent_isSome_eq_sum {γ : Type} [Fintype γ] (mx : m α) (f : α → Option γ) :
    Pr{let x ← mx}[(f x).isSome] = ∑ k, Pr{let x ← mx}[f x = some k] := by
  let : MeasurableSpace α := ⊤
  simp only [prEvent_eq_evalDist_of_discrete]
  rw [← measure_biUnion_finset (fun i _ j _ hij ↦ Set.disjoint_left.mpr fun _ hi hj ↦
      hij (Option.some.inj (hi.symm.trans hj))) fun _ _ ↦ MeasurableSet.of_discrete]
  congr 1
  ext x
  simp [Option.isSome_iff_exists]

/-- Disjoint selector events of one computation have total probability at most one. -/
theorem sum_prEvent_eq_some_le_one {γ : Type} [Fintype γ] (mx : m α) (f : α → Option γ) :
    ∑ k, Pr{let x ← mx}[f x = some k] ≤ 1 := by
  rw [← prEvent_isSome_eq_sum]
  exact prEvent_le_one _

/-- Union bound over a finite type. -/
theorem prEvent_exists_le {ι : Type} [Fintype ι] (mx : m α) (p : ι → α → Prop) :
    Pr{let x ← mx}[∃ i, p i x] ≤ ∑ i, Pr{let x ← mx}[p i x] := by
  simpa using prEvent_exists_finset_le Finset.univ mx p

/-- A uniform bound on each of finitely many events bounds their union by the count. -/
theorem prEvent_exists_le_card_mul {ι : Type} [Fintype ι] (mx : m α) (p : ι → α → Prop)
    {ε : ℝ≥0∞} (h : ∀ i, Pr{let x ← mx}[p i x] ≤ ε) :
    Pr{let x ← mx}[∃ i, p i x] ≤ Fintype.card ι * ε :=
  (prEvent_exists_le mx p).trans (by
    simpa using Finset.sum_le_card_nsmul Finset.univ _ ε (fun i _ ↦ h i))

/-- An event splits along a second predicate. -/
theorem prEvent_eq_prEvent_and_add_prEvent_and_not (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[p x ∧ q x] + Pr{let x ← mx}[p x ∧ ¬ q x] := by
  let : MeasurableSpace α := ⊤
  simp only [prEvent_eq_evalDist_of_discrete]
  rw [← measure_union (Set.disjoint_left.mpr fun x hx hx' ↦ hx'.2 hx.2) MeasurableSet.of_discrete]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  exact ⟨fun hp ↦ (em (q x)).imp (fun hq ↦ ⟨hp, hq⟩) (fun hq ↦ ⟨hp, hq⟩),
    fun h ↦ h.elim And.left And.left⟩

/-- An event is bounded by a second one plus the part outside it. -/
theorem prEvent_le_prEvent_add_prEvent_and_not (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] + Pr{let x ← mx}[p x ∧ ¬ q x] := by
  rw [prEvent_eq_prEvent_and_add_prEvent_and_not mx p q]
  exact add_le_add_left (prEvent_mono mx (fun x ↦ p x ∧ q x) q fun x hx ↦ hx.2) _

/-- An event and its negation partition the successful mass. -/
theorem prEvent_add_prEvent_not_eq_prEvent_true (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] + Pr{let x ← mx}[¬p x] = Pr{let _ ← mx}[True] := by
  rw [prEvent_eq_prEvent_and_add_prEvent_and_not mx (fun _ ↦ True) p]
  simp only [true_and]

/-- Up-to-bad bound, one direction. If the part of `mx` off the flag `bad` is dominated by `my`,
then an event of `mx` exceeds the matching event of `my` by at most the flag probability. -/
theorem prEvent_le_prEvent_add_of_prEvent_and_not_le {β : Type} (mx : m α) (my : m β)
    (bad p : α → Prop) (q : β → Prop)
    (h : Pr{let x ← mx}[p x ∧ ¬bad x] ≤ Pr{let y ← my}[q y]) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[bad x] + Pr{let y ← my}[q y] :=
  (prEvent_le_prEvent_add_prEvent_and_not mx p bad).trans (add_le_add le_rfl h)

/-- Up-to-bad bound, reverse direction. If `my` keeps no more mass than `mx`, and the part of `mx`
off the flag `bad` is dominated by `my` on the complementary events, then an event of `my`
exceeds the matching event of `mx` by at most the flag probability. -/
theorem prEvent_le_prEvent_add_of_prEvent_not_and_not_le {β : Type} (mx : m α) (my : m β)
    (bad p : α → Prop) (q : β → Prop)
    (hmass : Pr{let _ ← my}[True] ≤ Pr{let _ ← mx}[True])
    (h : Pr{let x ← mx}[¬p x ∧ ¬bad x] ≤ Pr{let y ← my}[¬q y]) :
    Pr{let y ← my}[q y] ≤ Pr{let x ← mx}[bad x] + Pr{let x ← mx}[p x] := by
  refine ENNReal.le_of_add_le_add_right (a := Pr{let y ← my}[¬q y])
    (ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one _)) ?_
  rw [prEvent_add_prEvent_not_eq_prEvent_true]
  calc Pr{let _ ← my}[True] ≤ Pr{let _ ← mx}[True] := hmass
    _ = Pr{let x ← mx}[p x] + Pr{let x ← mx}[¬p x] :=
      (prEvent_add_prEvent_not_eq_prEvent_true mx p).symm
    _ ≤ Pr{let x ← mx}[p x] + (Pr{let x ← mx}[bad x] + Pr{let y ← my}[¬q y]) :=
      add_le_add le_rfl (prEvent_le_prEvent_add_of_prEvent_and_not_le mx my bad _ _ h)
    _ = _ := by rw [← add_assoc]; congr 1; exact add_comm _ _

/-- A conjunction is bounded by its first conjunct. -/
theorem prEvent_and_le_left (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x ∧ q x] ≤ Pr{let x ← mx}[p x] :=
  prEvent_mono mx _ _ fun _ hx ↦ hx.1

/-- A conjunction is bounded by its second conjunct. -/
theorem prEvent_and_le_right (mx : m α) (p q : α → Prop) :
    Pr{let x ← mx}[p x ∧ q x] ≤ Pr{let x ← mx}[q x] :=
  prEvent_mono mx _ _ fun _ hx ↦ hx.2

end eventAlgebra

/-! ## Conditioning on a common draw -/

section conditioning

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type}

/-- A uniform bound on the event of every continuation bounds the event after a common draw.
No losslessness of the draw is needed. -/
theorem prEvent_bind_le_of_forall_le (mx : m α) (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let x ← mx; let y ← f x}[q y] ≤ ε :=
  wp_le_of_forall_le mx h

/-- A pointwise comparison of continuation events survives a common draw. -/
theorem prEvent_bind_mono_of_forall_le {γ : Type} (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop) (h : ∀ a, Pr{let y ← f a}[p y] ≤ Pr{let y ← g a}[q y]) :
    Pr{let x ← mx; let y ← f x}[p y] ≤ Pr{let x ← mx; let y ← g x}[q y] :=
  ExpectationWP.wp_mono mx h

/-- A continuation event bounded by `ε` where `p` holds, and null where it fails, is bounded after
a common draw by the probability of `p` times `ε`. -/
theorem prEvent_bind_le_prEvent_mul_of_forall_le (mx : m α) (f : α → m β) (p : α → Prop)
    (q : β → Prop) {ε : ℝ≥0∞} (h₁ : ∀ a, p a → Pr{let y ← f a}[q y] ≤ ε)
    (h₂ : ∀ a, ¬ p a → Pr{let y ← f a}[q y] = 0) :
    Pr{let x ← mx; let y ← f x}[q y] ≤ Pr{let a ← mx}[p a] * ε := by
  rw [← wp_propInd_mul]
  refine ExpectationWP.wp_mono mx fun a ↦ ?_
  by_cases hp : p a
  · simpa [hp] using h₁ a hp
  · simp [hp, h₂ a hp]

/-- A pointwise split of a continuation event into two other continuation events survives a
common draw. -/
theorem prEvent_bind_le_add_of_forall_le {γ δ : Type} (mx : m α) (f : α → m β)
    (g : α → m γ) (k : α → m δ) (p : β → Prop) (q : γ → Prop) (r : δ → Prop)
    (h : ∀ a, Pr{let y ← f a}[p y] ≤ Pr{let y ← g a}[q y] + Pr{let y ← k a}[r y]) :
    Pr{let x ← mx; let y ← f x}[p y] ≤
      Pr{let x ← mx; let y ← g x}[q y] + Pr{let x ← mx; let y ← k x}[r y] :=
  (ExpectationWP.wp_mono mx h).trans_eq (ExpectationWP.wp_add mx _ _)

/-- A uniform lower bound on the event of every continuation bounds the event after a lossless
common draw. -/
theorem le_prEvent_bind_of_forall_le (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ε ≤ Pr{let y ← f a}[q y]) :
    ε ≤ Pr{let x ← mx; let y ← f x}[q y] :=
  le_wp_of_forall_le mx hmx h

/-- A continuation event with the same probability after every draw keeps that probability after a
lossless draw. -/
theorem prEvent_bind_eq_of_forall_eq (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, Pr{let y ← f a}[q y] = ε) :
    Pr{let x ← mx; let y ← f x}[q y] = ε :=
  le_antisymm (prEvent_bind_le_of_forall_le mx f q fun a ↦ (h a).le)
    (le_prEvent_bind_of_forall_le mx hmx f q fun a ↦ (h a).ge)

/-- Multiplying a lower bound for a prefix event by a uniform conditional lower bound gives a
lower bound for the event after the bind. -/
theorem mul_le_prEvent_bind_of_forall (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {r r' : ℝ≥0∞}
    (h : r ≤ Pr{let x ← mx}[p x])
    (h' : ∀ x, p x → r' ≤ Pr{let y ← f x}[q y]) :
    r * r' ≤ Pr{let x ← mx; let y ← f x}[q y] := by
  calc
    r * r' ≤ Pr{let x ← mx}[p x] * r' := by gcongr
    _ = wp⟦mx⟧ fun x ↦ propInd (p x) * r' := (wp_propInd_mul mx p r').symm
    _ ≤ _ := ExpectationWP.wp_mono mx fun x ↦ by
      by_cases hx : p x
      · simpa [hx] using h' x hx
      · simp [hx]

/-- Conditioning on a predicate of the common draw: the continuation event is bounded by the
predicate's probability plus the conditional bound weighted by the predicate's complement.
The weighting is the honest subprobability form; for a lossless draw the complement's probability
is `1 - Pr{let a ← mx}[p a]` by `prEvent_add_prEvent_not`. -/
theorem prEvent_bind_le_prEvent_add_mul_prEvent_not (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let x ← mx; let y ← f x}[q y] ≤ Pr{let a ← mx}[p a] + ε * Pr{let a ← mx}[¬ p a] := by
  rw [← wp_mul_propInd, ← ExpectationWP.wp_add]
  refine ExpectationWP.wp_mono mx fun a ↦ ?_
  by_cases hpa : p a
  · simp [hpa]
  · simpa [hpa] using h a hpa

/-- A continuation event vanishing outside a predicate of the common draw is bounded by the
predicate's probability. -/
theorem prEvent_bind_le_prEvent_of_forall_eq_zero (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ a, ¬ p a → Pr{let y ← f a}[q y] = 0) :
    Pr{let x ← mx; let y ← f x}[q y] ≤ Pr{let a ← mx}[p a] := by
  simpa using prEvent_bind_le_prEvent_add_mul_prEvent_not mx f p q (ε := 0)
    fun a ha ↦ (h a ha).le

/-- A continuation event bounded by `ε` outside a predicate of the common draw is bounded by the
predicate's probability plus `ε`. -/
theorem prEvent_bind_le_prEvent_add (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let x ← mx; let y ← f x}[q y] ≤ Pr{let a ← mx}[p a] + ε :=
  (prEvent_bind_le_prEvent_add_mul_prEvent_not mx f p q h).trans
    (add_le_add_right (mul_le_of_le_one_right' (prEvent_le_one _)) _)

end conditioning

/-! ## Conditioning on a probability-one event

An observation bounded by one has expectation one exactly when it equals one almost surely. In the
nested normal form of an event, a probability-one event of the whole computation is a
probability-one event of the first draw under which every continuation's event has probability
one, with no losslessness or support hypothesis on the draw. -/

section probabilityOne

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}

/-- An observation bounded by one that equals one wherever a probability-one event holds has
expectation one. -/
theorem wp_eq_one_of_prEvent_eq_one (mx : m α) {q : α → Prop} {g : α → ℝ≥0∞}
    (hq : Pr{let x ← mx}[q x] = 1) (hg : ∀ x, q x → g x = 1) (hg1 : ∀ x, g x ≤ 1) :
    wp⟦mx⟧ g = 1 :=
  le_antisymm (wp_le_of_forall_le mx hg1) <| hq.symm.trans_le <|
    ExpectationWP.wp_mono mx fun x => by
      by_cases hx : q x <;> simp [propInd, hx, hg]

/-- An observation bounded by one with expectation one equals one almost surely. -/
theorem prEvent_eq_one_of_wp_eq_one (mx : m α) {g : α → ℝ≥0∞} (hg : ∀ x, g x ≤ 1)
    (h : wp⟦mx⟧ g = 1) : Pr{let x ← mx}[g x = 1] = 1 := by
  let : MeasurableSpace α := ⊤
  rw [ExpectationWP.wp_eq_lintegral mx g Measurable.of_discrete] at h
  have hmass : 𝒟[mx] Set.univ = 1 :=
    le_antisymm (evalDist_apply_univ_le_one mx) <| by
      calc (1 : ℝ≥0∞) = ∫⁻ x, g x ∂𝒟[mx] := h.symm
        _ ≤ ∫⁻ _, 1 ∂𝒟[mx] := lintegral_mono hg
        _ = 𝒟[mx] Set.univ := by simp
  have : IsProbabilityMeasure 𝒟[mx] := ⟨hmass⟩
  rw [prEvent_eq_evalDist_of_discrete, ← ae_iff_prob_eq_one Measurable.of_discrete]
  exact ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall hg)
    (ne_top_of_le_ne_top ENNReal.one_ne_top h.le) measurable_const.aemeasurable (by simp [h])

/-- An observation bounded by one has expectation one exactly when it equals one almost
surely. -/
theorem wp_eq_one_iff_prEvent_eq_one (mx : m α) {g : α → ℝ≥0∞} (hg : ∀ x, g x ≤ 1) :
    wp⟦mx⟧ g = 1 ↔ Pr{let x ← mx}[g x = 1] = 1 :=
  ⟨prEvent_eq_one_of_wp_eq_one mx hg,
    fun h => wp_eq_one_of_prEvent_eq_one mx h (fun _ hx => hx) hg⟩

end probabilityOne

/-! ## Reachable continuations through core attachment

Bounds that only hold on structurally reachable outputs of the common draw factor the bind
through `MonadAttach.attach`, whose outputs carry their reachability proof. -/

section attach

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [MonadAttach m] [WeaklyLawfulMonadAttach m] {α β : Type}

/-- A bind factors through the attachment of its possible outputs. -/
theorem bind_eq_attach_bind (mx : m α) (f : α → m β) :
    mx >>= f = MonadAttach.attach mx >>= fun a ↦ f a.1 := by
  conv_lhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  rw [bind_map_left]

variable [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- The trivially true event is unchanged by attachment. -/
theorem prEvent_true_attach (mx : m α) :
    Pr{let _ ← MonadAttach.attach mx}[True] = Pr{let _ ← mx}[True] := by
  conv_rhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  rw [prEvent_map]

/-- An expectation is the expectation over the attached outputs. -/
theorem wp_eq_wp_attach (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = wp⟦MonadAttach.attach mx⟧ fun a ↦ g a.1 := by
  conv_lhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  exact ExpectationWP.wp_map _ _ _

/-- Comparing observations on the structurally reachable outputs compares their expectations. -/
@[gcongr]
theorem wp_mono_of_support (mx : m α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ support mx, f a ≤ g a) : wp⟦mx⟧ f ≤ wp⟦mx⟧ g := by
  rw [wp_eq_wp_attach mx f, wp_eq_wp_attach mx g]
  exact ExpectationWP.wp_mono _ fun a ↦ h a.1 a.2

/-- Observations that agree on the structurally reachable outputs have equal expectations. -/
theorem wp_congr_of_support (mx : m α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ support mx, f a = g a) : wp⟦mx⟧ f = wp⟦mx⟧ g :=
  le_antisymm (wp_mono_of_support mx fun a ha ↦ (h a ha).le)
    (wp_mono_of_support mx fun a ha ↦ (h a ha).ge)

/-- Implication between events only on the structurally reachable outputs bounds their
probabilities. -/
theorem prEvent_mono_of_support (mx : m α) (p q : α → Prop)
    (h : ∀ a ∈ support mx, p a → q a) :
    Pr{let a ← mx}[p a] ≤ Pr{let a ← mx}[q a] := by
  conv_lhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  conv_rhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  rw [prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ fun a ha ↦ h a.1 a.2 ha

/-- Events that agree on every structurally reachable output have equal probability. -/
theorem prEvent_congr_of_support (mx : m α) (p q : α → Prop)
    (h : ∀ a ∈ support mx, p a ↔ q a) :
    Pr{let a ← mx}[p a] = Pr{let a ← mx}[q a] :=
  le_antisymm (prEvent_mono_of_support mx p q fun a ha ↦ (h a ha).1)
    (prEvent_mono_of_support mx q p fun a ha ↦ (h a ha).2)

/-- An event avoiding every structurally reachable output has probability zero. -/
theorem prEvent_eq_zero_of_forall_mem_support (mx : m α) (p : α → Prop)
    (h : ∀ a ∈ support mx, ¬ p a) : Pr{let a ← mx}[p a] = 0 :=
  (prEvent_congr_of_support mx p (fun _ ↦ False) fun a ha ↦ iff_false_intro (h a ha)).trans
    (prEvent_eq_zero_of_forall_not mx _ fun _ ↦ id)

/-- An unreachable output has probability zero. -/
theorem prEvent_eq_zero_of_not_mem_support (mx : m α) {x : α} (hx : x ∉ support mx) :
    Pr{let y ← mx}[y = x] = 0 :=
  prEvent_eq_zero_of_forall_mem_support mx _ fun _ hy h ↦ hx (h ▸ hy)

/-- A bound on the event of every reachable continuation bounds the event after the draw. -/
theorem prEvent_bind_le_of_forall_le_of_support (mx : m α) (f : α → m β) (q : β → Prop)
    {ε : ℝ≥0∞} (h : ∀ a ∈ support mx, Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let x ← mx; let y ← f x}[q y] ≤ ε := by
  rw [wp_eq_wp_attach]
  exact wp_le_of_forall_le _ fun a ↦ h a.1 a.2

/-- A comparison of continuation events on the structurally reachable outputs survives a common
draw. -/
theorem prEvent_bind_mono_of_forall_le_of_support {γ : Type} (mx : m α) (f : α → m β)
    (g : α → m γ) (p : β → Prop) (q : γ → Prop)
    (h : ∀ a ∈ support mx, Pr{let y ← f a}[p y] ≤ Pr{let y ← g a}[q y]) :
    Pr{let x ← mx; let y ← f x}[p y] ≤ Pr{let x ← mx; let y ← g x}[q y] :=
  wp_mono_of_support mx h

/-- A lower bound on the event of every reachable continuation bounds the event after a lossless
draw. -/
theorem le_prEvent_bind_of_forall_le_of_support (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ε ≤ Pr{let y ← f a}[q y]) :
    ε ≤ Pr{let x ← mx; let y ← f x}[q y] := by
  rw [wp_eq_wp_attach]
  exact le_wp_of_forall_le _ (by rwa [prEvent_true_attach]) fun a ↦ h a.1 a.2

/-- Conditioning on a predicate of the reachable common draw. -/
theorem prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let x ← mx; let y ← f x}[q y] ≤ Pr{let a ← mx}[p a] + ε * Pr{let a ← mx}[¬ p a] := by
  rw [← wp_mul_propInd, ← ExpectationWP.wp_add]
  refine wp_mono_of_support mx fun a ha ↦ ?_
  by_cases hpa : p a
  · simp [hpa]
  · simpa [hpa] using h a ha hpa

/-- A continuation event vanishing outside a predicate of the reachable draw is bounded by the
predicate's probability. -/
theorem prEvent_bind_le_prEvent_of_support (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] = 0) :
    Pr{let x ← mx; let y ← f x}[q y] ≤ Pr{let a ← mx}[p a] := by
  simpa using prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support mx f p q (ε := 0)
    fun a ha hp ↦ (h a ha hp).le

/-- A continuation event bounded outside a predicate of the reachable draw. -/
theorem prEvent_bind_le_prEvent_add_of_support (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let x ← mx; let y ← f x}[q y] ≤ Pr{let a ← mx}[p a] + ε :=
  (prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support mx f p q h).trans
    (add_le_add_right (mul_le_of_le_one_right' (prEvent_le_one _)) _)

end attach

/-! ## Failure of a bind -/

section prFail

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β : Type}

/-- A bind fails when its prefix fails, or when the continuation fails after a successful prefix
output. -/
theorem prFail_bind_eq_add_lintegral_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (f : α → m β) :
    prFail (mx >>= f) = prFail mx + ∫⁻ x, prFail (f x) ∂𝒟[mx] := by
  have hbind : Pr{let x ← mx; let _ ← f x}[True] = ∫⁻ x, Pr{let _ ← f x}[True] ∂𝒟[mx] :=
    prEvent_bind_eq_lintegral_of_discrete mx f (fun _ ↦ True)
  have hle : ∫⁻ x, Pr{let _ ← f x}[True] ∂𝒟[mx] ≤ 𝒟[mx] Set.univ :=
    calc ∫⁻ x, Pr{let _ ← f x}[True] ∂𝒟[mx] ≤ ∫⁻ _, 1 ∂𝒟[mx] :=
          lintegral_mono fun x ↦ prEvent_le_one _
      _ = 𝒟[mx] Set.univ := by simp
  have hsub : ∫⁻ x, prFail (f x) ∂𝒟[mx] =
      𝒟[mx] Set.univ - ∫⁻ x, Pr{let _ ← f x}[True] ∂𝒟[mx] := by
    simp only [prFail_def]
    rw [lintegral_sub Measurable.of_discrete (ne_top_of_le_ne_top (measure_ne_top _ _) hle)
      (Filter.Eventually.of_forall fun x ↦ prEvent_le_one _)]
    simp
  rw [prFail_def, prEvent_bind, prFail_eq_one_sub_evalDist_univ, hsub, hbind]
  exact (tsub_add_tsub_cancel (evalDist_apply_univ_le_one mx) hle).symm

end prFail
