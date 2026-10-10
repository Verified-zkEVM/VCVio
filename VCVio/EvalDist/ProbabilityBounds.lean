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

/-!
# Probability bounds for computation observations

Union bounds, event splitting, and conditioning on a common draw are stated for events observed
in `Prop`, so intermediate types need no measurable-space arguments in the public statements. The
common draw may lose mass; lower bounds ask for its losslessness as the trivially true event.
Bounds that only need to hold on structurally reachable outputs go through core attachment.
Conditional independent draws bound the squared probability of a single event.
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
    Pr{let y ← source >>= f}[p y] ^ 2 ≤
      Pr{let x ← source; let a ← f x; let b ← f x}[p a ∧ p b] := by
  let : MeasurableSpace α := ⊤
  have hpair :
      Pr{let x ← source; let a ← f x; let b ← f x}[p a ∧ p b] =
        ∫⁻ x, Pr{let a ← f x}[p a] ^ 2 ∂𝒟[source] := by
    rw [prEvent_bind_of_discrete]
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

/-- Union bound over a finite index set with a uniform bound on each event. -/
theorem prEvent_exists_finset_le_card_mul {ι : Type} (s : Finset ι) (mx : m α)
    (p : ι → α → Prop) {ε : ℝ≥0∞} (h : ∀ i ∈ s, Pr{let x ← mx}[p i x] ≤ ε) :
    Pr{let x ← mx}[∃ i ∈ s, p i x] ≤ s.card * ε :=
  (prEvent_exists_finset_le s mx p).trans (by simpa using Finset.sum_le_card_nsmul s _ ε h)

/-- If at most one index satisfies `p`, and each index satisfying `p` has its event with
probability at most `ε`, then some index satisfying `p` has its event with probability at most
`ε`. The predicate `p` does not depend on the drawn value. -/
theorem prEvent_exists_and_le_of_subsingleton {ι : Type} (mx : m α) (p : ι → Prop)
    (event : ι → α → Prop) {ε : ℝ≥0∞} (hε : ∀ i, p i → Pr{let x ← mx}[event i x] ≤ ε)
    (hp : {i | p i}.Subsingleton) :
    Pr{let x ← mx}[∃ i, p i ∧ event i x] ≤ ε := by
  have hcard : hp.finite.toFinset.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦
    hp (hp.finite.mem_toFinset.mp ha) (hp.finite.mem_toFinset.mp hb)
  refine (prEvent_mono _ _ (fun x ↦ ∃ i ∈ hp.finite.toFinset, event i x)
    fun _ ⟨i, hi, h⟩ ↦ ⟨i, hp.finite.mem_toFinset.mpr hi, h⟩).trans
    ((prEvent_exists_finset_le_card_mul _ mx event
      fun i hi ↦ hε i (hp.finite.mem_toFinset.mp hi)).trans ?_)
  calc (hp.finite.toFinset.card : ℝ≥0∞) * ε ≤ (1 : ℕ) * ε := by gcongr
    _ = ε := by simp

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
    Pr{let y ← mx >>= f}[q y] ≤ ε := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ a, Pr{let y ← f a}[q y] ∂𝒟[mx]
      ≤ ∫⁻ _, ε ∂𝒟[mx] := lintegral_mono h
    _ = ε * 𝒟[mx] Set.univ := lintegral_const ε
    _ ≤ ε := mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)

/-- A pointwise comparison of continuation events survives a common draw. -/
theorem prEvent_bind_mono_of_forall_le {γ : Type} (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop) (h : ∀ a, Pr{let y ← f a}[p y] ≤ Pr{let y ← g a}[q y]) :
    Pr{let y ← mx >>= f}[p y] ≤ Pr{let y ← mx >>= g}[q y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  exact lintegral_mono h

/-- A continuation event bounded by `ε` where `p` holds, and null where it fails, is bounded after
a common draw by the probability of `p` times `ε`. -/
theorem prEvent_bind_le_prEvent_mul_of_forall_le (mx : m α) (f : α → m β) (p : α → Prop)
    (q : β → Prop) {ε : ℝ≥0∞} (h₁ : ∀ a, p a → Pr{let y ← f a}[q y] ≤ ε)
    (h₂ : ∀ a, ¬ p a → Pr{let y ← f a}[q y] = 0) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] * ε := by
  classical
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_eq_evalDist_of_discrete, mul_comm,
    ← lintegral_indicator_const MeasurableSet.of_discrete]
  refine lintegral_mono fun a => ?_
  by_cases hp : p a
  · simpa [Set.indicator_of_mem (show a ∈ {x | p x} from hp)] using h₁ a hp
  · rw [Set.indicator_of_notMem (show a ∉ {x | p x} from hp), h₂ a hp]

/-- A pointwise split of a continuation event into two other continuation events survives a
common draw. -/
theorem prEvent_bind_le_add_of_forall_le {γ δ : Type} (mx : m α) (f : α → m β)
    (g : α → m γ) (k : α → m δ) (p : β → Prop) (q : γ → Prop) (r : δ → Prop)
    (h : ∀ a, Pr{let y ← f a}[p y] ≤ Pr{let y ← g a}[q y] + Pr{let y ← k a}[r y]) :
    Pr{let y ← mx >>= f}[p y] ≤ Pr{let y ← mx >>= g}[q y] + Pr{let y ← mx >>= k}[r y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
    prEvent_bind_eq_lintegral_of_discrete, ← lintegral_add_left Measurable.of_discrete]
  exact lintegral_mono h

/-- A uniform lower bound on the event of every continuation bounds the event after a lossless
common draw. -/
theorem le_prEvent_bind_of_forall_le (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ε ≤ Pr{let y ← f a}[q y]) :
    ε ≤ Pr{let y ← mx >>= f}[q y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_true_eq_evalDist_apply_univ] at hmx
  rw [prEvent_bind_eq_lintegral_of_discrete]
  calc ε = ∫⁻ _, ε ∂𝒟[mx] := by rw [lintegral_const, hmx, mul_one]
    _ ≤ _ := lintegral_mono h

/-- A continuation event with the same probability after every draw keeps that probability after a
lossless draw. -/
theorem prEvent_bind_eq_of_forall_eq (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, Pr{let y ← f a}[q y] = ε) :
    Pr{let y ← mx >>= f}[q y] = ε :=
  le_antisymm (prEvent_bind_le_of_forall_le mx f q fun a ↦ (h a).le)
    (le_prEvent_bind_of_forall_le mx hmx f q fun a ↦ (h a).ge)

/-- Multiplying a lower bound for a prefix event by a uniform conditional lower bound gives a
lower bound for the event after the bind. -/
theorem mul_le_prEvent_bind_of_forall (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {r r' : ℝ≥0∞}
    (h : r ≤ Pr{let x ← mx}[p x])
    (h' : ∀ x, p x → r' ≤ Pr{let y ← f x}[q y]) :
    r * r' ≤ Pr{let y ← mx >>= f}[q y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete] at h
  calc
    r * r' ≤ 𝒟[mx] {x | p x} * r' := by gcongr
    _ = ∫⁻ x, ({x | p x} : Set α).indicator (fun _ ↦ r') x ∂𝒟[mx] := by
      rw [lintegral_indicator MeasurableSet.of_discrete, setLIntegral_const]
      exact mul_comm _ _
    _ ≤ ∫⁻ x, Pr{let y ← f x}[q y] ∂𝒟[mx] := by
      apply lintegral_mono
      intro x
      by_cases hx : p x
      · rw [Set.indicator_of_mem (show x ∈ {x | p x} from hx)]
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using h' x hx
      · rw [Set.indicator_of_notMem (show x ∉ {x | p x} from hx)]
        exact zero_le
    _ = Pr{let y ← mx >>= f}[q y] := (prEvent_bind_eq_lintegral_of_discrete mx f q).symm
    _ ≤ _ := by rfl

/-- Conditioning on a predicate of the common draw: the continuation event is bounded by the
predicate's probability plus the conditional bound weighted by the predicate's complement.
The weighting is the honest subprobability form; for a lossless draw the complement's probability
is `1 - Pr{let a ← mx}[p a]` by `prEvent_add_prEvent_not`. -/
theorem prEvent_bind_le_prEvent_add_mul_prEvent_not (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] + ε * Pr{let a ← mx}[¬ p a] := by
  classical
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  have hpt : ∀ a, Pr{let y ← f a}[q y] ≤
      ({a | p a} : Set α).indicator (fun _ ↦ 1) a +
        ({a | ¬ p a} : Set α).indicator (fun _ ↦ ε) a := by
    intro a
    by_cases hpa : p a
    · rw [Set.indicator_of_mem (show a ∈ {a | p a} from hpa),
        Set.indicator_of_notMem (show a ∉ {a | ¬ p a} from not_not.mpr hpa), add_zero]
      exact prEvent_le_one _
    · rw [Set.indicator_of_notMem (show a ∉ {a | p a} from hpa),
        Set.indicator_of_mem (show a ∈ {a | ¬ p a} from hpa), zero_add]
      exact h a hpa
  calc ∫⁻ a, Pr{let y ← f a}[q y] ∂𝒟[mx]
      ≤ ∫⁻ a, ({a | p a} : Set α).indicator (fun _ ↦ 1) a +
          ({a | ¬ p a} : Set α).indicator (fun _ ↦ ε) a ∂𝒟[mx] := lintegral_mono hpt
    _ = 𝒟[mx] {a | p a} + ε * 𝒟[mx] {a | ¬ p a} := by
      rw [lintegral_add_left (Measurable.of_discrete),
        lintegral_indicator MeasurableSet.of_discrete,
        lintegral_indicator MeasurableSet.of_discrete]
      simp [lintegral_const]

/-- A continuation event vanishing outside a predicate of the common draw is bounded by the
predicate's probability. -/
theorem prEvent_bind_le_prEvent_of_forall_eq_zero (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ a, ¬ p a → Pr{let y ← f a}[q y] = 0) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] := by
  simpa using prEvent_bind_le_prEvent_add_mul_prEvent_not mx f p q (ε := 0)
    fun a ha ↦ (h a ha).le

/-- A continuation event bounded by `ε` outside a predicate of the common draw is bounded by the
predicate's probability plus `ε`. -/
theorem prEvent_bind_le_prEvent_add (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] + ε :=
  (prEvent_bind_le_prEvent_add_mul_prEvent_not mx f p q h).trans
    (add_le_add_right (mul_le_of_le_one_right' (prEvent_le_one _)) _)

/-- When an event of the inner draw has the same probability `c` for every value of the outer
draw, the joint event with a predicate on the outer value factors as `c` times the outer
probability. -/
theorem prEvent_bind_and_eq_mul (mx : m α) (my : α → m β)
    (q : β → Prop) (p : α → Prop) {c : ℝ≥0∞} (hq : ∀ a, Pr{let b ← my a}[q b] = c) :
    Pr{let a ← mx; let b ← my a}[q b ∧ p a] = c * Pr{let a ← mx}[p a] := by
  let : MeasurableSpace α := ⊤
  have hinner (a : α) : Pr{let b ← my a}[q b ∧ p a] = {a | p a}.indicator (fun _ => c) a := by
    by_cases ha : p a
    · simpa only [ha, and_true, Set.indicator_of_mem (show a ∈ {a | p a} from ha)] using hq a
    · rw [Set.indicator_of_notMem (show a ∉ {a | p a} from ha)]
      exact prEvent_eq_zero_of_forall_not _ _ fun _ h => ha h.2
  have hbind := prEvent_bind_eq_lintegral_of_discrete mx
    (fun a => do let b ← my a; pure (q b ∧ p a)) id
  have hbind' : Pr{let a ← mx; let b ← my a}[q b ∧ p a] =
      ∫⁻ a, Pr{let b ← my a}[q b ∧ p a] ∂𝒟[mx] := by
    simpa only [prEvent_norm, bind_assoc, pure_bind, id_eq] using hbind
  rw [hbind']
  simp_rw [hinner]
  rw [lintegral_indicator_const MeasurableSet.of_discrete, prEvent_eq_evalDist_of_discrete]

end conditioning

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

variable [EvalDistSemantics m]

/-- The trivially true event is unchanged by attachment. -/
theorem prEvent_true_attach (mx : m α) :
    Pr{let _ ← MonadAttach.attach mx}[True] = Pr{let _ ← mx}[True] := by
  conv_rhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  rw [prEvent_map]

variable [LawfulEvalDistSemantics m]

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

/-- A bound on the event of every reachable continuation bounds the event after the draw. -/
theorem prEvent_bind_le_of_forall_le_of_support (mx : m α) (f : α → m β) (q : β → Prop)
    {ε : ℝ≥0∞} (h : ∀ a ∈ support mx, Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ ε := by
  rw [bind_eq_attach_bind mx f]
  exact prEvent_bind_le_of_forall_le _ _ q fun a ↦ h a.1 a.2

/-- A lower bound on the event of every reachable continuation bounds the event after a lossless
draw. -/
theorem le_prEvent_bind_of_forall_le_of_support (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m β) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ε ≤ Pr{let y ← f a}[q y]) :
    ε ≤ Pr{let y ← mx >>= f}[q y] := by
  rw [bind_eq_attach_bind mx f]
  exact le_prEvent_bind_of_forall_le _ (by rwa [prEvent_true_attach]) _ q fun a ↦ h a.1 a.2

/-- Conditioning on a predicate of the reachable common draw. -/
theorem prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] + ε * Pr{let a ← mx}[¬ p a] := by
  rw [bind_eq_attach_bind mx f]
  have := prEvent_bind_le_prEvent_add_mul_prEvent_not (MonadAttach.attach mx) (fun a ↦ f a.1)
    (fun a ↦ p a.1) q fun a ha ↦ h a.1 a.2 ha
  refine this.trans (le_of_eq ?_)
  conv_rhs => rw [← WeaklyLawfulMonadAttach.map_attach (x := mx)]
  rw [prEvent_map, prEvent_map]

/-- A continuation event vanishing outside a predicate of the reachable draw is bounded by the
predicate's probability. -/
theorem prEvent_bind_le_prEvent_of_support (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] = 0) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] := by
  simpa using prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support mx f p q (ε := 0)
    fun a ha hp ↦ (h a ha hp).le

/-- A continuation event bounded outside a predicate of the reachable draw. -/
theorem prEvent_bind_le_prEvent_add_of_support (mx : m α) (f : α → m β)
    (p : α → Prop) (q : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ a ∈ support mx, ¬ p a → Pr{let y ← f a}[q y] ≤ ε) :
    Pr{let y ← mx >>= f}[q y] ≤ Pr{let a ← mx}[p a] + ε :=
  (prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support mx f p q h).trans
    (add_le_add_right (mul_le_of_le_one_right' (prEvent_le_one _)) _)

end attach
