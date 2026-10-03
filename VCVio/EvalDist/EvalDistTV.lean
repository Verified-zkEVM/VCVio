/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.EvalDistEq
public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.EvalDist.MeasureTVDist.Event
public import VCVio.EvalDist.ProbabilityBounds
public import ToMathlib.MeasureTheory.Measure.TotalVariation.Bind

/-!
# Total variation between computations, keyed on events

`etvDist mx my` is the largest discrepancy between the probabilities of an event under two
computations, over all events. It is the extended total variation distance of their
successful-output measures on the discrete σ-algebra, stated across monads and with no measurable
structure on the outputs, as `mx =ᵈ my` is (`etvDist_eq_zero_iff`), and `tvDist` is its real value.
Every event and every bounded expectation moves by at most the distance
(`prEvent_le_prEvent_add_etvDist`, `absDiff_wp_le_etvDist`). Post-processing and a common
continuation do not increase it (`etvDist_map_le`, `etvDist_bind_le`). Two continuations of one
prefix are within their expected pointwise distance (`etvDist_bind_bind_le_wp`), or within the
probability of a bad prefix plus a bound on the good ones (`etvDist_bind_bind_le_of_bad`).

`measureETVDist` is the distance for statements about a chosen σ-algebra and almost-everywhere
hypotheses. `etvDist_eq_measureETVDist` identifies the two distances on a discrete output space,
and `measureETVDist_le_etvDist` bounds `measureETVDist` by `etvDist` on any other σ-algebra.
-/

public section

open MeasureTheory ENNReal
open scoped ENNReal

universe v v' v''

section defs

variable {m : Type → Type v} {m' : Type → Type v'} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m] [Monad m'] [LawfulMonad m']
  [EvalDistSemantics m'] [LawfulEvalDistSemantics m'] {α : Type}

/-- The largest discrepancy between the probabilities of an event under two computations. -/
@[expose] noncomputable def etvDist (mx : m α) (my : m' α) : ℝ≥0∞ :=
  ⨆ p : α → Prop, ENNReal.absDiff Pr{let x ← mx}[p x] Pr{let y ← my}[p y]

/-- The real-valued total variation between two computations. -/
@[expose] noncomputable def tvDist (mx : m α) (my : m' α) : ℝ :=
  (etvDist mx my).toReal

end defs

variable {m : Type → Type v} {m' : Type → Type v'} {m'' : Type → Type v''}
  [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  [Monad m'] [LawfulMonad m'] [EvalDistSemantics m'] [LawfulEvalDistSemantics m']
  [Monad m''] [LawfulMonad m''] [EvalDistSemantics m''] [LawfulEvalDistSemantics m'']
  {α β : Type}

/-! ## Events -/

/-- Every event's discrepancy is at most the distance. -/
theorem absDiff_prEvent_le_etvDist (mx : m α) (my : m' α) (p : α → Prop) :
    ENNReal.absDiff Pr{let x ← mx}[p x] Pr{let y ← my}[p y] ≤ etvDist mx my :=
  le_iSup (fun q : α → Prop => ENNReal.absDiff Pr{let x ← mx}[q x] Pr{let y ← my}[q y]) p

/-- An event is at most as likely as under another computation plus their distance. -/
theorem prEvent_le_prEvent_add_etvDist (mx : m α) (my : m' α) (p : α → Prop) :
    Pr{let x ← mx}[p x] ≤ Pr{let y ← my}[p y] + etvDist mx my :=
  (ENNReal.absDiff_le_iff.1 (absDiff_prEvent_le_etvDist mx my p)).1

/-- The distance is at most `δ` exactly when every event moves by at most `δ`. -/
theorem etvDist_le_iff {mx : m α} {my : m' α} {δ : ℝ≥0∞} :
    etvDist mx my ≤ δ ↔ ∀ p : α → Prop,
      ENNReal.absDiff Pr{let x ← mx}[p x] Pr{let y ← my}[p y] ≤ δ :=
  iSup_le_iff

/-! ## The pseudometric -/

@[simp]
theorem etvDist_self (mx : m α) : etvDist mx mx = 0 := by
  simp [etvDist]

theorem etvDist_comm (mx : m α) (my : m' α) : etvDist mx my = etvDist my mx :=
  iSup_congr fun _ => ENNReal.absDiff_comm _ _

theorem etvDist_triangle (mx : m α) (my : m' α) (mz : m'' α) :
    etvDist mx mz ≤ etvDist mx my + etvDist my mz :=
  iSup_le fun p => (ENNReal.absDiff_triangle _ _ _).trans
    (add_le_add (absDiff_prEvent_le_etvDist mx my p) (absDiff_prEvent_le_etvDist my mz p))

theorem etvDist_le_one (mx : m α) (my : m' α) : etvDist mx my ≤ 1 :=
  iSup_le fun _ => ENNReal.absDiff_le_iff.2
    ⟨(prEvent_le_one _).trans le_add_self, (prEvent_le_one _).trans le_add_self⟩

@[aesop (rule_sets := [finiteness]) safe apply]
theorem etvDist_ne_top (mx : m α) (my : m' α) : etvDist mx my ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (etvDist_le_one mx my)

/-- Two computations are at distance zero exactly when they are equal in distribution. -/
theorem etvDist_eq_zero_iff (mx : m α) (my : m' α) : etvDist mx my = 0 ↔ mx =ᵈ my := by
  simp only [etvDist, ENNReal.iSup_eq_zero, ENNReal.absDiff_eq_zero]
  exact ⟨fun h => EvalDistEq.of_forall_prEvent_eq h, fun h p => h.prEvent_eq p⟩

theorem EvalDistEq.etvDist_eq_zero {mx : m α} {my : m' α} (h : mx =ᵈ my) : etvDist mx my = 0 :=
  (etvDist_eq_zero_iff mx my).2 h

/-- The distance is a congruence for equality in distribution. -/
theorem EvalDistEq.etvDist_congr_left {mx : m α} {mx' : m'' α} (h : mx =ᵈ mx') (my : m' α) :
    etvDist mx my = etvDist mx' my :=
  iSup_congr fun p => by rw [h.prEvent_eq p]

theorem EvalDistEq.etvDist_congr_right {my : m' α} {my' : m'' α} (h : my =ᵈ my') (mx : m α) :
    etvDist mx my = etvDist mx my' :=
  iSup_congr fun p => by rw [h.prEvent_eq p]

/-- Post-processing both computations does not increase their distance. -/
theorem etvDist_map_le (mx : m α) (my : m' α) (f : α → β) :
    etvDist (f <$> mx) (f <$> my) ≤ etvDist mx my :=
  iSup_le fun p => by
    rw [prEvent_map, prEvent_map]
    exact absDiff_prEvent_le_etvDist mx my fun x => p (f x)

/-! ## The measure-level distance -/

section measure

variable [MeasurableSpace α]

/-- The distance of the output measures on a coarser σ-algebra is at most the event-keyed one. -/
theorem evalDist_etvDist_le_etvDist (mx : m α) (my : m' α) :
    Measure.etvDist 𝒟[mx] 𝒟[my] ≤ etvDist mx my :=
  iSup_le fun s => by
    have hx := prEvent_eq_evalDist mx (· ∈ s.1) s.2.mem
    have hy := prEvent_eq_evalDist my (· ∈ s.1) s.2.mem
    rw [Set.ofPred_mem_eq] at hx hy
    rw [← hx, ← hy]
    exact absDiff_prEvent_le_etvDist mx my _

/-- On a discrete output space the event-keyed distance is the distance of the output measures,
across monads. -/
theorem etvDist_eq_evalDist_etvDist [DiscreteMeasurableSpace α] (mx : m α) (my : m' α) :
    etvDist mx my = Measure.etvDist 𝒟[mx] 𝒟[my] :=
  le_antisymm
    (iSup_le fun p => by
      rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
      exact Measure.absDiff_apply_le_etvDist _ _ MeasurableSet.of_discrete)
    (evalDist_etvDist_le_etvDist mx my)

/-- The measure-level distance on a coarser σ-algebra is at most the event-keyed one. -/
theorem measureETVDist_le_etvDist (mx my : m α) : measureETVDist mx my ≤ etvDist mx my :=
  evalDist_etvDist_le_etvDist mx my

/-- On a discrete output space the event-keyed distance is the measure-level one. -/
theorem etvDist_eq_measureETVDist [DiscreteMeasurableSpace α] (mx my : m α) :
    etvDist mx my = measureETVDist mx my :=
  le_antisymm
    (iSup_le fun p => by
      rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
      exact measure_absDiff_apply_le_measureETVDist mx my MeasurableSet.of_discrete)
    (measureETVDist_le_etvDist mx my)

theorem tvDist_eq_measureTVDist [DiscreteMeasurableSpace α] (mx my : m α) :
    tvDist mx my = measureTVDist mx my := by
  rw [tvDist, etvDist_eq_measureETVDist]
  rfl

end measure

/-! ## Expectations -/

/-- A bounded expectation moves by at most the distance. -/
theorem absDiff_wp_le_etvDist (mx : m α) (my : m' α) (g : α → ℝ≥0∞) (hg : ∀ x, g x ≤ 1) :
    ENNReal.absDiff (wp⟦mx⟧ g) (wp⟦my⟧ g) ≤ etvDist mx my := by
  let : MeasurableSpace α := ⊤
  rw [ExpectationWP.wp_eq_lintegral mx g Measurable.of_discrete,
    ExpectationWP.wp_eq_lintegral my g Measurable.of_discrete]
  exact (Measure.absDiff_lintegral_le_etvDist 𝒟[mx] 𝒟[my] g Measurable.of_discrete hg).trans
    (evalDist_etvDist_le_etvDist mx my)

/-- A bounded expectation is at most its value under another computation plus their distance. -/
theorem wp_le_wp_add_etvDist (mx : m α) (my : m' α) (g : α → ℝ≥0∞) (hg : ∀ x, g x ≤ 1) :
    wp⟦mx⟧ g ≤ wp⟦my⟧ g + etvDist mx my :=
  (ENNReal.absDiff_le_iff.1 (absDiff_wp_le_etvDist mx my g hg)).1

/-- The discrepancy of two expectations over one computation is at most the expectation of the
pointwise discrepancy. -/
theorem absDiff_wp_le_wp_absDiff (mx : m α) (u v : α → ℝ≥0∞) :
    ENNReal.absDiff (wp⟦mx⟧ u) (wp⟦mx⟧ v) ≤ wp⟦mx⟧ fun a => ENNReal.absDiff (u a) (v a) := by
  let : MeasurableSpace α := ⊤
  rw [ExpectationWP.wp_eq_lintegral mx u Measurable.of_discrete,
    ExpectationWP.wp_eq_lintegral mx v Measurable.of_discrete,
    ExpectationWP.wp_eq_lintegral mx _ Measurable.of_discrete]
  simp only [ENNReal.absDiff]
  rw [lintegral_add_left Measurable.of_discrete]
  exact add_le_add (lintegral_sub_le _ _ Measurable.of_discrete)
    (lintegral_sub_le _ _ Measurable.of_discrete)

/-! ## Sequencing -/

/-- A common continuation does not increase the distance. -/
theorem etvDist_bind_le (mx my : m α) (f : α → m β) :
    etvDist (mx >>= f) (my >>= f) ≤ etvDist mx my :=
  iSup_le fun p => by
    rw [prEvent_bind, prEvent_bind]
    exact absDiff_wp_le_etvDist mx my _ fun a => prEvent_le_one _

/-- Continuations equal in distribution do not increase the distance of their prefixes, across
monads. -/
theorem etvDist_bind_le_of_evalDistEq (mx : m α) (my : m' α) (f : α → m β) (g : α → m' β)
    (hfg : ∀ a, f a =ᵈ g a) : etvDist (mx >>= f) (my >>= g) ≤ etvDist mx my :=
  iSup_le fun p => by
    rw [prEvent_bind, prEvent_bind]
    simp only [fun a => (hfg a).prEvent_eq p]
    exact absDiff_wp_le_etvDist mx my _ fun a => prEvent_le_one _

/-- Two continuations of one prefix are within the expected pointwise distance. -/
theorem etvDist_bind_bind_le_wp (mx : m α) (f g : α → m β) (bound : α → ℝ≥0∞)
    (h : ∀ a, etvDist (f a) (g a) ≤ bound a) :
    etvDist (mx >>= f) (mx >>= g) ≤ wp⟦mx⟧ bound :=
  iSup_le fun p => by
    rw [prEvent_bind, prEvent_bind]
    exact (absDiff_wp_le_wp_absDiff mx _ _).trans
      (ExpectationWP.wp_mono mx fun a => (absDiff_prEvent_le_etvDist (f a) (g a) p).trans (h a))

/-- Two continuations of one prefix are within the expected pointwise distance, which only the
reachable prefix outputs need to satisfy. -/
theorem etvDist_bind_bind_le_wp_of_support [MonadAttach m] [ExactMonadAttach m] (mx : m α)
    (f g : α → m β) (bound : α → ℝ≥0∞) (h : ∀ a ∈ support mx, etvDist (f a) (g a) ≤ bound a) :
    etvDist (mx >>= f) (mx >>= g) ≤ wp⟦mx⟧ bound :=
  iSup_le fun p => by
    rw [prEvent_bind, prEvent_bind]
    exact (absDiff_wp_le_wp_absDiff mx _ _).trans
      (wp_mono_of_support mx fun a ha =>
        (absDiff_prEvent_le_etvDist (f a) (g a) p).trans (h a ha))

/-- Two sequences are within the distance of their prefixes plus the expected distance of their
continuations. -/
theorem etvDist_bind_bind_le_add_wp (mx my : m α) (f g : α → m β) (bound : α → ℝ≥0∞)
    (h : ∀ a, etvDist (f a) (g a) ≤ bound a) :
    etvDist (mx >>= f) (my >>= g) ≤ etvDist mx my + wp⟦my⟧ bound :=
  (etvDist_triangle (mx >>= f) (my >>= f) (my >>= g)).trans
    (add_le_add (etvDist_bind_le mx my f) (etvDist_bind_bind_le_wp my f g bound h))

/-- Two continuations of one prefix are within the probability of a bad prefix plus a bound on
the distance after a good one. -/
theorem etvDist_bind_bind_le_of_bad (mx : m α) (f g : α → m β) (bad : α → Prop)
    (ε : ℝ≥0∞) (hgood : ∀ a, ¬ bad a → etvDist (f a) (g a) ≤ ε) :
    etvDist (mx >>= f) (mx >>= g) ≤ Pr{let a ← mx}[bad a] + ε * Pr{let a ← mx}[¬ bad a] := by
  classical
  refine (etvDist_bind_bind_le_wp mx f g
    (fun a => propInd (bad a) + ε * propInd (¬ bad a)) fun a => ?_).trans_eq ?_
  · by_cases hbad : bad a
    · simp only [hbad, propInd_true, not_true_eq_false, propInd_false, mul_zero, add_zero]
      exact etvDist_le_one _ _
    · simp only [hbad, propInd_false, not_false_eq_true, propInd_true, mul_one, zero_add]
      exact hgood a hbad
  · rw [ExpectationWP.wp_add, ExpectationWP.wp_const_mul]
    rfl

/-- Two sequences are within the distance of their prefixes plus the expected distance of their
continuations, which only the reachable outputs of the second prefix need to satisfy. -/
theorem etvDist_bind_bind_le_add_wp_of_support [MonadAttach m] [ExactMonadAttach m]
    (mx my : m α) (f g : α → m β) (bound : α → ℝ≥0∞)
    (h : ∀ a ∈ support my, etvDist (f a) (g a) ≤ bound a) :
    etvDist (mx >>= f) (my >>= g) ≤ etvDist mx my + wp⟦my⟧ bound :=
  (etvDist_triangle (mx >>= f) (my >>= f) (my >>= g)).trans
    (add_le_add (etvDist_bind_le mx my f) (etvDist_bind_bind_le_wp_of_support my f g bound h))

/-! ## Hybrid arguments -/

/-- A chain of computations is within the sum of the distances of its consecutive members. -/
theorem etvDist_le_sum_etvDist_succ (f : ℕ → m α) (n : ℕ) :
    etvDist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, etvDist (f i) (f (i + 1)) := by
  induction n with
  | zero => simp [etvDist_self]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (etvDist_triangle (f 0) (f n) (f (n + 1))).trans (add_le_add ih le_rfl)

/-- A chain of `n` steps, each within `ε`, ends within `n * ε`. -/
theorem etvDist_le_of_forall_etvDist_succ_le (f : ℕ → m α) (n : ℕ) (ε : ℝ≥0∞)
    (h : ∀ i < n, etvDist (f i) (f (i + 1)) ≤ ε) :
    etvDist (f 0) (f n) ≤ n * ε :=
  (etvDist_le_sum_etvDist_succ f n).trans <|
    calc ∑ i ∈ Finset.range n, etvDist (f i) (f (i + 1))
        ≤ ∑ _ ∈ Finset.range n, ε := Finset.sum_le_sum fun i hi => h i (Finset.mem_range.1 hi)
      _ = n * ε := by simp

/-! ## Identical until bad -/

/-- Computations that agree on every event away from a bad event are, after any post-processing,
within the bad event's probability. -/
theorem etvDist_map_le_prEvent_of_agree (mx : m α) (my : m' α) (f : α → β) (bad : α → Prop)
    (hagree : ∀ p : α → Prop,
      Pr{let x ← mx}[p x ∧ ¬ bad x] = Pr{let y ← my}[p y ∧ ¬ bad y])
    (hbad : Pr{let y ← my}[bad y] ≤ Pr{let x ← mx}[bad x]) :
    etvDist (f <$> mx) (f <$> my) ≤ Pr{let x ← mx}[bad x] := by
  refine iSup_le fun q => ?_
  rw [prEvent_map, prEvent_map, prEvent_eq_prEvent_and_add_prEvent_and_not mx _ bad,
    prEvent_eq_prEvent_and_add_prEvent_and_not my _ bad, hagree fun x => q (f x)]
  have h₁ : Pr{let x ← mx}[q (f x) ∧ bad x] ≤ Pr{let x ← mx}[bad x] :=
    prEvent_mono mx _ _ fun _ hx => hx.2
  have h₂ : Pr{let y ← my}[q (f y) ∧ bad y] ≤ Pr{let x ← mx}[bad x] :=
    (prEvent_mono my _ _ fun _ hy => hy.2).trans hbad
  refine ENNReal.absDiff_le_iff.2 ⟨?_, ?_⟩
  · calc _ ≤ Pr{let x ← mx}[bad x] + Pr{let y ← my}[q (f y) ∧ ¬ bad y] := add_le_add h₁ le_rfl
      _ ≤ _ := by rw [add_comm]; exact add_le_add le_add_self le_rfl
  · calc _ ≤ Pr{let x ← mx}[bad x] + Pr{let y ← my}[q (f y) ∧ ¬ bad y] := add_le_add h₂ le_rfl
      _ ≤ _ := by rw [add_comm]; exact add_le_add le_add_self le_rfl

/-- **Post-processing through a public view.** The first computation's outputs are read through a
public view `pub`, and the two post-processings agree whenever that view is a good output of the
second computation: the post-processed runs are within the distance of the public views plus the
second computation's bad mass. -/
theorem etvDist_map_le_map_add_prEvent_bad {γ : Type} (oa : m α) (ob : m β) (pub : α → β)
    (fa : α → γ) (fb : β → γ) (bad : β → Prop)
    (h_eq : ∀ a b, pub a = b → ¬ bad b → fa a = fb b) :
    etvDist (fa <$> oa) (fb <$> ob) ≤ etvDist (pub <$> oa) ob + Pr{let y ← ob}[bad y] := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace γ := ⊤
  rw [etvDist_eq_measureETVDist]
  exact (measureETVDist_map_le_map_add_prEvent_bad oa ob pub fa fb bad h_eq).trans
    (add_le_add (measureETVDist_le_etvDist _ _) le_rfl)

/-! ## The real distance -/

@[simp]
theorem tvDist_self (mx : m α) : tvDist mx mx = 0 := by
  simp [tvDist]

theorem tvDist_comm (mx : m α) (my : m' α) : tvDist mx my = tvDist my mx := by
  rw [tvDist, tvDist, etvDist_comm]

theorem tvDist_nonneg (mx : m α) (my : m' α) : 0 ≤ tvDist mx my :=
  ENNReal.toReal_nonneg

theorem tvDist_triangle (mx : m α) (my : m' α) (mz : m'' α) :
    tvDist mx mz ≤ tvDist mx my + tvDist my mz := by
  rw [tvDist, tvDist, tvDist, ← ENNReal.toReal_add (etvDist_ne_top _ _) (etvDist_ne_top _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨etvDist_ne_top _ _, etvDist_ne_top _ _⟩)
    (etvDist_triangle mx my mz)

theorem tvDist_le_one (mx : m α) (my : m' α) : tvDist mx my ≤ 1 := by
  rw [tvDist, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (etvDist_le_one mx my)

theorem tvDist_eq_zero_iff (mx : m α) (my : m' α) : tvDist mx my = 0 ↔ mx =ᵈ my := by
  rw [tvDist, ENNReal.toReal_eq_zero_iff, etvDist_eq_zero_iff]
  exact or_iff_left (etvDist_ne_top mx my)

theorem tvDist_map_le (mx : m α) (my : m' α) (f : α → β) :
    tvDist (f <$> mx) (f <$> my) ≤ tvDist mx my :=
  ENNReal.toReal_mono (etvDist_ne_top mx my) (etvDist_map_le mx my f)

/-- The real distance of a chain is within the sum of the real distances of its steps. -/
theorem tvDist_le_sum_tvDist_succ (f : ℕ → m α) (n : ℕ) :
    tvDist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, tvDist (f i) (f (i + 1)) := by
  unfold tvDist
  rw [← ENNReal.toReal_sum fun i _ => etvDist_ne_top _ _]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => etvDist_ne_top _ _)
    (etvDist_le_sum_etvDist_succ f n)

theorem tvDist_bind_le (mx my : m α) (f : α → m β) :
    tvDist (mx >>= f) (my >>= f) ≤ tvDist mx my :=
  ENNReal.toReal_mono (etvDist_ne_top mx my) (etvDist_bind_le mx my f)

/-- An event is at most as likely as under another computation plus their real distance. -/
theorem prEvent_le_prEvent_add_ofReal_tvDist (mx : m α) (my : m' α) (p : α → Prop) :
    Pr{let x ← mx}[p x] ≤ Pr{let y ← my}[p y] + ENNReal.ofReal (tvDist mx my) := by
  rw [tvDist, ENNReal.ofReal_toReal (etvDist_ne_top mx my)]
  exact prEvent_le_prEvent_add_etvDist mx my p
