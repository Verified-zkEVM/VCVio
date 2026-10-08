/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position
public import VCVio.OracleComp.QueryTracking.ExpectedQueryCount

/-!
# A hit potential on the instrumented class-indexed tape run

`classPosImplFwd` with the passive state `freshHitAux trig rel` records, beside each cached
point's tape class and position, a hit set: at a fresh draw `u` at a point `x` satisfying `trig`,
every point `y` cached before the draw with `rel x u y` joins it. This file bounds the
probability that every *designated* position of one class's tape ends up holding a hit point,
when every draw at a `trig` point is a fresh uniform draw.

The designated positions are a finite set `P` of positions on the tape of class `jF`. Position
`p` is *cleared* (`HitCleared`) when the point sitting there is in the hit set, and
`hitPending` counts the designated positions not yet cleared. `HitDistinct` asks that one draw
can hit at most one designated point: two designated points that the same answer at the same
point relates to are equal. `HitAll` is the event that every designated position is cleared and
`HitDistinct` holds.

## The potential

`hitPot … ε n s` is `(n * ε) ^ hitPending s` on a state satisfying `HitInv` and `HitDistinct`,
`0` on a state satisfying `HitInv` but not `HitDistinct`, and `⊤` off `HitInv`. `HitInv` is the
position invariant `ClassPosInv` together with the fact that every hit point is cached. The gate
makes the step inequality of `OracleComp.lintegral_run_le_of_isQueryBoundP` hold at every state,
reachable or not: at a state off `HitInv` its right-hand side is `⊤`.

* `hitPot_step` is that step inequality. A step that is not a fresh draw at a `trig` point keeps
  the hit set, so it keeps every cleared position cleared and clears no other; it can only
  designate further points, which can only break `HitDistinct`. A fresh draw at a `trig` point
  `x` answers uniformly when the tapes of the classes of `x` are empty. Its answer `u` clears a
  pending position only if `rel x u t` holds of the point `t` there, which has mass at most `ε`
  per pending position, and under `HitDistinct` it clears at most one. So the expected
  potential is at most `(n * ε) ^ k + k * ε * (n * ε) ^ (k - 1) ≤ ((n + 1) * ε) ^ k` for `k`
  pending positions, by `pow_add_mul_le_add_pow`.
* `prEvent_hitAll_le` composes `hitPot_step`, `hitPot_mono`, `hitPot_init` and
  `one_le_hitPot_of_hitAll` through `OracleComp.prEvent_run_le_of_isQueryBoundP`: a program
  making at most `n` queries satisfying `charged`, which covers every query at a `trig` point,
  reaches `HitAll` from the empty state with probability at most `(n * ε) ^ P.card`.

## Scope

* The tapes of the classes of `trig` points must be empty in the tape family (`hlazy`), so
  every fresh draw at a `trig` point is a uniform sample of its range rather than a tape entry.
* `ε` bounds the mass of `rel x u t` over a uniform `u`, separately for each `trig` point `x`
  and each point `t`; for a relation that a single answer satisfies, `ε` is the reciprocal of
  the size of the range.
* `HitDistinct` is part of the event: the bound says nothing about runs on which two
  designated points are related to one answer at one point.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace AnswerTape

variable {ι J : Type} {spec : OracleSpec.{0, 0} ι} {R : J → Type}

/-- The state of `classPosImplFwd` with a hit set as its passive component: the cache and the
unconsumed tapes, the position bookkeeping, and the hit set. -/
abbrev HitState (spec : OracleSpec.{0, 0} ι) (R : J → Type) : Type :=
  (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Set spec.Domain)

/-! ## The potential -/

section Potential

variable (τ : (spec + spec).Domain → J) (Lfam : (k : J) → List (R k))
  (rel : (x : spec.Domain) → spec.Range x → spec.Domain → Prop) (jF : J) (P : Finset ℕ)

/-- The invariant gating the hit potential, on the tape family `Lfam` a run started from: the
position invariant `ClassPosInv`, and every hit point cached. -/
@[expose]
def HitInv (s : HitState spec R) : Prop :=
  ClassPosInv τ Lfam s.1.1 s.1.2 s.2.1.cls s.2.1.pos s.2.1.next s.2.1.cnt ∧
    ∀ t ∈ s.2.2, s.1.1 t ≠ none

/-- Position `p` of the tape of class `jF` is cleared: the point sitting there is in the hit
set. -/
@[expose]
def HitCleared (s : HitState spec R) (p : ℕ) : Prop :=
  ∃ t, s.2.1.cls t = some jF ∧ s.2.1.pos t = some p ∧ t ∈ s.2.2

/-- The number of designated positions not yet cleared. -/
@[expose]
noncomputable def hitPending (s : HitState spec R) : ℕ := by
  classical
  exact (P.filter fun p => ¬ HitCleared jF s p).card

/-- One answer at one point hits at most one designated point: two points sitting at designated
positions of class `jF` that `rel x u` relates for the same `x` and `u` are equal. -/
@[expose]
def HitDistinct (s : HitState spec R) : Prop :=
  ∀ t t' p p', p ∈ P → p' ∈ P → s.2.1.cls t = some jF → s.2.1.pos t = some p →
    s.2.1.cls t' = some jF → s.2.1.pos t' = some p' → ∀ x u, rel x u t → rel x u t' → t = t'

/-- Every designated position is cleared, and one answer hits at most one designated point. -/
@[expose]
def HitAll (s : HitState spec R) : Prop :=
  (∀ p ∈ P, HitCleared jF s p) ∧ HitDistinct rel jF P s

/-- **The hit potential** at a remaining budget of `n` charged draws, each of which hits a given
point with probability at most `ε`: `(n * ε) ^ hitPending s` on `HitInv` and `HitDistinct`, `0`
on `HitInv` alone, and `⊤` off `HitInv`. -/
@[expose]
noncomputable def hitPot (ε : ℝ≥0∞) (n : ℕ) (s : HitState spec R) : ℝ≥0∞ := by
  classical
  exact if HitInv τ Lfam s then
    (if HitDistinct rel jF P s then ((n : ℝ≥0∞) * ε) ^ hitPending jF P s else 0)
  else ⊤

variable {τ Lfam rel jF P}

/-- On `HitInv` and `HitDistinct` the potential is `(n * ε) ^ hitPending s`. -/
theorem hitPot_of_hitDistinct {s : HitState spec R} (hs : HitInv τ Lfam s)
    (hD : HitDistinct rel jF P s) (ε : ℝ≥0∞) (n : ℕ) :
    hitPot τ Lfam rel jF P ε n s = ((n : ℝ≥0∞) * ε) ^ hitPending jF P s := by
  simp only [hitPot, hs, hD, ↓reduceIte]

/-- On `HitInv` without `HitDistinct` the potential is `0`. -/
theorem hitPot_of_not_hitDistinct {s : HitState spec R} (hs : HitInv τ Lfam s)
    (hD : ¬ HitDistinct rel jF P s) (ε : ℝ≥0∞) (n : ℕ) :
    hitPot τ Lfam rel jF P ε n s = 0 := by
  simp only [hitPot, hs, hD, ↓reduceIte]

/-- Off `HitInv` the potential is `⊤`. -/
theorem hitPot_of_not_hitInv {s : HitState spec R} (hs : ¬ HitInv τ Lfam s) (ε : ℝ≥0∞)
    (n : ℕ) : hitPot τ Lfam rel jF P ε n s = ⊤ := by
  simp only [hitPot, hs, ↓reduceIte]

/-- The hit potential is monotone in the remaining budget. -/
theorem hitPot_mono (ε : ℝ≥0∞) (s : HitState spec R) :
    Monotone fun n => hitPot τ Lfam rel jF P ε n s := by
  intro a b hab
  simp only [hitPot]
  split_ifs
  · exact pow_le_pow_left₀ zero_le (mul_le_mul_left (Nat.cast_le.2 hab) ε) _
  all_goals exact le_rfl

/-- On the empty state every designated position is pending, so the potential is
`(n * ε) ^ P.card`. -/
theorem hitPot_init (ε : ℝ≥0∞) (n : ℕ) :
    hitPot τ Lfam rel jF P ε n ((∅, Lfam), (ClassPos.init, ∅)) = ((n : ℝ≥0∞) * ε) ^ P.card := by
  classical
  have hinv : HitInv τ Lfam (((∅, Lfam), (ClassPos.init, ∅)) : HitState spec R) :=
    ⟨ClassPosInv.empty τ Lfam, fun _ h => h.elim⟩
  have hD : HitDistinct rel jF P (((∅, Lfam), (ClassPos.init, ∅)) : HitState spec R) :=
    fun _ _ _ _ _ _ h => absurd h (by simp)
  rw [hitPot_of_hitDistinct hinv hD, hitPending]
  congr 1
  exact congrArg Finset.card (Finset.filter_true_of_mem fun p _ ⟨_, h, _⟩ => by simp at h)

/-- On `HitAll` no designated position is pending, so the potential at budget `0` is at
least `1`. -/
theorem one_le_hitPot_of_hitAll (ε : ℝ≥0∞) {s : HitState spec R} (h : HitAll rel jF P s) :
    1 ≤ hitPot τ Lfam rel jF P ε 0 s := by
  classical
  by_cases hs : HitInv τ Lfam s
  · rw [hitPot_of_hitDistinct hs h.2, hitPending,
      Finset.card_eq_zero.2 (Finset.filter_false_of_mem fun p hp hn => hn (h.1 p hp)), pow_zero]
  · rw [hitPot_of_not_hitInv hs]
    exact le_top

end Potential

/-! ## One step of the instrumented run -/

section Step

variable [DecidableEq ι] [DecidableEq J] [∀ t : spec.Domain, SampleableType (spec.Range t)]
  (trig : spec.Domain → Prop) [DecidablePred trig]
  (rel : (x : spec.Domain) → spec.Range x → spec.Domain → Prop)
  (τ : (spec + spec).Domain → J)
  (hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t))
  {Lfam : (k : J) → List (R k)} {jF : J} {P : Finset ℕ}
  {t : (unifSpec + (spec + spec)).Domain} {s : HitState spec R}
  {y : (unifSpec + (spec + spec)).Range t × HitState spec R}

/-- A step of the instrumented run preserves `HitInv`, keeps the class and position of every
point cached before it, only grows the hit set, and adds to it only points cached before it. -/
theorem hitInv_of_mem_support_classPosImplFwd_run (hs : HitInv τ Lfam s)
    (hy : y ∈ support ((classPosImplFwd R τ hR (freshHitAux trig rel) t).run s)) :
    HitInv τ Lfam y.2 ∧
      (∀ t', s.1.1 t' ≠ none → y.2.2.1.cls t' = s.2.1.cls t' ∧ y.2.2.1.pos t' = s.2.1.pos t') ∧
      s.2.2 ⊆ y.2.2.2 ∧ ∀ t' ∈ y.2.2.2, s.1.1 t' ≠ none := by
  obtain ⟨-, hq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ t s y).1 hy
  refine ⟨⟨classPosInvAuxFwd_step τ hR _ Lfam t s hs.1 y hy,
    ne_none_of_mem_hits_of_mem_support_classPosImplFwd_run trig rel τ hR t s hs.2 y hy⟩,
    fun t' ht' => by rw [hq]; exact classPosAuxFwd_cls_pos_of_ne_none τ t _ _ _ _ ht', ?_⟩
  rw [hq]
  rcases t with n | (x | x)
  · exact ⟨subset_rfl, hs.2⟩
  all_goals exact ⟨subset_freshHitStep trig rel, ne_none_of_mem_freshHitStep trig rel hs.2⟩

/-- After a step, a designated position is cleared exactly when a point sitting there before the
step is in the hit set after it. -/
theorem hitCleared_iff_of_mem_support_classPosImplFwd_run (hs : HitInv τ Lfam s)
    (hy : y ∈ support ((classPosImplFwd R τ hR (freshHitAux trig rel) t).run s)) (p : ℕ) :
    HitCleared jF y.2 p ↔
      ∃ t', s.2.1.cls t' = some jF ∧ s.2.1.pos t' = some p ∧ t' ∈ y.2.2.2 := by
  obtain ⟨-, hcp, -, hcached⟩ := hitInv_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy
  constructor
  · rintro ⟨t', hc, hp, hh⟩
    obtain ⟨h₁, h₂⟩ := hcp t' (hcached t' hh)
    exact ⟨t', h₁ ▸ hc, h₂ ▸ hp, hh⟩
  · rintro ⟨t', hc, hp, hh⟩
    obtain ⟨h₁, h₂⟩ := hcp t' fun h => by simp [hs.1.cls_none t' h] at hc
    exact ⟨t', h₁ ▸ hc, h₂ ▸ hp, hh⟩

/-- A step designates no fewer points, so `HitDistinct` after it gives `HitDistinct` before. -/
theorem hitDistinct_of_mem_support_classPosImplFwd_run (hs : HitInv τ Lfam s)
    (hy : y ∈ support ((classPosImplFwd R τ hR (freshHitAux trig rel) t).run s))
    (hD : HitDistinct rel jF P y.2) : HitDistinct rel jF P s := by
  obtain ⟨-, hcp, -⟩ := hitInv_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy
  have hkeep : ∀ t' p, s.2.1.cls t' = some jF → s.2.1.pos t' = some p →
      y.2.2.1.cls t' = some jF ∧ y.2.2.1.pos t' = some p := fun t' p hc hp => by
    obtain ⟨h₁, h₂⟩ := hcp t' fun h => by simp [hs.1.cls_none t' h] at hc
    exact ⟨h₁.trans hc, h₂.trans hp⟩
  intro t₁ t₂ p p' hp hp' hc₁ hp₁ hc₂ hp₂
  exact hD t₁ t₂ p p' hp hp' (hkeep _ _ hc₁ hp₁).1 (hkeep _ _ hc₁ hp₁).2 (hkeep _ _ hc₂ hp₂).1
    (hkeep _ _ hc₂ hp₂).2

/-- A step clears no fewer positions, so no more are pending after it. -/
theorem hitPending_le_of_mem_support_classPosImplFwd_run (hs : HitInv τ Lfam s)
    (hy : y ∈ support ((classPosImplFwd R τ hR (freshHitAux trig rel) t).run s)) :
    hitPending jF P y.2 ≤ hitPending jF P s := by
  classical
  obtain ⟨-, -, hsub, -⟩ := hitInv_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy
  refine Finset.card_le_card (Finset.monotone_filter_right _ fun p _ hn hc => hn ?_)
  obtain ⟨t', hc', hp', hh⟩ := hc
  exact (hitCleared_iff_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy p).2
    ⟨t', hc', hp', hsub hh⟩

/-- **Steps that keep the hit set.** If a step leaves the hit set unchanged, the potential after
it is at most the potential before it, at the same budget. -/
theorem hitPot_le_of_hits_eq (hs : HitInv τ Lfam s)
    (hy : y ∈ support ((classPosImplFwd R τ hR (freshHitAux trig rel) t).run s))
    (hh : y.2.2.2 = s.2.2) (ε : ℝ≥0∞) (n : ℕ) :
    hitPot τ Lfam rel jF P ε n y.2 ≤ hitPot τ Lfam rel jF P ε n s := by
  classical
  have hy' := (hitInv_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy).1
  by_cases hD : HitDistinct rel jF P y.2
  · rw [hitPot_of_hitDistinct hy' hD, hitPot_of_hitDistinct hs
      (hitDistinct_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy hD), hitPending,
      hitPending]
    refine le_of_eq (congrArg _ (congrArg _ (Finset.filter_congr fun p _ => not_congr ?_)))
    rw [hitCleared_iff_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy p, hh]
    rfl
  · rw [hitPot_of_not_hitDistinct hy' hD]
    exact zero_le

/-- The answers `u` of a draw at `x` that hit a point sitting at a pending designated position
of the state `s`. -/
@[expose]
def HitsPending (jF : J) (P : Finset ℕ) (s : HitState spec R) (x : spec.Domain)
    (u : spec.Range x) : Prop :=
  ∃ p ∈ P, ¬ HitCleared jF s p ∧ ∃ t', s.2.1.cls t' = some jF ∧ s.2.1.pos t' = some p ∧ rel x u t'

/-- **Fresh draws, pointwise.** After a step whose hit set gains exactly the points cached
before it that the answer `u` at `x` relates to, the potential at budget `n` is at most
`a ^ k`, plus `a ^ (k - 1)` when `u` hits a pending designated point, where `a = n * ε` and `k`
is the number of pending positions before the step. -/
theorem hitPot_le_of_hits_eq_union (hs : HitInv τ Lfam s) (hD : HitDistinct rel jF P s)
    (hy : y ∈ support ((classPosImplFwd R τ hR (freshHitAux trig rel) t).run s))
    (x : spec.Domain) (u : spec.Range x)
    (hh : y.2.2.2 = s.2.2 ∪ {t' | s.1.1 t' ≠ none ∧ rel x u t'}) (ε : ℝ≥0∞) (n : ℕ) :
    hitPot τ Lfam rel jF P ε n y.2 ≤ ((n : ℝ≥0∞) * ε) ^ hitPending jF P s +
      {u' | HitsPending rel jF P s x u'}.indicator
        (fun _ => ((n : ℝ≥0∞) * ε) ^ (hitPending jF P s - 1)) u := by
  classical
  have hy' := (hitInv_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy).1
  by_cases hDy : HitDistinct rel jF P y.2
  swap
  · rw [hitPot_of_not_hitDistinct hy' hDy]
    exact zero_le
  rw [hitPot_of_hitDistinct hy' hDy]
  set a : ℝ≥0∞ := (n : ℝ≥0∞) * ε
  set k := hitPending jF P s
  have hle : hitPending jF P y.2 ≤ k :=
    hitPending_le_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy
  -- the positions the draw clears
  set C := P.filter fun p => ¬ HitCleared jF s p ∧
    ∃ t', s.2.1.cls t' = some jF ∧ s.2.1.pos t' = some p ∧ rel x u t'
  have hsub : (P.filter fun p => ¬ HitCleared jF s p) ⊆
      (P.filter fun p => ¬ HitCleared jF y.2 p) ∪ C := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hc : HitCleared jF y.2 p
    · obtain ⟨t', hc', hp', hm⟩ :=
        (hitCleared_iff_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy p).1 hc
      rw [hh] at hm
      rcases hm with hm | hm
      · exact absurd ⟨t', hc', hp', hm⟩ hp.2
      · exact Or.inr ⟨hp.1, hp.2, t', hc', hp', hm.2⟩
    · exact Or.inl ⟨hp.1, hc⟩
  have hk : k ≤ hitPending jF P y.2 + C.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hC1 : C.card ≤ 1 := by
    refine Finset.card_le_one.2 fun p hp p' hp' => ?_
    obtain ⟨hpP, -, t₁, hc₁, hp₁, hr₁⟩ := Finset.mem_filter.1 hp
    obtain ⟨hpP', -, t₂, hc₂, hp₂, hr₂⟩ := Finset.mem_filter.1 hp'
    obtain rfl := hD t₁ t₂ p p' hpP hpP' hc₁ hp₁ hc₂ hp₂ x u hr₁ hr₂
    exact Option.some_injective _ (hp₁.symm.trans hp₂)
  by_cases hB : HitsPending rel jF P s x u
  · rw [Set.indicator_of_mem (show u ∈ {u' | HitsPending rel jF P s x u'} from hB)]
    rcases le_total a 1 with ha | ha
    · exact (pow_le_pow_of_le_one zero_le ha (by omega)).trans le_add_self
    · exact (pow_le_pow_right₀ ha hle).trans le_self_add
  · have hC0 : C.card = 0 := Finset.card_eq_zero.2 (Finset.filter_false_of_mem
      fun p hp ⟨hn, ht⟩ => hB ⟨p, hp, hn, ht⟩)
    rw [Set.indicator_of_notMem (show u ∉ {u' | HitsPending rel jF P s x u'} from hB), add_zero]
    exact le_of_eq (congrArg _ (by omega))

omit [DecidableEq ι] [DecidableEq J] in
/-- **The mass of hitting a pending designated point.** If `rel x u t` has mass at most `ε` over
a uniform `u` for every point `t`, a uniform answer at `x` hits a point sitting at a pending
designated position with probability at most `ε` per pending position. -/
theorem prEvent_hitsPending_le (hs : HitInv τ Lfam s) (x : spec.Domain) {ε : ℝ≥0∞}
    (hε : ∀ t', Pr{let u ← ($ᵗ spec.Range x : ProbComp _)}[rel x u t'] ≤ ε) :
    Pr{let u ← ($ᵗ spec.Range x : ProbComp _)}[HitsPending rel jF P s x u] ≤
      hitPending jF P s * ε := by
  classical
  have hev : ∀ u, HitsPending rel jF P s x u ↔ ∃ p ∈ P.filter fun p => ¬ HitCleared jF s p,
      ∃ t', s.2.1.cls t' = some jF ∧ s.2.1.pos t' = some p ∧ rel x u t' := fun u => by
    simp only [HitsPending, Finset.mem_filter, and_assoc]
  simp only [hev]
  refine (prEvent_exists_finset_le _ _ _).trans ?_
  rw [hitPending, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun p _ => ?_
  by_cases hp : ∃ t₀, s.2.1.cls t₀ = some jF ∧ s.2.1.pos t₀ = some p
  · obtain ⟨t₀, hc₀, hp₀⟩ := hp
    refine (prEvent_mono _ _ _ fun u ⟨t', hc', hp', hr⟩ => ?_).trans (hε t₀)
    rwa [← hs.1.pos_inj t' t₀ jF p hc' hp' hc₀ hp₀]
  · rw [prEvent_eq_zero_of_forall_not _ _ fun u ⟨t', hc', hp', _⟩ => hp ⟨t', hc', hp'⟩]
    exact zero_le

end Step

/-! ## The expected step -/

section Expected

/-- A bound `a ^ k`, raised by `a ^ (k - 1)` on an event of mass at most `k * ε`, has expectation
at most `(a + ε) ^ k` over a uniform sample. -/
private theorem lintegral_uniformSample_le {A : Type} [SampleableType A] (f : A → ℝ≥0∞)
    (B : Set A) (a ε : ℝ≥0∞) (k : ℕ) (hf : ∀ u, f u ≤ a ^ k + B.indicator (fun _ => a ^ (k - 1)) u)
    (hB : Pr{let u ← ($ᵗ A : ProbComp A)}[u ∈ B] ≤ k * ε) :
    ∫⁻ r, r ∂𝒟[f <$> ($ᵗ A : ProbComp A)] ≤ (a + ε) ^ k := by
  let _ : MeasurableSpace A := ⊤
  refine (lintegral_id_evalDist_map_mono _ hf).trans ?_
  calc ∫⁻ r, r ∂𝒟[(fun u => a ^ k + B.indicator (fun _ => a ^ (k - 1)) u) <$>
          ($ᵗ A : ProbComp A)]
      = ∫⁻ r, r ∂𝒟[(fun _ => a ^ k) <$> ($ᵗ A : ProbComp A)] +
          ∫⁻ r, r ∂𝒟[B.indicator (fun _ => a ^ (k - 1)) <$> ($ᵗ A : ProbComp A)] :=
        lintegral_id_evalDist_map_add _ _ _
    _ ≤ a ^ k + a ^ (k - 1) * (k * ε) := by
        gcongr
        · exact lintegral_id_evalDist_map_le_of_le _ fun _ => le_rfl
        · rw [lintegral_id_evalDist_map, lintegral_indicator_const MeasurableSet.of_discrete]
          rw [prEvent_eq_evalDist_of_discrete] at hB
          gcongr
          exact hB
    _ = a ^ k + k * a ^ (k - 1) * ε := by ring
    _ ≤ (a + ε) ^ k := pow_add_mul_le_add_pow zero_le zero_le k

variable [DecidableEq ι] [DecidableEq J] [∀ t : spec.Domain, SampleableType (spec.Range t)]
  (trig : spec.Domain → Prop) [DecidablePred trig]
  (rel : (x : spec.Domain) → spec.Range x → spec.Domain → Prop)
  (τ : (spec + spec).Domain → J)
  (hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t))
  (Lfam : (k : J) → List (R k)) (jF : J) (P : Finset ℕ) (ε : ℝ≥0∞)

/-- **The hit-potential step.** If the tapes of the classes of every `trig` point are empty,
`rel x u t` has mass at most `ε` over a uniform `u` at every `trig` point `x`, and every query
at a `trig` point is `charged`, then one step of the instrumented run raises the expected hit
potential by at most one budget level at a charged query and not at all otherwise. -/
theorem hitPot_step
    (hlazy : ∀ x, trig x → Lfam (τ (.inl x)) = [] ∧ Lfam (τ (.inr x)) = [])
    (hε : ∀ x, trig x → ∀ t', Pr{let u ← ($ᵗ spec.Range x : ProbComp _)}[rel x u t'] ≤ ε)
    (charged : (unifSpec + (spec + spec)).Domain → Prop) [DecidablePred charged]
    (hcharged : ∀ x, trig x → charged (.inr (.inl x)) ∧ charged (.inr (.inr x)))
    (t : (unifSpec + (spec + spec)).Domain) (s : HitState spec R) (n : ℕ) :
    ∫⁻ r, r ∂𝒟[(fun z => hitPot τ Lfam rel jF P ε n z.2) <$>
        (classPosImplFwd R τ hR (freshHitAux trig rel) t).run s] ≤
      hitPot τ Lfam rel jF P ε (n + if charged t then 1 else 0) s := by
  classical
  by_cases hs : HitInv τ Lfam s
  swap
  · rw [hitPot_of_not_hitInv hs]
    exact le_top
  by_cases hD : HitDistinct rel jF P s
  swap
  · refine (lintegral_id_evalDist_map_le_of_le_of_mem_support _ fun y hy => ?_).trans zero_le
    rw [hitPot_of_not_hitDistinct
      (hitInv_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy).1
      (mt (hitDistinct_of_mem_support_classPosImplFwd_run trig rel τ hR hs hy) hD)]
  by_cases hfresh : ∃ x, (t = .inr (.inl x) ∨ t = .inr (.inr x)) ∧ s.1.1 x = none ∧ trig x
  · obtain ⟨x, ht, hc, hx⟩ := hfresh
    have hch : charged t := by
      rcases ht with rfl | rfl
      exacts [(hcharged x hx).1, (hcharged x hx).2]
    simp only [hch, ↓reduceIte]
    rw [hitPot_of_hitDistinct hs hD, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    obtain ⟨⟨c, L⟩, q⟩ := s
    -- the tapes of the classes of `x` are empty
    have hnil : ∀ j, Lfam j = [] → L j = [] := fun j hj => by
      have := hs.1.length_add j
      simp only [hj, List.length_nil, Nat.add_eq_zero_iff] at this
      exact List.eq_nil_of_length_eq_zero this.1
    rcases ht with rfl | rfl
    · have hrun : (classPosImplFwd R τ hR (freshHitAux trig rel) (.inr (.inl x))).run
          ((c, L), q) = (fun u => (u, ((c.cacheQuery x u, L), (classPosAuxFwd R τ (.inr (.inl x))
            (c, L) u (c.cacheQuery x u, L) q.1, freshHitStep trig rel c x u q.2)))) <$>
            ($ᵗ spec.Range x : ProbComp _) := by
        rw [QueryImpl.extendState_apply]
        simp [tapeCachingImplClass_apply_inl, tapeStep_run_nil hc (hnil _ (hlazy x hx).1),
          freshHitAux]
      rw [hrun, Functor.map_map]
      refine lintegral_uniformSample_le _ {u | HitsPending rel jF P ((c, L), q) x u} _ _ _
        (fun u => ?_) (prEvent_hitsPending_le rel τ hs x (hε x hx))
      refine hitPot_le_of_hits_eq_union trig rel τ hR (t := .inr (.inl x)) hs hD (y := (u, _)) ?_
        x u (freshHitStep_of_eq_none trig rel hc hx) ε n
      rw [hrun, support_map, support_uniformSample, Set.image_univ]
      exact ⟨u, rfl⟩
    · have hrun : (classPosImplFwd R τ hR (freshHitAux trig rel) (.inr (.inr x))).run
          ((c, L), q) = (fun u => (u, ((c.cacheQuery x u, L), (classPosAuxFwd R τ (.inr (.inr x))
            (c, L) u (c.cacheQuery x u, L) q.1, freshHitStep trig rel c x u q.2)))) <$>
            ($ᵗ spec.Range x : ProbComp _) := by
        rw [QueryImpl.extendState_apply]
        simp [tapeCachingImplClass_apply_inr, tapeStep_run_nil hc (hnil _ (hlazy x hx).2),
          freshHitAux]
      rw [hrun, Functor.map_map]
      refine lintegral_uniformSample_le _ {u | HitsPending rel jF P ((c, L), q) x u} _ _ _
        (fun u => ?_) (prEvent_hitsPending_le rel τ hs x (hε x hx))
      refine hitPot_le_of_hits_eq_union trig rel τ hR (t := .inr (.inr x)) hs hD (y := (u, _)) ?_
        x u (freshHitStep_of_eq_none trig rel hc hx) ε n
      rw [hrun, support_map, support_uniformSample, Set.image_univ]
      exact ⟨u, rfl⟩
  · push Not at hfresh
    have hh := hits_eq_self_of_mem_support_classPosImplFwd_run trig rel τ hR t s
      fun x hxt hc => hfresh x hxt hc
    refine (lintegral_id_evalDist_map_le_of_le_of_mem_support _ fun y hy =>
      hitPot_le_of_hits_eq trig rel τ hR hs hy (hh y hy) ε n).trans
      (hitPot_mono ε s (Nat.le_add_right n _))

/-- **Hitting every designated position.** If the tapes of the classes of every `trig` point
are empty, `rel x u t` has mass at most `ε` over a uniform `u` at every `trig` point `x`, and
`oa` makes at most `n` `charged` queries, where every query at a `trig` point is `charged`,
then the instrumented run of `oa` from the empty state reaches `HitAll` with probability at
most `(n * ε) ^ P.card`. -/
theorem prEvent_hitAll_le
    (hlazy : ∀ x, trig x → Lfam (τ (.inl x)) = [] ∧ Lfam (τ (.inr x)) = [])
    (hε : ∀ x, trig x → ∀ t', Pr{let u ← ($ᵗ spec.Range x : ProbComp _)}[rel x u t'] ≤ ε)
    (charged : (unifSpec + (spec + spec)).Domain → Prop) [DecidablePred charged]
    (hcharged : ∀ x, trig x → charged (.inr (.inl x)) ∧ charged (.inr (.inr x)))
    {α : Type} (oa : OracleComp (unifSpec + (spec + spec)) α) (n : ℕ)
    (hq : IsQueryBoundP oa charged n) :
    Pr{let z ← (simulateQ (classPosImplFwd R τ hR (freshHitAux trig rel)) oa).run
        ((∅, Lfam), (ClassPos.init, ∅))}[HitAll rel jF P z.2] ≤ ((n : ℝ≥0∞) * ε) ^ P.card :=
  (prEvent_run_le_of_isQueryBoundP _ charged (hitPot τ Lfam rel jF P ε) (hitPot_mono ε)
    (hitPot_step trig rel τ hR Lfam jF P ε hlazy hε charged hcharged) _
    (fun _ h => one_le_hitPot_of_hitAll ε h) oa n hq _).trans_eq (hitPot_init ε n)

end Expected

end AnswerTape
