/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.WP.OracleMeasure
public import VCVio.ProgramLogic.Unary.WP.Quantitative
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.OracleComp.Constructions.Replicate.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import ToMathlib.MeasureTheory.Measure.Bounds

/-!
# Quantitative Hoare triples

`wp` and `Triple` expose the expectation interpretation of core's lattice-generic
weakest-precondition API for `OracleComp`. Their equations follow from the ordered
expectation algebra in `Unary/WP/Quantitative.lean`.

Core's `⦃ pre ⦄ program ⦃ post ⦄` notation is available through
`open scoped Std.Internal.Do OracleComp.Quantitative`. VCVio's quantitative facade
keeps the carrier explicit in its definitions.
-/

@[expose] public section

open ENNReal MeasureTheory
open Std.Internal.Do
open scoped OracleComp.Quantitative

universe u

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic

/-! ## Prop-to-ℝ≥0∞ indicator -/

open scoped Classical in
/-- Indicator embedding: lifts `P : Prop` into `ℝ≥0∞` as `1` (true) or `0` (false).
It takes values in the expectation carrier `ℝ≥0∞`. -/
noncomputable def propInd (P : Prop) : ℝ≥0∞ := if P then 1 else 0

@[simp] lemma propInd_true : propInd True = 1 := ite_eq_left trivial
@[simp] lemma propInd_false : propInd False = 0 := ite_eq_right id

lemma propInd_eq_ite {P : Prop} [Decidable P] : propInd P = if P then 1 else 0 := by simp [propInd]

open scoped Classical in
@[simp] lemma propInd_and {P Q : Prop} : propInd (P ∧ Q) = propInd P * propInd Q := by
  unfold propInd; split_ifs <;> simp_all

open scoped Classical in
@[gcongr] lemma propInd_mono {P Q : Prop} (h : P → Q) : propInd P ≤ propInd Q := by
  unfold propInd; split_ifs <;> simp_all

lemma propInd_le_one (P : Prop) : propInd P ≤ 1 := by
  unfold propInd; split_ifs <;> simp

open scoped Classical in
lemma propInd_eq_one_iff {P : Prop} : propInd P = 1 ↔ P := by simp [propInd]

open scoped Classical in
lemma propInd_eq_zero_iff {P : Prop} : propInd P = 0 ↔ ¬P := by simp [propInd]

open scoped Classical in
lemma propInd_or_le {P Q : Prop} : propInd (P ∨ Q) ≤ propInd P + propInd Q := by
  unfold propInd; split_ifs <;> simp_all

open scoped Classical in
lemma propInd_not {P : Prop} : propInd (¬P) = 1 - propInd P := by
  unfold propInd; split_ifs <;> simp_all



variable {ι : Type u} {spec : OracleSpec ι}
variable [∀ t, MeasurableSpace (spec.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec.Range t)]
variable {α β σ : Type}

section Native

variable [OracleSpec.IsMeasureSpec spec]

/-! ## API contract

This interface uses the configured native measure interpretation, with assertions in `ℝ≥0∞`.
The abbreviations fix the empty exception postcondition
while retaining core's WP and triple representations.
-/

/-- Quantitative weakest-precondition for `OracleComp spec`, fixing the
exception postcondition to `Lean.Order.bot`. Definitionally equal to
`Std.Internal.Do.wp oa post Lean.Order.bot`; see the API contract for details. -/
noncomputable abbrev wp (oa : OracleComp spec α) (post : α → ℝ≥0∞) : ℝ≥0∞ :=
  Std.Internal.Do.wp oa post Lean.Order.bot

/-- Quantitative Hoare triple for `OracleComp spec`, fixing the exception
postcondition to `Lean.Order.bot`. Definitionally equal to
`Std.Internal.Do.Triple oa pre post Lean.Order.bot`; see the API contract for
details. -/
noncomputable abbrev Triple (pre : ℝ≥0∞) (oa : OracleComp spec α)
    (post : α → ℝ≥0∞) : Prop :=
  Std.Internal.Do.Triple oa pre post Lean.Order.bot

/-! ## Internal alias

`MAlgOrdered.wp` is `rfl`-equal to `wp _ _` on
`OracleComp` via the `OracleComp.Quantitative.instWP` instance. The bridge `wp_eq_mAlgOrdered_wp`
re-exposes this so existing `MAlgOrdered.wp_*` lemmas can be applied with
a single rewrite. -/

theorem wp_eq_mAlgOrdered_wp (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp oa post =
      MAlgOrdered.wp (m := OracleComp spec) (l := ℝ≥0∞) oa post := rfl

/-- Quantitative WP integrates a measurable assertion in the chosen output space. -/
theorem wp_eq_lintegral [MeasurableSpace α] (oa : OracleComp spec α)
    (post : α → ℝ≥0∞) (hpost : Measurable post) :
    wp oa post = ∫⁻ x, post x ∂𝒟[oa] :=
  MeasureProgramLogic.Quantitative.wp_eq_lintegral oa post hpost

/-- Quantitative WP integrates the assertion-valued observation, without an output space. -/
theorem wp_eq_lintegral_map (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp oa post = ∫⁻ y, y ∂𝒟[post <$> oa] :=
  MeasureProgramLogic.Quantitative.wp_eq_lintegral_map oa post

/-- A quantitative core triple is the corresponding inequality of expectations. -/
theorem triple_iff_le_wp
    (pre : ℝ≥0∞) (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Triple pre oa post ↔
      pre ≤ wp oa post :=
  Std.Internal.Do.Triple.iff (epost := Lean.Order.bot)

/-- Construct a quantitative triple from an expectation inequality. -/
theorem triple_ofLE
    {pre : ℝ≥0∞} {oa : OracleComp spec α} {post : α → ℝ≥0∞}
    (h : pre ≤ wp oa post) :
    Triple pre oa post :=
  (triple_iff_le_wp pre oa post).mpr h

/-- Extract the `≤`-form `pre ≤ wp oa post` from a
`Triple …`. Companion to `triple_iff_le_wp.mp`. -/
theorem triple_toLE
    {pre : ℝ≥0∞} {oa : OracleComp spec α} {post : α → ℝ≥0∞}
    (h : Triple pre oa post) :
    pre ≤ wp oa post :=
  (triple_iff_le_wp pre oa post).mp h

/-! ## `wp` lemmas (against `wp _ _`) -/

@[game_rule] theorem wp_pure (x : α) (post : α → ℝ≥0∞) :
    wp (pure x : OracleComp spec α) post = post x := by
  rw [wp_eq_mAlgOrdered_wp, MAlgOrdered.wp_pure]

@[game_rule] theorem wp_ite (c : Prop) [Decidable c]
    (oa ob : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (if c then oa else ob) post =
      if c then wp oa post
      else wp ob post := by
  split_ifs <;> rfl

@[game_rule] theorem wp_dite (c : Prop) [Decidable c]
    (oa : c → OracleComp spec α) (ob : ¬c → OracleComp spec α) (post : α → ℝ≥0∞) :
    wp (dite c oa ob) post =
      dite c (fun h => wp (oa h) post)
        (fun h => wp (ob h) post) := by
  split_ifs <;> rfl

@[game_rule] theorem wp_bind (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (post : β → ℝ≥0∞) :
    wp (oa >>= ob) post =
      wp oa (fun x => wp (ob x) post) := by
  simp only [wp_eq_mAlgOrdered_wp]
  exact MAlgOrdered.wp_bind (m := OracleComp spec) (l := ℝ≥0∞) oa ob post

@[game_rule] theorem wp_replicate_zero (oa : OracleComp spec α) (post : List α → ℝ≥0∞) :
    wp (oa.replicate 0) post = post [] := by
  simp [OracleComp.replicate_zero]

@[game_rule] theorem wp_replicate_succ
    (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp (oa.replicate (n + 1)) post =
      wp oa
        (fun x => wp (oa.replicate n)
          (fun xs => post (x :: xs))) := by
  rw [OracleComp.replicate_succ_bind, wp_bind]
  congr 1
  funext x
  rw [wp_bind]
  simp

@[game_rule] theorem wp_list_mapM_nil
    (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp (([] : List α).mapM f) post = post [] := by
  simp

@[game_rule] theorem wp_list_mapM_cons
    (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp ((x :: xs).mapM f) post =
      wp (f x)
        (fun y => wp (xs.mapM f)
          (fun ys => post (y :: ys))) := by
  rw [List.mapM_cons, wp_bind]
  congr 1
  funext y
  rw [wp_bind]
  simp

@[game_rule] theorem wp_list_foldlM_nil
    (f : σ → α → OracleComp spec σ) (init : σ) (post : σ → ℝ≥0∞) :
    wp (([] : List α).foldlM f init) post = post init := by
  simp

@[game_rule] theorem wp_list_foldlM_cons
    (x : α) (xs : List α) (f : σ → α → OracleComp spec σ)
    (init : σ) (post : σ → ℝ≥0∞) :
    wp ((x :: xs).foldlM f init) post =
      wp (f init x)
        (fun s => wp (xs.foldlM f s) post) := by
  rw [List.foldlM_cons, wp_bind]

/-- `wp` is monotone in the postcondition; `gcongr` descends through it. -/
@[gcongr low]
theorem wp_mono (oa : OracleComp spec α) {post post' : α → ℝ≥0∞}
    (hpost : ∀ x, post x ≤ post' x) :
    wp oa post ≤ wp oa post' := by
  exact MAlgOrdered.wp_mono oa hpost

/-- `wp` is monotone when the postconditions are ordered on the computation's support. -/
@[gcongr]
theorem wp_mono_of_support (oa : OracleComp spec α) {post post' : α → ℝ≥0∞}
    (hpost : ∀ x ∈ support oa, post x ≤ post' x) : wp oa post ≤ wp oa post' :=
  MeasureProgramLogic.Quantitative.wp_mono_of_support oa hpost

/-- Support-aware comparison on PolyFun's canonical quantitative WP head. -/
@[gcongr]
theorem mAlgOrdered_wp_mono_of_support (oa : OracleComp spec α) {post post' : α → ℝ≥0∞}
    (hpost : ∀ x ∈ support oa, post x ≤ post' x) :
    MAlgOrdered.wp oa post ≤ MAlgOrdered.wp oa post' :=
  wp_mono_of_support oa hpost

/-- Finite postconditions over a finite result type have finite weakest precondition. -/
@[aesop (rule_sets := [finiteness]) safe apply]
theorem wp_ne_top_of_finite [Finite α] (oa : OracleComp spec α) {post : α → ℝ≥0∞}
    (hpost : ∀ x, post x ≠ ⊤) : wp oa post ≠ ⊤ := by
  let c := ⨆ x, post x
  have hc : c ≠ ⊤ := iSup_ne_top hpost
  exact ne_top_of_le_ne_top hc
    (MeasureProgramLogic.Quantitative.wp_le_const_of_support oa fun x _ ↦ le_iSup post x)

@[game_rule] theorem wp_map (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp (f <$> oa) post =
      wp oa (post ∘ f) := by
  simp [Function.comp_def]

theorem wp_const (oa : OracleComp spec α) (c : ℝ≥0∞) :
    MAlgOrdered.wp oa (fun _ ↦ c) = c :=
  MeasureProgramLogic.Quantitative.wp_const_of_oracle oa c

@[game_rule] theorem wp_add (oa : OracleComp spec α) (f g : α → ℝ≥0∞) :
    wp oa (fun x ↦ f x + g x) = wp oa f + wp oa g :=
  MeasureProgramLogic.Quantitative.wp_add_of_oracle oa f g

theorem wp_const_mul (oa : OracleComp spec α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    wp oa (fun x ↦ f x * c) = wp oa f * c := by
  simpa only [wp_eq_mAlgOrdered_wp, mul_comm] using
    (MeasureProgramLogic.Quantitative.wp_const_mul_of_oracle oa c f)

@[game_rule] theorem wp_mul_const (oa : OracleComp spec α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    wp oa (fun x ↦ c * f x) = c * wp oa f :=
  MeasureProgramLogic.Quantitative.wp_const_mul_of_oracle oa c f

/-- A support-wise postcondition bound controls the quantitative WP. -/
theorem wp_le_const_of_support (oa : OracleComp spec α) {post : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hpost : ∀ x ∈ support oa, post x ≤ c) : wp oa post ≤ c :=
  (wp_mono_of_support oa hpost).trans_eq (by simp)

/-- Additive support-wise comparison of quantitative postconditions. -/
theorem wp_le_const_add_of_support (oa : OracleComp spec α) {f g : α → ℝ≥0∞}
    {c : ℝ≥0∞} (hfg : ∀ x ∈ support oa, f x ≤ c + g x) :
    wp oa f ≤ c + wp oa g := by
  refine (wp_mono_of_support oa hfg).trans_eq ?_
  rw [wp_add]
  simp

/-- Finite sums of quantitative postconditions commute with expectation. -/
theorem wp_finsetSum {κ : Type*} (oa : OracleComp spec α) (s : Finset κ)
    (f : κ → α → ℝ≥0∞) :
    wp oa (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, wp oa (f i) :=
  MeasureProgramLogic.Quantitative.wp_finsetSum_of_oracle oa s f

/-! ## `Triple` lemmas (against `Triple _ _ _`)

`Std.Internal.Do.Triple` is an inductive wrapper around `pre ⊑ wp …`. The
accessor `Std.Internal.Do.Triple.iff` exchanges between the inductive form and
the `≤`-form; `triple_ofLE` packages a `≤`-proof into the
constructor; pattern matching `match h with | .intro h => h` extracts
the underlying inequality. -/

theorem triple_conseq {pre pre' : ℝ≥0∞} {oa : OracleComp spec α}
    {post post' : α → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ x, post x ≤ post' x) :
    Triple pre oa post →
      Triple pre' oa post' := fun h =>
  triple_ofLE
    (le_trans hpre (le_trans (triple_toLE h)
      (MAlgOrdered.wp_mono (m := OracleComp spec) (l := ℝ≥0∞) oa hpost)))

theorem triple_bind {pre : ℝ≥0∞} {oa : OracleComp spec α}
    {cut : α → ℝ≥0∞} {ob : α → OracleComp spec β} {post : β → ℝ≥0∞}
    (hoa : Triple pre oa cut)
    (hob : ∀ x, Triple (cut x) (ob x) post) :
    Triple pre (oa >>= ob) post :=
  triple_ofLE (MAlgOrdered.triple_bind (m := OracleComp spec) (l := ℝ≥0∞)
    (triple_toLE hoa) fun x => triple_toLE (hob x))

theorem triple_bind_wp {pre : ℝ≥0∞} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {post : β → ℝ≥0∞}
    (h : Triple pre oa
          (fun x => wp (ob x) post)) :
    Triple pre (oa >>= ob) post :=
  triple_ofLE (by rw [wp_bind]; exact triple_toLE h)

theorem triple_pure (x : α) (post : α → ℝ≥0∞) :
    Triple (post x) (pure x : OracleComp spec α) post :=
  triple_ofLE (by simp)

/-- A quantitative triple with precondition `0` is always true. -/
theorem triple_zero (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    Triple (0 : ℝ≥0∞) oa post :=
  triple_ofLE (by simp)

theorem triple_ite {c : Prop} [Decidable c] {pre : ℝ≥0∞}
    {oa ob : OracleComp spec α} {post : α → ℝ≥0∞}
    (ht : c → Triple pre oa post)
    (hf : ¬c → Triple pre ob post) :
    Triple pre (if c then oa else ob) post := by
  split_ifs with h
  · exact ht h
  · exact hf h

theorem triple_dite {c : Prop} [Decidable c] {pre : ℝ≥0∞}
    {oa : c → OracleComp spec α} {ob : ¬c → OracleComp spec α} {post : α → ℝ≥0∞}
    (ht : ∀ h : c, Triple pre (oa h) post)
    (hf : ∀ h : ¬c, Triple pre (ob h) post) :
    Triple pre (dite c oa ob) post := by
  split_ifs with h
  · exact ht h
  · exact hf h

open scoped Classical in
/-- An observed event probability is WP of its indicator assertion. -/
lemma probEvent_eq_wp_indicator (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] :
    Pr{let x ← oa}[p x] = wp oa (fun x ↦ if p x then 1 else 0) := by
  rw [prEvent_eq_evalDist_map]
  have h := wp_eq_lintegral (p <$> oa) (fun b ↦ if b then 1 else 0) Measurable.of_discrete
  rw [wp_map] at h
  have hi : (fun b : Prop ↦ if b then (1 : ℝ≥0∞) else 0) =
      ({True} : Set Prop).indicator (fun _ ↦ 1) := by
    funext b
    simp only [Set.indicator_apply, Set.mem_singleton_iff, eq_iff_iff, iff_true]
  calc
    _ = ∫⁻ b : Prop, (if b then 1 else 0) ∂𝒟[p <$> oa] := by
      rw [hi, lintegral_indicator_const (measurableSet_singleton True), one_mul]
    _ = _ := h.symm.trans (by
      congr 1
      funext x
      by_cases hx : p x <;> simp [hx])

/-- Native event probability is WP of its proposition indicator. -/
lemma probEvent_eq_wp_propInd {ι : Type u} {spec : OracleSpec ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← oa}[p x] = wp oa (fun x => propInd (p x)) := by
  classical
  simpa only [propInd_eq_ite] using probEvent_eq_wp_indicator oa p

/-- An observed singleton probability is WP of its indicator assertion. -/
lemma probOutput_eq_wp_indicator (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Pr{let y ← oa}[y = x] = wp oa (fun y ↦ if y = x then 1 else 0) :=
  probEvent_eq_wp_indicator oa (fun y ↦ y = x)

/-- Assertions agreeing on structural support have equal quantitative WP. -/
lemma wp_congr_of_support (oa : OracleComp spec α) {f g : α → ℝ≥0∞}
    (hfg : ∀ x ∈ support oa, f x = g x) : wp oa f = wp oa g :=
  le_antisymm (wp_mono_of_support oa fun x hx ↦ (hfg x hx).le)
    (wp_mono_of_support oa fun x hx ↦ (hfg x hx).ge)

open scoped Classical in
/-- Finite-response computations integrate assertions by a finite partition of reachable outputs.
The output labels need no measurable-space instance. -/
theorem wp_eq_sum_finSupport [∀ t, Fintype (spec.Range t)] [DecidableEq α] (oa : OracleComp spec α)
    (post : α → ℝ≥0∞) :
    wp oa post = ∑ x ∈ finSupport oa, Pr{let y ← oa}[y = x] * post x := by
  classical
  calc
    _ = wp oa (fun y ↦ ∑ x ∈ finSupport oa, if y = x then post x else 0) := by
      apply wp_congr_of_support
      intro y hy
      simp [Finset.sum_ite_eq, mem_finSupport_iff_mem_support, hy]
    _ = ∑ x ∈ finSupport oa, wp oa (fun y ↦ if y = x then post x else 0) :=
      wp_finsetSum oa _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [probOutput_eq_wp_indicator, ← wp_const_mul]
      congr 1
      funext y
      split_ifs <;> simp

open scoped Classical in
/-- The finite reachable-output partition extends to a native event-weighted sum. -/
theorem wp_eq_tsum [∀ t, Finite (spec.Range t)] (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp oa post = ∑' x, Pr{let y ← oa}[y = x] * post x := by
  let : DecidableEq α := Classical.decEq α
  let : ∀ t, Fintype (spec.Range t) := fun _ ↦ Fintype.ofFinite _
  rw [wp_eq_sum_finSupport]
  symm
  apply tsum_eq_sum
  intro x hx
  have hn : x ∉ support oa := by simpa only [mem_finSupport_iff_mem_support] using hx
  have hz : Pr{let y ← oa}[y = x] = 0 := by
    rw [prEvent_congr_of_support oa _ (fun _ ↦ False)]
    · exact prEvent_eq_zero_of_forall_not oa _ (fun _ h ↦ h)
    · intro y hy
      constructor
      · intro h; subst y; exact hn hy
      · intro h; exact h.elim
  rw [hz, zero_mul]

/-- A query's quantitative WP integrates against its configured answer measure. -/
@[game_rule] theorem wp_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp (query t : OracleComp spec (spec.Range t)) post =
      ∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t := by
  rw [wp_eq_lintegral _ _ Measurable.of_discrete, evalDist_liftM_query]

/-- Lifting a primitive query has the same native expectation rule. -/
theorem wp_liftM_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp (liftM (query t) : OracleComp spec (spec.Range t)) post =
      ∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t := by
  rw [wp_eq_lintegral _ _ Measurable.of_discrete, evalDist_liftM_query]

/-- The ergonomic query interface integrates the configured answer measure. -/
@[game_rule] theorem wp_HasQuery_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp (spec := spec) (HasQuery.query t : OracleComp spec (spec.Range t)) post =
      ∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t := wp_query t post

end Native

section Uniform

/-- A uniform query's expectation is its finite average. -/
theorem wp_query_uniform [OracleSpec.IsUniformMeasureSpec spec]
    (t : spec.Domain) [Fintype (spec.Range t)] (post : spec.Range t → ℝ≥0∞) :
    wp (query t : OracleComp spec (spec.Range t)) post =
      ∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * post u := by
  rw [wp_query, OracleSpec.IsMeasureSpec.toMeasure_eq_uniformOn]
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_comm]
  congr 1
  simp [ProbabilityTheory.uniformOn_univ]

end Uniform

section Native

variable [OracleSpec.IsMeasureSpec spec]

/-- Uniform sampling integrates its chosen native measure. -/
@[game_rule] theorem wp_uniformSample [SampleableType α] (post : α → ℝ≥0∞) :
    wp ($ᵗ α) post = ∫⁻ y, y ∂𝒟[post <$> ($ᵗ α : ProbComp α)] :=
  wp_eq_lintegral_map _ _

/-- Indicator-event probability as an exact quantitative triple. -/
theorem triple_probEvent_indicator (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Triple (Pr{let x ← oa}[p x]) oa (fun x => if p x then 1 else 0) :=
  triple_ofLE (by rw [probEvent_eq_wp_indicator])

/-- Singleton-output probability as an exact quantitative triple. -/
theorem triple_probOutput_indicator (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Triple (Pr{let y ← oa}[y = x]) oa (fun y => if y = x then 1 else 0) :=
  triple_ofLE (by rw [probOutput_eq_wp_indicator])

/-- Lower bounds on `probEvent` are exactly indicator-postcondition triples. -/
theorem le_probEvent_iff_triple_indicator (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] (r : ℝ≥0∞) :
    r ≤ Pr{let x ← oa}[p x] ↔
      Triple r oa (fun x => if p x then 1 else 0) := by
  rw [triple_iff_le_wp, ← probEvent_eq_wp_indicator]

/-- Lower bounds on `probOutput` are exactly singleton-indicator triples. -/
theorem le_probOutput_iff_triple_indicator (oa : OracleComp spec α) [DecidableEq α]
    (x : α) (r : ℝ≥0∞) :
    r ≤ Pr{let y ← oa}[y = x] ↔
      Triple r oa (fun y => if y = x then 1 else 0) := by
  rw [triple_iff_le_wp, ← probOutput_eq_wp_indicator]

/-- The support event of an `OracleComp` occurs almost surely. -/
theorem probEvent_mem_support (oa : OracleComp spec α) :
    Pr{let x ← oa}[x ∈ support oa] = 1 := by
  rw [prEvent_congr_of_support oa _ (fun _ ↦ True) (fun _ hx ↦ by simp only [hx]),
    prEvent_eq_evalDist_map]
  simp

/-- Exact probability-1 events are exact quantitative triples. -/
theorem triple_probEvent_eq_one (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] (h : Pr{let x ← oa}[p x] = 1) :
    Triple (1 : ℝ≥0∞) oa (fun x => if p x then 1 else 0) := by
  have := triple_probEvent_indicator (oa := oa) p
  rwa [h] at this

/-- Exact probability-1 singleton outputs are exact quantitative triples. -/
theorem triple_probOutput_eq_one (oa : OracleComp spec α) [DecidableEq α]
    (x : α) (h : Pr{let y ← oa}[y = x] = 1) :
    Triple (1 : ℝ≥0∞) oa (fun y => if y = x then 1 else 0) := by
  have := triple_probOutput_indicator (oa := oa) x
  rwa [h] at this

/-- Probability-one singleton events are exactly probability-one indicator triples. -/
theorem probOutput_eq_one_iff_triple (oa : OracleComp spec α) [DecidableEq α]
    (x : α) :
    Pr{let y ← oa}[y = x] = 1 ↔
      Triple (1 : ℝ≥0∞) oa (fun y => if y = x then 1 else 0) := by
  constructor
  · exact triple_probOutput_eq_one oa x
  · intro h
    have hle : (1 : ℝ≥0∞) ≤ Pr{let y ← oa}[y = x] := by
      rw [probOutput_eq_wp_indicator]; exact triple_toLE h
    exact le_antisymm ((measure_mono (Set.subset_univ _)).trans
      (evalDist_apply_univ_le_one (do let y ← oa; pure (y = x)))) hle

/-- Support membership is a useful default cut function for support-sensitive bind proofs. -/
theorem triple_support (oa : OracleComp spec α) [DecidablePred fun x => x ∈ support oa] :
    Triple (1 : ℝ≥0∞) oa
      (fun x => if x ∈ support oa then 1 else 0) := by
  simpa using
    triple_probEvent_eq_one (oa := oa) (p := fun x => x ∈ support oa)
      (h := probEvent_mem_support (oa := oa))

/-! ## Loop stepping rules (Triple-level) -/

theorem triple_replicate_succ {pre : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    {post : List α → ℝ≥0∞}
    (h : Triple pre oa
          (fun x => wp (oa.replicate n)
            (fun xs => post (x :: xs)))) :
    Triple pre (oa.replicate (n + 1)) post :=
  triple_ofLE (by rw [wp_replicate_succ]; exact triple_toLE h)

theorem triple_list_mapM_cons {pre : ℝ≥0∞} {x : α} {xs : List α}
    {f : α → OracleComp spec β} {post : List β → ℝ≥0∞}
    (h : Triple pre (f x)
          (fun y => wp (xs.mapM f)
            (fun ys => post (y :: ys)))) :
    Triple pre ((x :: xs).mapM f) post :=
  triple_ofLE (by rw [wp_list_mapM_cons]; exact triple_toLE h)

theorem triple_list_foldlM_cons {pre : ℝ≥0∞} {x : α} {xs : List α}
    {f : σ → α → OracleComp spec σ} {init : σ} {post : σ → ℝ≥0∞}
    (h : Triple pre (f init x)
          (fun s => wp (xs.foldlM f s) post)) :
    Triple pre ((x :: xs).foldlM f init) post :=
  triple_ofLE (by rw [wp_list_foldlM_cons]; exact triple_toLE h)

/-! ## Loop invariant rules -/

/-- Constant invariant through bounded iteration via `replicate`. -/
theorem triple_replicate_inv {I : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    (hstep : Triple I oa (fun _ => I)) :
    Triple I (oa.replicate n) (fun _ => I) := by
  induction n with
  | zero => exact triple_pure [] (fun _ => I)
  | succ n ih =>
      rw [OracleComp.replicate_succ_bind]
      exact triple_bind hstep fun x => triple_bind ih fun xs =>
        triple_pure (x :: xs) (fun _ => I)

/-- Indexed invariant through `List.foldlM`. -/
theorem triple_list_foldlM_inv {I : σ → ℝ≥0∞}
    {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    (hstep : ∀ s x, x ∈ l → Triple (I s) (f s x) I) :
    Triple (I s₀) (l.foldlM f s₀) I := by
  induction l generalizing s₀ with
  | nil => exact triple_pure s₀ I
  | cons a as ih =>
      rw [List.foldlM_cons]
      exact triple_bind (hstep s₀ a (by simp)) fun s =>
        ih fun s x hx => hstep s x (by simp [hx])

/-- Constant invariant through `List.mapM`. -/
theorem triple_list_mapM_inv {I : ℝ≥0∞}
    {f : α → OracleComp spec β} {l : List α}
    (hstep : ∀ x, x ∈ l → Triple I (f x) (fun _ => I)) :
    Triple I (l.mapM f) (fun _ => I) := by
  induction l with
  | nil => exact triple_pure ([] : List β) (fun _ => I)
  | cons a as ih =>
      rw [List.mapM_cons]
      exact triple_bind (hstep a (by simp)) fun y =>
        triple_bind (ih fun x hx => hstep x (by simp [hx])) fun ys =>
          triple_pure (y :: ys) (fun _ => I)

/-- `replicate` invariant with consequence: bridges arbitrary pre/post to the invariant. -/
theorem triple_replicate {I pre : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : Triple I oa (fun _ => I)) :
    Triple pre (oa.replicate n) post :=
  triple_conseq hpre hpost (triple_replicate_inv hstep)

/-- `List.foldlM` invariant with consequence. -/
theorem triple_list_foldlM {I : σ → ℝ≥0∞}
    {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    {pre : ℝ≥0∞} {post : σ → ℝ≥0∞}
    (hpre : pre ≤ I s₀) (hpost : ∀ s, I s ≤ post s)
    (hstep : ∀ s x, x ∈ l → Triple (I s) (f s x) I) :
    Triple pre (l.foldlM f s₀) post :=
  triple_conseq hpre hpost (triple_list_foldlM_inv hstep)

/-- `List.mapM` invariant with consequence. -/
theorem triple_list_mapM {I : ℝ≥0∞}
    {f : α → OracleComp spec β} {l : List α}
    {pre : ℝ≥0∞} {post : List β → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ ys, I ≤ post ys)
    (hstep : ∀ x, x ∈ l → Triple I (f x) (fun _ => I)) :
    Triple pre (l.mapM f) post :=
  triple_conseq hpre hpost (triple_list_mapM_inv hstep)

/-! ## Congruence of native observations -/

/-- The expectation algebra evaluates the identity assertion. -/
lemma μ_eq_wp (oa : OracleComp spec ℝ≥0∞) : μ oa = wp oa (fun x ↦ x) := by
  simp [MAlgOrdered.wp, μ]

/-- Equal assertion-valued observations have equal quantitative WP. -/
lemma wp_congr_evalDist_map {oa ob : OracleComp spec α} (post : α → ℝ≥0∞)
    (h : 𝒟[post <$> oa] = 𝒟[post <$> ob]) : wp oa post = wp ob post := by
  rw [wp_eq_lintegral_map, wp_eq_lintegral_map, h]

/-- Equal chosen output measures give equal expectations of measurable assertions. -/
lemma wp_congr_evalDist [MeasurableSpace α] {oa ob : OracleComp spec α}
    (h : 𝒟[oa] = 𝒟[ob]) (post : α → ℝ≥0∞) (hpost : Measurable post) :
    wp oa post = wp ob post := by
  rw [wp_eq_lintegral oa post hpost, wp_eq_lintegral ob post hpost, h]

end Native

end OracleComp.ProgramLogic
