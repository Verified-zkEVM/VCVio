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

Expectations `wp⟦oa⟧ post` (`VCVio.EvalDist.Expectation`) and core's triples
`⦃ pre ⦄ oa ⦃ post ⦄` expose the expectation interpretation of core's lattice-generic
weakest-precondition API for `OracleComp`. The laws below specialize the generic ones to oracle
computations, which are lossless, and add the oracle-specific ones: queries, uniform sampling,
replication and traversals.

The expectation interpretation is the core instance of `OracleComp spec`
(`OracleComp.Quantitative.instWP`), so core's `⦃ pre ⦄ program ⦃ post ⦄` notation, available
through `open scoped Std.WP`, states these triples: it is `Std.WP.Triple program pre post ⊥`,
with the empty exception postcondition.
-/

@[expose] public section

open ENNReal MeasureTheory
open Std.WP
open scoped OracleComp.Quantitative

universe u

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable {α β σ : Type}

section MeasureSpec

variable [OracleSpec.IsMeasureSpec spec]

/-! ## API contract

This interface uses the configured measure interpretation, with assertions in `ℝ≥0∞`.
Expectations are core's `wp` under that interpretation, written `wp⟦oa⟧ post`. Triples are
core's `Std.WP.Triple oa pre post ⊥`, written `⦃ pre ⦄ oa ⦃ post ⦄`: `Std.WP.Triple.iff`
unfolds one to the inequality `pre ⊑ wp oa post ⊥`, which is `pre ≤ wp⟦oa⟧ post`.
-/

/-- Quantitative WP integrates a measurable assertion in the chosen output space. -/
theorem wp_eq_lintegral [MeasurableSpace α] (oa : OracleComp spec α)
    (post : α → ℝ≥0∞) (hpost : Measurable post) :
    wp⟦oa⟧ post = ∫⁻ x, post x ∂𝒟[oa] :=
  MeasureProgramLogic.wp_eq_lintegral oa post hpost

/-- Quantitative WP integrates the assertion-valued observation, without an output space. -/
theorem wp_eq_lintegral_map (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦oa⟧ post = ∫⁻ y, y ∂𝒟[post <$> oa] :=
  MeasureProgramLogic.wp_eq_lintegral_map oa post

/-! ## `wp` lemmas (against `wp _ _`)

The structural equations of an expectation are the generic ones, `MeasureProgramLogic.wp_pure`,
`wp_bind`, `wp_map`, `wp_add`, `wp_const_mul` and PolyFun's `ExactWPMonad.wp_ite` / `wp_dite`,
tagged here for the `game_rule` set; a constant observation of an oracle computation is
`MeasureProgramLogic.wp_const_of_oracle`. The rules below unfold the loop combinators. -/

attribute [game_rule] MeasureProgramLogic.wp_pure MeasureProgramLogic.wp_bind
  MeasureProgramLogic.wp_map MeasureProgramLogic.wp_add MeasureProgramLogic.wp_const_mul
  ExactWPMonad.wp_ite ExactWPMonad.wp_dite

@[game_rule] theorem wp_replicate_zero (oa : OracleComp spec α) (post : List α → ℝ≥0∞) :
    wp⟦oa.replicate 0⟧ post = post [] := by
  simp [OracleComp.replicate_zero]

@[game_rule] theorem wp_replicate_succ
    (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp⟦oa.replicate (n + 1)⟧ post =
      wp⟦oa⟧
        (fun x => wp⟦oa.replicate n⟧
          (fun xs => post (x :: xs))) := by
  rw [OracleComp.replicate_succ_bind, MeasureProgramLogic.wp_bind]
  congr 1
  funext x
  rw [MeasureProgramLogic.wp_bind]
  simp

@[game_rule] theorem wp_list_mapM_nil
    (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp⟦([] : List α).mapM f⟧ post = post [] := by
  simp

@[game_rule] theorem wp_list_mapM_cons
    (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp⟦(x :: xs).mapM f⟧ post =
      wp⟦f x⟧
        (fun y => wp⟦xs.mapM f⟧
          (fun ys => post (y :: ys))) := by
  rw [List.mapM_cons, MeasureProgramLogic.wp_bind]
  congr 1
  funext y
  rw [MeasureProgramLogic.wp_bind]
  simp

@[game_rule] theorem wp_list_foldlM_nil
    (f : σ → α → OracleComp spec σ) (init : σ) (post : σ → ℝ≥0∞) :
    wp⟦([] : List α).foldlM f init⟧ post = post init := by
  simp

@[game_rule] theorem wp_list_foldlM_cons
    (x : α) (xs : List α) (f : σ → α → OracleComp spec σ)
    (init : σ) (post : σ → ℝ≥0∞) :
    wp⟦(x :: xs).foldlM f init⟧ post =
      wp⟦f init x⟧
        (fun s => wp⟦xs.foldlM f s⟧ post) := by
  rw [List.foldlM_cons, MeasureProgramLogic.wp_bind]

/-- `wp` is monotone in the postcondition; `gcongr` descends through it. -/
@[gcongr low]
theorem wp_mono (oa : OracleComp spec α) {post post' : α → ℝ≥0∞}
    (hpost : ∀ x, post x ≤ post' x) :
    wp⟦oa⟧ post ≤ wp⟦oa⟧ post' :=
  MeasureProgramLogic.wp_mono oa hpost

/-- Finite postconditions over a finite result type have finite weakest precondition. -/
@[aesop (rule_sets := [finiteness]) safe apply]
theorem wp_ne_top_of_finite [Finite α] (oa : OracleComp spec α) {post : α → ℝ≥0∞}
    (hpost : ∀ x, post x ≠ ⊤) : wp⟦oa⟧ post ≠ ⊤ := by
  let c := ⨆ x, post x
  have hc : c ≠ ⊤ := iSup_ne_top hpost
  exact ne_top_of_le_ne_top hc
    (MeasureProgramLogic.wp_le_const_of_support oa fun x _ ↦ le_iSup post x)

/-- A support-wise postcondition bound controls the quantitative WP. -/
theorem wp_le_const_of_support (oa : OracleComp spec α) {post : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hpost : ∀ x ∈ support oa, post x ≤ c) : wp⟦oa⟧ post ≤ c :=
  (wp_mono_of_support oa hpost).trans_eq (MeasureProgramLogic.wp_const_of_oracle oa c)

/-- Additive support-wise comparison of quantitative postconditions. -/
theorem wp_le_const_add_of_support (oa : OracleComp spec α) {f g : α → ℝ≥0∞}
    {c : ℝ≥0∞} (hfg : ∀ x ∈ support oa, f x ≤ c + g x) :
    wp⟦oa⟧ f ≤ c + wp⟦oa⟧ g := by
  refine (wp_mono_of_support oa hfg).trans_eq ?_
  rw [MeasureProgramLogic.wp_add]
  exact congrArg (· + wp⟦oa⟧ g) (MeasureProgramLogic.wp_const_of_oracle oa c)

/-- Finite sums of quantitative postconditions commute with expectation. -/
theorem wp_finsetSum {κ : Type*} (oa : OracleComp spec α) (s : Finset κ)
    (f : κ → α → ℝ≥0∞) :
    wp⟦oa⟧ (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, wp⟦oa⟧ (f i) :=
  MeasureProgramLogic.wp_finsetSum oa s f

/-! ## Triple lemmas

Core's `Std.WP.Triple` is a structure around `pre ⊑ wp …`: `Std.WP.Triple.intro` builds a
triple from the inequality, `Std.WP.Triple.le_wp` extracts it, and `Std.WP.Triple.iff`
exchanges the two forms. Core supplies the generic rules (`Std.WP.Spec.pure`,
`Std.WP.Triple.bind`, `Std.WP.Triple.map`, `Std.WP.Triple.entails_wp_of_pre_post`) and `vcgen`
splits conditionals; the rules below are the quantitative ones for `OracleComp`, stated with
`ℝ≥0∞` inequalities. -/

/-- A quantitative triple with precondition `0` is always true. -/
theorem triple_zero (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    ⦃ (0 : ℝ≥0∞) ⦄ oa ⦃ post ⦄ :=
  ⟨bot_le⟩

open scoped Classical in
/-- An observed event probability is WP of its indicator assertion. -/
lemma prEvent_eq_wp_indicator (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] :
    Pr{let x ← oa}[p x] = wp⟦oa⟧ (fun x ↦ if p x then 1 else 0) := by
  change wp⟦oa⟧ (fun x ↦ propInd (p x)) = _
  simp only [propInd_eq_ite]

/-- An event probability is by definition the expectation of its indicator. -/
lemma prEvent_eq_wp_propInd {ι : Type u} {spec : OracleSpec ι}
    [OracleSpec.IsMeasureSpec spec] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← oa}[p x] = wp⟦oa⟧ (fun x => propInd (p x)) := rfl

open scoped Classical in
/-- Finite-response computations integrate assertions by a finite partition of reachable outputs.
The output labels need no measurable-space instance. -/
theorem wp_eq_sum_finSupport [∀ t, Fintype (spec.Range t)] [DecidableEq α] (oa : OracleComp spec α)
    (post : α → ℝ≥0∞) :
    wp⟦oa⟧ post = ∑ x ∈ finSupport oa, Pr{let y ← oa}[y = x] * post x := by
  classical
  calc
    _ = wp⟦oa⟧ (fun y ↦ ∑ x ∈ finSupport oa, if y = x then post x else 0) := by
      apply wp_congr_of_support
      intro y hy
      simp [Finset.sum_ite_eq, mem_finSupport_iff_mem_support, hy]
    _ = ∑ x ∈ finSupport oa, wp⟦oa⟧ (fun y ↦ if y = x then post x else 0) :=
      wp_finsetSum oa _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [prEvent_eq_wp_indicator, ← MeasureProgramLogic.wp_mul_const]
      congr 1
      funext y
      split_ifs <;> simp

open scoped Classical in
/-- The finite reachable-output partition extends to an event-weighted sum. -/
theorem wp_eq_tsum [∀ t, Finite (spec.Range t)] (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦oa⟧ post = ∑' x, Pr{let y ← oa}[y = x] * post x := by
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
    wp⟦(query t : OracleComp spec (spec.Range t))⟧ post =
      ∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t := by
  let : MeasurableSpace (spec.Range t) := ⊤
  rw [wp_eq_lintegral _ _ Measurable.of_discrete, evalDist_liftM_query, trim_eq_self]

/-- Lifting a primitive query has the same expectation rule. -/
theorem wp_liftM_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp⟦(liftM (query t) : OracleComp spec (spec.Range t))⟧ post =
      ∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t := by
  let : MeasurableSpace (spec.Range t) := ⊤
  rw [wp_eq_lintegral _ _ Measurable.of_discrete, evalDist_liftM_query, trim_eq_self]

/-- The ergonomic query interface integrates the configured answer measure. -/
@[game_rule] theorem wp_HasQuery_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp⟦(HasQuery.query t : OracleComp spec (spec.Range t))⟧ post =
      ∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t := wp_query t post

end MeasureSpec

section Uniform

/-- A uniform query's expectation is its finite average. -/
theorem wp_query_uniform [OracleSpec.IsUniformMeasureSpec spec]
    (t : spec.Domain) [Fintype (spec.Range t)] (post : spec.Range t → ℝ≥0∞) :
    wp⟦(query t : OracleComp spec (spec.Range t))⟧ post =
      ∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * post u := by
  let : MeasurableSpace (spec.Range t) := ⊤
  rw [wp_query, OracleSpec.IsMeasureSpec.toMeasure_eq_uniformOn]
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_comm]
  congr 1
  simp [ProbabilityTheory.uniformOn_univ]

end Uniform

section MeasureSpec

variable [OracleSpec.IsMeasureSpec spec]

/-- Uniform sampling integrates its chosen measure. -/
@[game_rule] theorem wp_uniformSample [SampleableType α] (post : α → ℝ≥0∞) :
    wp⟦$ᵗ α⟧ post = ∫⁻ y, y ∂𝒟[post <$> ($ᵗ α : ProbComp α)] :=
  wp_eq_lintegral_map _ _

attribute [expect_eval] OracleComp.replicate_zero OracleComp.replicate_succ_bind
  List.mapM_nil List.mapM_cons List.foldlM_nil List.foldlM_cons
  wp_query wp_liftM_query wp_HasQuery_query wp_uniformSample le_refl Function.comp_def

/-- Indicator-event probability as an exact quantitative triple. -/
theorem triple_prEvent_indicator (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    ⦃ Pr{let x ← oa}[p x] ⦄ oa ⦃ fun x => if p x then 1 else 0 ⦄ :=
  ⟨(prEvent_eq_wp_indicator oa p).le⟩

/-- Lower bounds on an event probability are exactly indicator-postcondition triples. -/
theorem le_prEvent_iff_triple_indicator (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] (r : ℝ≥0∞) :
    r ≤ Pr{let x ← oa}[p x] ↔ ⦃ r ⦄ oa ⦃ fun x => if p x then 1 else 0 ⦄ := by
  rw [Std.WP.Triple.iff, ← prEvent_eq_wp_indicator]
  exact Iff.rfl

/-- The support event of an `OracleComp` occurs almost surely. -/
theorem prEvent_mem_support (oa : OracleComp spec α) :
    Pr{let x ← oa}[x ∈ support oa] = 1 := by
  rw [prEvent_congr_of_support oa _ (fun _ ↦ True) (fun _ hx ↦ by simp only [hx]),
    prEvent_eq_evalDist_map]
  simp

/-- Exact probability-1 events are exact quantitative triples. -/
theorem triple_prEvent_eq_one (oa : OracleComp spec α) (p : α → Prop)
    [DecidablePred p] (h : Pr{let x ← oa}[p x] = 1) :
    ⦃ (1 : ℝ≥0∞) ⦄ oa ⦃ fun x => if p x then 1 else 0 ⦄ := by
  have := triple_prEvent_indicator (oa := oa) p
  rwa [h] at this

/-- Support membership is a useful default cut function for support-sensitive bind proofs. -/
theorem triple_support (oa : OracleComp spec α) [DecidablePred fun x => x ∈ support oa] :
    ⦃ (1 : ℝ≥0∞) ⦄ oa ⦃ fun x => if x ∈ support oa then 1 else 0 ⦄ := by
  simpa using
    triple_prEvent_eq_one (oa := oa) (p := fun x => x ∈ support oa)
      (h := prEvent_mem_support (oa := oa))

/-! ## Loop stepping rules -/

/-- Unroll one iteration of `replicate`, cutting at the expectation of the remaining ones. -/
theorem triple_replicate_succ {pre : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    {post : List α → ℝ≥0∞}
    (h : ⦃ pre ⦄ oa ⦃ fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs)) ⦄) :
    ⦃ pre ⦄ oa.replicate (n + 1) ⦃ post ⦄ :=
  ⟨by rw [wp_replicate_succ]; exact h.le_wp⟩

/-- Unroll the head of a `List.mapM`, cutting at the expectation of the tail. -/
theorem triple_list_mapM_cons {pre : ℝ≥0∞} {x : α} {xs : List α}
    {f : α → OracleComp spec β} {post : List β → ℝ≥0∞}
    (h : ⦃ pre ⦄ f x ⦃ fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys)) ⦄) :
    ⦃ pre ⦄ (x :: xs).mapM f ⦃ post ⦄ :=
  ⟨by rw [wp_list_mapM_cons]; exact h.le_wp⟩

/-- Unroll the head of a `List.foldlM`, cutting at the expectation of the tail. -/
theorem triple_list_foldlM_cons {pre : ℝ≥0∞} {x : α} {xs : List α}
    {f : σ → α → OracleComp spec σ} {init : σ} {post : σ → ℝ≥0∞}
    (h : ⦃ pre ⦄ f init x ⦃ fun s => wp⟦xs.foldlM f s⟧ post ⦄) :
    ⦃ pre ⦄ (x :: xs).foldlM f init ⦃ post ⦄ :=
  ⟨by rw [wp_list_foldlM_cons]; exact h.le_wp⟩

/-! ## Loop invariant rules -/

/-- Constant invariant through bounded iteration via `replicate`. -/
theorem triple_replicate_inv {I : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    (hstep : ⦃ I ⦄ oa ⦃ fun _ => I ⦄) :
    ⦃ I ⦄ oa.replicate n ⦃ fun _ => I ⦄ := by
  induction n with
  | zero => exact Spec.pure (post := fun _ => I) []
  | succ n ih =>
      rw [OracleComp.replicate_succ_bind]
      exact Triple.bind _ _ _ hstep fun x => Triple.bind _ _ _ ih fun xs =>
        Spec.pure (post := fun _ => I) (x :: xs)

/-- Indexed invariant through `List.foldlM`. -/
theorem triple_list_foldlM_inv {I : σ → ℝ≥0∞}
    {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    (hstep : ∀ s x, x ∈ l → ⦃ I s ⦄ f s x ⦃ I ⦄) :
    ⦃ I s₀ ⦄ l.foldlM f s₀ ⦃ I ⦄ := by
  induction l generalizing s₀ with
  | nil => exact Spec.pure (post := I) s₀
  | cons a as ih =>
      rw [List.foldlM_cons]
      exact Triple.bind _ _ _ (hstep s₀ a (by simp)) fun s =>
        ih fun s x hx => hstep s x (by simp [hx])

/-- Constant invariant through `List.mapM`. -/
theorem triple_list_mapM_inv {I : ℝ≥0∞}
    {f : α → OracleComp spec β} {l : List α}
    (hstep : ∀ x, x ∈ l → ⦃ I ⦄ f x ⦃ fun _ => I ⦄) :
    ⦃ I ⦄ l.mapM f ⦃ fun _ => I ⦄ := by
  induction l with
  | nil => exact Spec.pure (post := fun _ => I) ([] : List β)
  | cons a as ih =>
      rw [List.mapM_cons]
      exact Triple.bind _ _ _ (hstep a (by simp)) fun y =>
        Triple.bind _ _ _ (ih fun x hx => hstep x (by simp [hx])) fun ys =>
          Spec.pure (post := fun _ => I) (y :: ys)

/-- `replicate` invariant with consequence: bridges arbitrary pre/post to the invariant. -/
theorem triple_replicate {I pre : ℝ≥0∞} {oa : OracleComp spec α} {n : ℕ}
    {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : ⦃ I ⦄ oa ⦃ fun _ => I ⦄) :
    ⦃ pre ⦄ oa.replicate n ⦃ post ⦄ :=
  ⟨Std.WP.Triple.entails_wp_of_pre_post (triple_replicate_inv hstep) hpre hpost⟩

/-- `List.foldlM` invariant with consequence. -/
theorem triple_list_foldlM {I : σ → ℝ≥0∞}
    {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    {pre : ℝ≥0∞} {post : σ → ℝ≥0∞}
    (hpre : pre ≤ I s₀) (hpost : ∀ s, I s ≤ post s)
    (hstep : ∀ s x, x ∈ l → ⦃ I s ⦄ f s x ⦃ I ⦄) :
    ⦃ pre ⦄ l.foldlM f s₀ ⦃ post ⦄ :=
  ⟨Std.WP.Triple.entails_wp_of_pre_post (triple_list_foldlM_inv hstep) hpre hpost⟩

/-- `List.mapM` invariant with consequence. -/
theorem triple_list_mapM {I : ℝ≥0∞}
    {f : α → OracleComp spec β} {l : List α}
    {pre : ℝ≥0∞} {post : List β → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ ys, I ≤ post ys)
    (hstep : ∀ x, x ∈ l → ⦃ I ⦄ f x ⦃ fun _ => I ⦄) :
    ⦃ pre ⦄ l.mapM f ⦃ post ⦄ :=
  ⟨Std.WP.Triple.entails_wp_of_pre_post (triple_list_mapM_inv hstep) hpre hpost⟩

/-! ## Congruence of observations -/

/-- The expectation algebra evaluates the identity assertion. -/
lemma μ_eq_wp (oa : OracleComp spec ℝ≥0∞) : μ oa = wp⟦oa⟧ (fun x ↦ x) := by
  change MAlgOrdered.μ oa = MAlgOrdered.μ (oa >>= fun x ↦ pure x)
  rw [bind_pure]

/-- Equal assertion-valued observations have equal quantitative WP. -/
lemma wp_congr_evalDist_map {oa ob : OracleComp spec α} (post : α → ℝ≥0∞)
    (h : 𝒟[post <$> oa] = 𝒟[post <$> ob]) : wp⟦oa⟧ post = wp⟦ob⟧ post := by
  rw [wp_eq_lintegral_map, wp_eq_lintegral_map, h]

/-- Equal chosen output measures give equal expectations of measurable assertions. -/
lemma wp_congr_evalDist [MeasurableSpace α] {oa ob : OracleComp spec α}
    (h : 𝒟[oa] = 𝒟[ob]) (post : α → ℝ≥0∞) (hpost : Measurable post) :
    wp⟦oa⟧ post = wp⟦ob⟧ post := by
  rw [wp_eq_lintegral oa post hpost, wp_eq_lintegral ob post hpost, h]

end MeasureSpec

end OracleComp.ProgramLogic
