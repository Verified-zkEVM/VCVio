/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Relational.QuantitativeDefs
public import VCVio.ProgramLogic.Unary.HoareTriple
public import ToMathlib.MeasureTheory.Measure.Coupling.Maximal
import ToMathlib.MeasureTheory.Function.AEMeasurable
import ToMathlib.MeasureTheory.Integral.Countable

/-!
# Quantitative Relational Program Logic (eRHL)

This file develops the main theorem layer for the eRHL-style quantitative relational
logic for `OracleComp`, building on the core interfaces in
`VCVio.ProgramLogic.Relational.QuantitativeDefs`.

The core idea (from Avanzini-Barthe-Gregoire-Davoli, POPL 2025) is to make pre/postconditions
`ℝ≥0∞`-valued instead of `Prop`-valued. This subsumes both pRHL (exact coupling, via indicator
postconditions) and apRHL (ε-approximate coupling, via threshold preconditions).

Output measures of oracle computations with finite response types concentrate on finite
structural supports, so coupled expectations are finite sums; this supplies the exchange of the
coupling supremum with the sum behind the bind rule.

## Main results in this file

- introduction, consequence, and bind rules for eRHL
- the quantitative relational algebra and its anchoring to unary expectations
- total variation as the complement of the best coupled probability of equal outputs
- witness lower bounds for uniform samples and oracle queries under a bijection

## Design

```
                eRHL (ℝ≥0∞-valued pre/post)
               /          |           \
              /           |            \
pRHL (exact)    apRHL (ε-approx)   stat-distance
indicator R      1-ε, indicator R    1, indicator(=)
```
-/

@[expose] public section

open ENNReal OracleSpec OracleComp MeasureTheory ProbabilityTheory

universe u v

open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic.Relational

private lemma Finset_sum_iSup_le_iSup_sum {ι : Type*} {J : ι → Type*}
    [hne : ∀ i, Nonempty (J i)]
    (g : (i : ι) → J i → ℝ≥0∞) (s : Finset ι) :
    ∑ i ∈ s, ⨆ j, g i j ≤ ⨆ (f : ∀ i, J i), ∑ i ∈ s, g i (f i) := by
  let : DecidableEq ι := Classical.decEq ι
  have : Nonempty (∀ i, J i) := ⟨fun i => (hne i).some⟩
  refine Finset.induction_on s (by simp) fun a s ha ih => ?_
  simp_rw [Finset.sum_insert ha]
  calc (⨆ j, g a j) + ∑ i ∈ s, ⨆ j, g i j
      ≤ (⨆ j, g a j) + ⨆ (f : ∀ i, J i), ∑ i ∈ s, g i (f i) :=
        add_le_add le_rfl ih
    _ = ⨆ j, ⨆ (f : ∀ i, J i), (g a j + ∑ i ∈ s, g i (f i)) := by
        rw [ENNReal.iSup_add]; congr 1; ext j; rw [ENNReal.add_iSup]
    _ ≤ ⨆ (f : ∀ i, J i), (g a (f a) + ∑ i ∈ s, g i (f i)) := by
        refine iSup_le fun j => iSup_le fun f => ?_
        refine le_iSup_of_le (Function.update f a j) (le_of_eq ?_)
        rw [Function.update_self]
        exact congrArg _ <| Finset.sum_congr rfl fun i hi => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]

private lemma ENNReal_tsum_iSup_le {ι : Type*} {J : ι → Type*}
    [∀ i, Nonempty (J i)] (g : (i : ι) → J i → ℝ≥0∞) :
    ∑' i, ⨆ j, g i j ≤ ⨆ (f : ∀ i, J i), ∑' i, g i (f i) := by
  let : DecidableEq ι := Classical.decEq ι
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => le_trans (Finset_sum_iSup_le_iSup_sum g s) ?_
  exact iSup_mono fun f => ENNReal.sum_le_tsum _

variable {ι₁ : Type u} {ι₂ : Type u}
variable {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{u, 0} ι₂}
variable {α β γ δ : Type}

section measureSpec

variable [IsMeasureSpec spec₁] [IsMeasureSpec spec₂]

/-! ## Quantitative relational WP rules -/

/-- Quantitative relational weakest precondition is monotone in the postcondition. -/
theorem eRelWP_mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {post post' : α → β → ℝ≥0∞}
    (hpost : ∀ a b, post a b ≤ post' a b) :
    eRelWP oa ob post ≤ eRelWP oa ob post' := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact MeasureProgramLogic.eRelWP_mono oa ob hpost

/-- Monotonicity/consequence rule for quantitative relational WP. -/
theorem eRelWP_conseq {pre pre' : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {post post' : α → β → ℝ≥0∞}
    (hpre : pre' ≤ pre) (hpost : ∀ a b, post a b ≤ post' a b)
    (h : pre ≤ eRelWP oa ob post) :
    pre' ≤ eRelWP oa ob post' :=
  hpre.trans (h.trans (eRelWP_mono hpost))

/-- A coupling of output measures witnesses a lower bound on the quantitative relational WP. -/
theorem le_eRelWP_of_isCoupling {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (post : α → β → ℝ≥0∞)
    (c : letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤;
      Measure.Coupling 𝒟[oa] 𝒟[ob]) :
    letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤;
      ∫⁻ z, post z.1 z.2 ∂c.joint ≤ eRelWP oa ob post := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact MeasureProgramLogic.le_eRelWP_of_isCoupling oa ob post c

/-- Coupled expectations are bounded by any pointwise bound on the postcondition. -/
theorem eRelWP_le (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (post : α → β → ℝ≥0∞) (bound : ℝ≥0∞) (h : ∀ a b, post a b ≤ bound) :
    eRelWP oa ob post ≤ bound := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact MeasureProgramLogic.eRelWP_le oa ob post bound h

/-- An indicator postcondition has coupled expectation at most one. -/
theorem eRelWP_indicator_le_one (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : eRelWP oa ob (RelPost.indicator R) ≤ 1 :=
  eRelWP_le oa ob _ 1 fun a b => by
    unfold RelPost.indicator
    split_ifs <;> simp

/-- Pure values characterize the quantitative relational weakest precondition. -/
theorem eRelWP_pure (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    eRelWP (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) post = post a b := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact MeasureProgramLogic.eRelWP_pure_pure a b post

/-- Pure rule for quantitative relational WP. -/
theorem eRelWP_pure_le (a : α) (b : β) (post : α → β → ℝ≥0∞) :
    post a b ≤ eRelWP (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) post :=
  (eRelWP_pure a b post).ge

section finite

variable [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]

/-- Quantitative relational weakest preconditions compose through bind. A coupling of the first
two computations concentrates on the finite product of their supports, so its coupled
expectation is a finite sum, and a choice of conditional couplings on that support gives a
coupling of the two binds. -/
theorem eRelWP_bind_le
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (fa : α → OracleComp spec₁ γ) (fb : β → OracleComp spec₂ δ)
    (post : γ → δ → ℝ≥0∞) :
    eRelWP oa ob (fun a b => eRelWP (fa a) (fb b) post) ≤
      eRelWP (oa >>= fa) (ob >>= fb) post := by
  classical
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace γ := ⊤
  let : MeasurableSpace δ := ⊤
  refine iSup_le fun c => ?_
  let S : Set (α × β) := support oa ×ˢ support ob
  have hS : S.Countable :=
    ((PFunctor.FreeM.support_finite oa).prod (PFunctor.FreeM.support_finite ob)).countable
  have hcS : ∀ᵐ z ∂c.joint, z ∈ S := ae_mem_support_prod c
  have hne (z : S) : Nonempty (Measure.Coupling 𝒟[fa z.1.1] 𝒟[fb z.1.2]) := by
    have : IsProbabilityMeasure 𝒟[fa z.1.1] := ⟨evalDist_apply_univ_eq_one _⟩
    have : IsProbabilityMeasure 𝒟[fb z.1.2] := ⟨evalDist_apply_univ_eq_one _⟩
    exact ⟨Measure.Coupling.prod _ _⟩
  change ∫⁻ z, eRelWP (fa z.1) (fb z.2) post ∂c.joint ≤ _
  rw [lintegral_eq_tsum_of_ae_mem_countable hS hcS]
  calc ∑' z : S, eRelWP (fa z.1.1) (fb z.1.2) post * c.joint {(z : α × β)}
      = ∑' z : S, ⨆ d : Measure.Coupling 𝒟[fa z.1.1] 𝒟[fb z.1.2],
          (∫⁻ w, post w.1 w.2 ∂d.joint) * c.joint {(z : α × β)} :=
        tsum_congr fun z => ENNReal.iSup_mul ..
    _ ≤ ⨆ D : ∀ z : S, Measure.Coupling 𝒟[fa z.1.1] 𝒟[fb z.1.2],
          ∑' z : S, (∫⁻ w, post w.1 w.2 ∂(D z).joint) * c.joint {(z : α × β)} :=
        ENNReal_tsum_iSup_le _
    _ ≤ eRelWP (oa >>= fa) (ob >>= fb) post := iSup_le fun D => ?_
  let j : α × β → Measure (γ × δ) := fun z =>
    if hz : z ∈ S then (D ⟨z, hz⟩).joint else 0
  have hj : AEMeasurable j c.joint := aemeasurable_of_ae_mem_countable hS hcS j
  have hstep : ∀ᵐ z ∂c.joint, Measure.IsCoupling (j z) 𝒟[fa z.1] 𝒟[fb z.2] :=
    hcS.mono fun z hz => by simpa only [j, dite_eq_left hz] using (D ⟨z, hz⟩).isCoupling
  have hjoint : Measure.IsCoupling (c.joint.bind j) 𝒟[oa >>= fa] 𝒟[ob >>= fb] := by
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    exact c.isCoupling.bind_of_aemeasurable Measurable.of_discrete Measurable.of_discrete hj hstep
  let C : Measure.Coupling 𝒟[oa >>= fa] 𝒟[ob >>= fb] := ⟨c.joint.bind j, hjoint⟩
  have hpost : AEMeasurable (fun w : γ × δ => post w.1 w.2) (c.joint.bind j) :=
    aemeasurable_of_ae_mem_countable
      ((PFunctor.FreeM.support_finite (oa >>= fa)).prod
        (PFunctor.FreeM.support_finite (ob >>= fb))).countable
      (ae_mem_support_prod C) _
  refine le_trans (le_of_eq ?_) (le_eRelWP_of_isCoupling post C)
  change _ = ∫⁻ w, post w.1 w.2 ∂(c.joint.bind j)
  rw [Measure.lintegral_bind hj hpost, lintegral_eq_tsum_of_ae_mem_countable hS hcS]
  exact tsum_congr fun z => by simp only [j, dite_eq_left z.2]

/-- Bind/sequential composition rule for quantitative relational WP. -/
theorem eRelWP_bind_rule
    {pre : ℝ≥0∞}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ}
    {cut : α → β → ℝ≥0∞} {post : γ → δ → ℝ≥0∞}
    (hxy : pre ≤ eRelWP oa ob cut)
    (hfg : ∀ a b, cut a b ≤ eRelWP (fa a) (fb b) post) :
    pre ≤ eRelWP (oa >>= fa) (ob >>= fb) post :=
  (eRelWP_conseq le_rfl hfg hxy).trans (eRelWP_bind_le oa ob fa fb post)

/-! ## Statistical distance via eRHL

Output measures of oracle computations concentrate on their finite supports, where the best
coupled probability of equal outputs is the overlap of the two measures, attained by their
maximal coupling. -/

/-- Total variation between two output measures is the complement of the best coupled
probability of equal outputs. -/
theorem etvDist_eq_one_sub_eRelWP_eqRel (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ α) :
    (letI : MeasurableSpace α := ⊤; 𝒟[oa].etvDist 𝒟[ob]) =
      1 - eRelWP oa ob (RelPost.indicator (EqRel α)) := by
  classical
  let : MeasurableSpace α := ⊤
  let F : Finset α := (PFunctor.FreeM.support_finite oa).toFinset ∪
    (PFunctor.FreeM.support_finite ob).toFinset
  have hμ : 𝒟[oa] (↑F)ᶜ = 0 := by
    have hs := ae_mem_support oa
    rw [ae_iff] at hs
    refine measure_mono_null (t := {a | a ∉ support oa}) (fun x hx hxs => hx ?_) hs
    simp [F, hxs]
  have hν : 𝒟[ob] (↑F)ᶜ = 0 := by
    have hs := ae_mem_support ob
    rw [ae_iff] at hs
    refine measure_mono_null (t := {a | a ∉ support ob}) (fun x hx hxs => hx ?_) hs
    simp [F, hxs]
  have : IsProbabilityMeasure 𝒟[oa] := ⟨evalDist_apply_univ_eq_one oa⟩
  have : IsProbabilityMeasure 𝒟[ob] := ⟨evalDist_apply_univ_eq_one ob⟩
  have hdiag (c : Measure.Coupling 𝒟[oa] 𝒟[ob]) :
      ∫⁻ z, RelPost.indicator (EqRel α) z.1 z.2 ∂c.joint = ∑ a ∈ F, c.joint {(a, a)} := by
    have hc : c.joint (↑(F ×ˢ F))ᶜ = 0 := by
      rw [Finset.coe_product]
      exact ae_iff.1 (c.isCoupling.ae_mem_prod F.measurableSet F.measurableSet
        (measure_eq_zero_iff_ae_notMem.1 hμ |>.mono fun _ h => not_not.1 h)
        (measure_eq_zero_iff_ae_notMem.1 hν |>.mono fun _ h => not_not.1 h))
    rw [Measure.lintegral_eq_sum_of_compl_eq_zero hc, Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_eq_single a (fun b _ hba => by simp [RelPost.indicator, EqRel, Ne.symm hba])
      (fun h => absurd ha h)]
    simp [RelPost.indicator, EqRel]
  have hw : eRelWP oa ob (RelPost.indicator (EqRel α)) =
      ∑ a ∈ F, min (𝒟[oa] {a}) (𝒟[ob] {a}) := by
    apply le_antisymm
    · refine iSup_le fun c => ?_
      rw [hdiag c]
      exact Finset.sum_le_sum fun a _ => c.isCoupling.apply_diag_le a
    · refine le_trans ?_ (le_eRelWP_of_isCoupling _ ⟨_, Measure.isCoupling_maximalCoupling hμ hν⟩)
      rw [hdiag]
      exact Finset.sum_le_sum fun a ha => Measure.min_le_maximalCoupling_apply_diag ha
  rw [hw, Measure.etvDist_eq_one_sub_sum_min hμ hν]

/-- An approximate equality coupling with error `ε` is exactly a total variation bound `ε`
between the two output measures. -/
theorem approxRelTriple_eqRel_iff_etvDist_le {oa : OracleComp spec₁ α}
    {ob : OracleComp spec₂ α} {ε : ℝ≥0∞} :
    ApproxRelTriple ε oa ob (EqRel α) ↔
      (letI : MeasurableSpace α := ⊤; 𝒟[oa].etvDist 𝒟[ob]) ≤ ε := by
  rw [ApproxRelTriple, etvDist_eq_one_sub_eRelWP_eqRel]
  exact tsub_le_iff_tsub_le

/-- Computations with a zero-error approximate equality coupling are equal in distribution. -/
theorem evalDistEq_of_approxRelTriple_zero {oa : OracleComp spec₁ α}
    {ob : OracleComp spec₂ α} (h : ApproxRelTriple 0 oa ob (EqRel α)) : oa =ᵈ ob := by
  let : MeasurableSpace α := ⊤
  exact EvalDistEq.of_evalDist_eq (Measure.etvDist_eq_zero_iff.1 (nonpos_iff_eq_zero.1
    (approxRelTriple_eqRel_iff_etvDist_le.1 h)))

/-! ## Relational algebra instance -/

/-- Quantitative relational algebra instance for `OracleComp`, based on `eRelWP`. -/
noncomputable instance instMAlgRelOrdered_eRelWP :
    MAlgRelOrdered (OracleComp spec₁) (OracleComp spec₂) ℝ≥0∞ where
  rwp := fun oa ob post => eRelWP oa ob post
  rwp_pure := fun a b post => eRelWP_pure a b post
  rwp_mono := fun hpost => eRelWP_mono hpost
  rwp_bind_le := fun oa ob fa fb post => eRelWP_bind_le oa ob fa fb post

end finite

/-- Every coupling of a Dirac law with the output measure of `y` integrates a postcondition as
the unary expectation of its section at the Dirac point. -/
private theorem lintegral_coupling_pure_left (a : α) (y : OracleComp spec₂ β)
    (post : α → β → ℝ≥0∞)
    (c : letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤;
      Measure.Coupling 𝒟[(pure a : OracleComp spec₁ α)] 𝒟[y]) :
    letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤;
      ∫⁻ z, post z.1 z.2 ∂c.joint = wp y (post a) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have hmeas : MeasurableSet {x : α | x = a} := measurableSet_singleton a
  have hfst : ∀ᵐ z ∂c.joint, z.1 = a := by
    refine (ae_map_iff measurable_fst.aemeasurable hmeas).1 ?_
    rw [show c.joint.map Prod.fst = 𝒟[(pure a : OracleComp spec₁ α)] from c.isCoupling.fst_eq,
      evalDist_pure]
    exact (ae_dirac_iff hmeas).2 rfl
  calc ∫⁻ z, post z.1 z.2 ∂c.joint = ∫⁻ z, post a z.2 ∂c.joint :=
        lintegral_congr_ae (hfst.mono fun z hz => by simp only [hz])
    _ = ∫⁻ b, post a b ∂c.joint.map Prod.snd :=
        (lintegral_map Measurable.of_discrete measurable_snd).symm
    _ = wp y (post a) := by
        rw [show c.joint.map Prod.snd = 𝒟[y] from c.isCoupling.snd_eq,
          wp_eq_lintegral y (post a) Measurable.of_discrete]

/-- A pure first computation collapses the coupled expectation to the unary expectation of the
second computation. -/
theorem eRelWP_pure_left (a : α) (y : OracleComp spec₂ β) (post : α → β → ℝ≥0∞) :
    eRelWP (pure a : OracleComp spec₁ α) y post = wp y (post a) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have : IsProbabilityMeasure 𝒟[y] := ⟨evalDist_apply_univ_eq_one y⟩
  have : Nonempty (Measure.Coupling 𝒟[(pure a : OracleComp spec₁ α)] 𝒟[y]) :=
    ⟨Measure.Coupling.prod _ _⟩
  change (⨆ c : Measure.Coupling 𝒟[(pure a : OracleComp spec₁ α)] 𝒟[y],
    ∫⁻ z, post z.1 z.2 ∂c.joint) = _
  simp only [lintegral_coupling_pure_left a y post, iSup_const]

/-- A pure second computation collapses the coupled expectation to the unary expectation of the
first computation. -/
theorem eRelWP_pure_right (x : OracleComp spec₁ α) (b : β) (post : α → β → ℝ≥0∞) :
    eRelWP x (pure b : OracleComp spec₂ β) post = wp x (fun a => post a b) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have : IsProbabilityMeasure 𝒟[x] := ⟨evalDist_apply_univ_eq_one x⟩
  rw [← eRelWP_pure_left (spec₁ := spec₂) b x fun b a => post a b]
  change (⨆ c : Measure.Coupling 𝒟[x] 𝒟[(pure b : OracleComp spec₂ β)],
      ∫⁻ z, post z.1 z.2 ∂c.joint) =
    ⨆ c : Measure.Coupling 𝒟[(pure b : OracleComp spec₂ β)] 𝒟[x], ∫⁻ z, post z.2 z.1 ∂c.joint
  refine le_antisymm (iSup_le fun c => le_iSup_of_le c.swap (le_of_eq ?_))
    (iSup_le fun c => le_iSup_of_le c.swap (le_of_eq ?_))
  · change _ = ∫⁻ z, post z.2 z.1 ∂(c.joint.map (MeasurableEquiv.prodComm (α := α) (β := β)))
    rw [lintegral_map_equiv]
    rfl
  · change _ = ∫⁻ z, post z.1 z.2 ∂(c.joint.map (MeasurableEquiv.prodComm (α := β) (β := α)))
    rw [lintegral_map_equiv]
    rfl

/-- Anchoring instance for the quantitative `ℝ≥0∞`-valued relational logic on `OracleComp`.

When one of the two computations is `pure`, every coupling has that computation's value as its
coordinate almost surely, so the relational expectation reduces to the unary expectation
`wp y (post a)` (resp. `wp x (fun a => post a b)`). This is the quantitative analogue of the
qualitative `Anchored Prop` instance in `VCVio/ProgramLogic/Relational/Basic.lean`. -/
noncomputable instance instAnchored_eRelWP
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)] :
    @MAlgRelOrdered.Anchored (OracleComp spec₁) (OracleComp spec₂) ℝ≥0∞ _ _ _
      OracleComp.Quantitative.instWP OracleComp.Quantitative.instWP _ :=
  letI := OracleComp.Quantitative.instWP (spec := spec₁)
  letI := OracleComp.Quantitative.instWP (spec := spec₂)
  { rwp_pure_left := fun a y post => eRelWP_pure_left a y post
    rwp_pure_right := fun x b post => eRelWP_pure_right x b post }

section finite

variable [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]

noncomputable example :
    MAlgRelOrdered (OptionT (OracleComp spec₁)) (OracleComp spec₂) ℝ≥0∞ :=
  inferInstance

noncomputable example {ε : Type} :
    MAlgRelOrdered (ExceptT ε (OracleComp spec₁)) (OracleComp spec₂) ℝ≥0∞ :=
  inferInstance

noncomputable example {σ : Type} :
    MAlgRelOrdered (StateT σ (OracleComp spec₁)) (OracleComp spec₂) (σ → ℝ≥0∞) :=
  inferInstance

/-! ## Specialisations of the generic asynchronous and structural rules

The following examples confirm that the generic rules in
`ToMathlib/Control/Monad/RelationalAlgebra.lean` (asynchronous one-sided
binds and structural pure rules) automatically apply to `eRelWP`. They are
the quantitative counterparts of SSProve's `apply_left` / `apply_right` /
`if_rule` style rules.
-/

example {α β γ : Type}
    (oa : OracleComp spec₁ α) (fa : α → OracleComp spec₁ γ)
    (ob : OracleComp spec₂ β) (post : γ → β → ℝ≥0∞) :
    eRelWP oa ob (fun a b => eRelWP (fa a) (pure b : OracleComp spec₂ β) post)
      ≤ eRelWP (oa >>= fa) ob post :=
  MAlgRelOrdered.relWP_bind_left_le oa fa ob post

example {α β δ : Type}
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (fb : β → OracleComp spec₂ δ)
    (post : α → δ → ℝ≥0∞) :
    eRelWP oa ob (fun a b => eRelWP (pure a : OracleComp spec₁ α) (fb b) post)
      ≤ eRelWP oa (ob >>= fb) post :=
  MAlgRelOrdered.relWP_bind_right_le oa ob fb post

example {α β : Type}
    (b : Bool) (oa oa' : OracleComp spec₁ α) (ob ob' : OracleComp spec₂ β)
    (pre : ℝ≥0∞) (post : α → β → ℝ≥0∞)
    (h_t : b = true → MAlgRelOrdered.Triple pre oa ob post)
    (h_f : b = false → MAlgRelOrdered.Triple pre oa' ob' post) :
    MAlgRelOrdered.Triple pre
        (if b then oa else oa') (if b then ob else ob') post :=
  MAlgRelOrdered.triple_ite b h_t h_f

end finite

/-! ## Quantitative effect-specific rules (eRHL primitives)

Witness-based lower bounds for `eRelWP` on the basic `OracleComp` effect operations (uniform
sampling and oracle queries under a bijection): the graph of the bijection couples the operation
with itself, and its coupled expectation is the unary expectation along the bijection.
-/

/-! ### Uniform sampling under a bijection -/

section Sampling

variable [SampleableType α]

/-- Quantitative lower bound for two uniform samples coupled by a bijection. -/
theorem eRelWP_uniformSample_bij_ge
    {f : α → α} (hf : Function.Bijective f) (post : α → α → ℝ≥0∞) :
    wp ($ᵗ α : ProbComp α) (fun a => post a (f a))
      ≤ eRelWP ($ᵗ α : ProbComp α) ($ᵗ α : ProbComp α) post := by
  let : MeasurableSpace α := ⊤
  have hgraph : Measurable fun a : α => (a, f a) := Measurable.of_discrete
  refine le_trans (le_of_eq ?_)
    (le_eRelWP_of_isCoupling post ⟨_, isCoupling_uniformSample_graph hf⟩)
  rw [wp_eq_lintegral _ _ Measurable.of_discrete]
  change _ = ∫⁻ z, post z.1 z.2 ∂(𝒟[($ᵗ α : ProbComp α)].map fun a => (a, f a))
  rw [lintegral_map (measurable_of_countable fun z : α × α => post z.1 z.2) hgraph]

/-- Any precondition below the bijection average discharges the quantitative
relational WP lower-bound for two uniform samples. -/
theorem eRelWP_uniformSample_bij
    {f : α → α} (hf : Function.Bijective f) (post : α → α → ℝ≥0∞)
    {pre : ℝ≥0∞}
    (hpre : pre ≤ wp ($ᵗ α : ProbComp α) (fun a => post a (f a))) :
    pre ≤ eRelWP ($ᵗ α : ProbComp α) ($ᵗ α : ProbComp α) post :=
  hpre.trans (eRelWP_uniformSample_bij_ge hf post)

end Sampling

end measureSpec

/-! ### Oracle queries under a bijection -/

section oracleQuery

variable [IsUniformMeasureSpec spec₁]
  [∀ t, Finite (spec₁.Range t)]

/-- Quantitative lower bound for two oracle queries coupled by a bijection on the range.
This is the eRHL counterpart of `relTriple_query_bij`. -/
theorem eRelWP_query_bij_ge (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t}
    (hf : Function.Bijective f)
    (post : spec₁.Range t → spec₁.Range t → ℝ≥0∞) :
    wp (liftM (query t) : OracleComp spec₁ (spec₁.Range t)) (fun a => post a (f a))
      ≤ eRelWP (spec₁ := spec₁) (spec₂ := spec₁)
          (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
          (liftM (query t) : OracleComp spec₁ (spec₁.Range t)) post := by
  let : MeasurableSpace (spec₁.Range t) := ⊤
  have hgraph : Measurable fun a : spec₁.Range t => (a, f a) := Measurable.of_discrete
  refine le_trans (le_of_eq ?_)
    (le_eRelWP_of_isCoupling post ⟨_, isCoupling_query_graph t hf⟩)
  rw [wp_eq_lintegral _ _ Measurable.of_discrete]
  change _ = ∫⁻ z, post z.1 z.2 ∂(𝒟[(liftM (query t) : OracleComp spec₁ (spec₁.Range t))].map
    fun a => (a, f a))
  rw [lintegral_map (measurable_of_countable fun z : spec₁.Range t × spec₁.Range t =>
    post z.1 z.2) hgraph]

/-- Triple form of `eRelWP_query_bij_ge`. -/
theorem eRelWP_query_bij (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t}
    (hf : Function.Bijective f)
    (post : spec₁.Range t → spec₁.Range t → ℝ≥0∞)
    {pre : ℝ≥0∞}
    (hpre : pre ≤
      wp (liftM (query t) : OracleComp spec₁ (spec₁.Range t)) (fun a => post a (f a))) :
    pre ≤ eRelWP (spec₁ := spec₁) (spec₂ := spec₁)
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t)) post :=
  hpre.trans (eRelWP_query_bij_ge t hf post)

end oracleQuery

/-! ## Demonstration examples for the quantitative primitives

Small examples illustrating how the closed-form and lower-bound `eRelWP` rules combine in
practice.
-/

/-- Quantitative bound via `eRelWP_uniformSample_bij`: any precondition below the
bijection-shifted average is realised by the bijection coupling. -/
example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) (post : α → α → ℝ≥0∞) :
    wp ($ᵗ α : ProbComp α) (fun a => post a (f a))
      ≤ eRelWP ($ᵗ α : ProbComp α) ($ᵗ α : ProbComp α) post :=
  eRelWP_uniformSample_bij hf post le_rfl

end OracleComp.ProgramLogic.Relational
