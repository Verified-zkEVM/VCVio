/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import ToMathlib.Control.Monad.RelationalAlgebra
public import VCVio.ProgramLogic.Relational.Measure.Bind
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.Constructions.Replicate.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.ProgramLogic.Unary.HoarePropTriple

/-!
# Relational program-logic baseline

This file defines `RelTriple` via the generic two-monad algebra interface `MAlgRelOrdered`,
instantiated for `OracleComp` with measure coupling semantics: `CouplingPost oa ob R` asks for a
coupling of the two output measures, each observed in the discrete structure on its output type,
under which `R` holds almost everywhere.

Finite oracle response types make every output measure concentrate on the finite structural
support, which supplies the countable choice behind the sequential rule. The anchoring and
bijection rules additionally need uniform response measures, under which every structurally
reachable output has positive mass.
-/

@[expose] public section

universe u v w x

open MeasureTheory ProbabilityTheory
open scoped OracleSpec.PrimitiveQuery

namespace OracleComp.ProgramLogic.Relational

open OracleSpec MeasureProgramLogic

/-- Relational postconditions over two output spaces. -/
abbrev RelPost (α : Sort w) (β : Sort x) := α → β → Prop

/-- Equality relation helper for same-type outputs. -/
def EqRel (α : Sort w) : RelPost α α := Eq

/-- Almost-sure properties transport along a measurable map out of a measure concentrated on a
countable set, even when the property is not measurable in the target. -/
theorem ae_map_of_ae_mem_countable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] {μ : Measure X} {f : X → Y} (hf : Measurable f)
    {s : Set X} (hs : s.Countable) {p : Y → Prop} (h : ∀ᵐ x ∂μ, x ∈ s ∧ p (f x)) :
    ∀ᵐ y ∂μ.map f, p y := by
  have hT : MeasurableSet (f '' {x | x ∈ s ∧ p (f x)}) :=
    ((hs.mono fun _ hx ↦ hx.1).image f).measurableSet
  filter_upwards [(ae_map_iff hf.aemeasurable hT).2 (h.mono fun x hx ↦ ⟨x, hx, rfl⟩)] with y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hx.2

variable {ι₁ : Type u} {ι₂ : Type v}
variable {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{v, 0} ι₂}
variable [∀ t, MeasurableSpace (spec₁.Range t)] [∀ t, MeasurableSpace (spec₂.Range t)]
variable {α β γ δ : Type}

section measureSpec

variable [IsMeasureSpec spec₁] [IsMeasureSpec spec₂]

/-- Coupling-based semantic relational WP for `OracleComp`: some coupling of the two output
measures, each observed in the discrete structure on its output type, satisfies `R` almost
everywhere. -/
def CouplingPost (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) : Prop :=
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  MeasureProgramLogic.RelWP oa ob R

/-- Implication of postconditions preserves a coupling. -/
theorem CouplingPost.mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R S : RelPost α β} (h : CouplingPost oa ob R) (hRS : ∀ a b, R a b → S a b) :
    CouplingPost oa ob S := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact relWP_mono h hRS

variable [∀ t, DiscreteMeasurableSpace (spec₁.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec₂.Range t)]

/-- Pure computations are coupled exactly on the relation between their values. -/
@[simp]
theorem couplingPost_pure_pure_iff (a : α) (b : β) (R : RelPost α β) :
    CouplingPost (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) R ↔ R a b := by
  simp [CouplingPost]

/-- The output measure of a computation concentrates on its structural support. -/
theorem ae_mem_support (oa : OracleComp spec₁ α) :
    letI : MeasurableSpace α := ⊤; ∀ᵐ a ∂𝒟[oa], a ∈ support oa := by
  let : MeasurableSpace α := ⊤
  exact evalDist.ae_of_forall_mem_support oa _ MeasurableSet.of_discrete fun _ h ↦ h

/-- A coupling of two output measures concentrates on the product of their structural
supports. -/
theorem ae_mem_support_prod {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (c : letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤;
      Measure.Coupling 𝒟[oa] 𝒟[ob]) :
    letI : MeasurableSpace α := ⊤; letI : MeasurableSpace β := ⊤;
      ∀ᵐ z ∂c.joint, z.1 ∈ support oa ∧ z.2 ∈ support ob := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  exact c.isCoupling.ae_mem_prod MeasurableSet.of_discrete MeasurableSet.of_discrete
    (ae_mem_support oa) (ae_mem_support ob)

section finite

variable [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]

/-- Sequential composition of couplings. Finite response types discharge the countable choice
and concentration obligations of the measure-level rule; no positivity of response masses is
required. -/
theorem CouplingPost.bind {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {fa : α → OracleComp spec₁ γ} {fb : β → OracleComp spec₂ δ} {post : RelPost γ δ}
    (h : CouplingPost oa ob fun a b ↦ CouplingPost (fa a) (fb b) post) :
    CouplingPost (oa >>= fa) (ob >>= fb) post := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace γ := ⊤
  let : MeasurableSpace δ := ⊤
  rw [CouplingPost, RelWP, evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  rw [CouplingPost, RelWP] at h
  exact h.bind_of_countable_of_ae_mem
    (PFunctor.FreeM.support_finite oa).countable
    (PFunctor.FreeM.support_finite ob).countable
    (PFunctor.FreeM.support_finite (oa >>= fa)).countable
    (PFunctor.FreeM.support_finite (ob >>= fb)).countable
    (ae_mem_support oa) (ae_mem_support ob) .of_discrete .of_discrete
    (fun a ha ↦ evalDist.ae_of_forall_mem_support (fa a) _ MeasurableSet.of_discrete
      fun x hx ↦ MonadAttach.mem_support_bind.mpr ⟨a, ha, hx⟩)
    (fun b hb ↦ evalDist.ae_of_forall_mem_support (fb b) _ MeasurableSet.of_discrete
      fun y hy ↦ MonadAttach.mem_support_bind.mpr ⟨b, hb, hy⟩)
    (fun _ _ _ _ h ↦ by simpa only [CouplingPost, RelWP] using h)

/-- Relational algebra instance for `OracleComp`, based on measure coupling semantics. -/
noncomputable instance instMAlgRelOrdered :
    MAlgRelOrdered (OracleComp spec₁) (OracleComp spec₂) Prop where
  rwp := CouplingPost
  rwp_pure a b R := propext (couplingPost_pure_pure_iff a b R)
  rwp_mono hpost h := h.mono hpost
  rwp_bind_le _ _ _ _ _ h := CouplingPost.bind h

/-- Relational weakest precondition induced by `MAlgRelOrdered` for `OracleComp`. -/
abbrev RelWP (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) : Prop :=
  MAlgRelOrdered.RelWP (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop) oa ob R

/-- Relational Hoare-style triple with implicit precondition `True`. -/
abbrev RelTriple (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) : Prop :=
  MAlgRelOrdered.Triple (m₁ := OracleComp spec₁) (m₂ := OracleComp spec₂) (l := Prop) True oa ob R

@[simp] lemma relTriple_iff_relWP {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} :
    RelTriple oa ob R ↔ RelWP oa ob R :=
  ⟨fun h => h trivial, fun h _ => h⟩

@[simp] lemma relWP_iff_couplingPost {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} :
    RelWP oa ob R ↔ CouplingPost oa ob R := Iff.rfl

/-- Pure values on both sides: `R a b` implies the coupling. -/
lemma relTriple_pure_pure {a : α} {b : β} {R : RelPost α β} (h : R a b) :
    RelTriple (pure a : OracleComp spec₁ α) (pure b : OracleComp spec₂ β) R :=
  relTriple_iff_relWP.2 ((couplingPost_pure_pure_iff a b R).2 h)

/-- A computation is related to itself by every postcondition that is reflexive on its support. -/
lemma relTriple_refl_of_mem_support (oa : OracleComp spec₁ α) {R : RelPost α α}
    (hR : ∀ a ∈ support oa, R a a) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa oa R := by
  let : MeasurableSpace α := ⊤
  refine relTriple_iff_relWP.2 ⟨Measure.Coupling.refl 𝒟[oa], ?_⟩
  rw [Measure.Coupling.refl_joint]
  exact ae_map_of_ae_mem_countable (measurable_id.prodMk measurable_id)
    (PFunctor.FreeM.support_finite oa).countable
    ((ae_mem_support oa).mono fun a ha ↦ ⟨ha, hR a ha⟩)

/-- Every computation is coupled with itself on equality of outputs. -/
@[simp]
theorem couplingPost_refl (oa : OracleComp spec₁ α) : CouplingPost oa oa (· = ·) :=
  relTriple_iff_relWP.1 (relTriple_refl_of_mem_support (R := (· = ·)) oa fun _ _ => rfl)

/-- Reflexivity rule for relational triples on equality. -/
lemma relTriple_refl (oa : OracleComp spec₁ α) :
    RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa oa (EqRel α) :=
  relTriple_refl_of_mem_support oa fun _ _ => rfl

/-- Postcondition monotonicity for relational triples. -/
lemma relTriple_post_mono {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R R' : RelPost α β}
    (h : RelTriple oa ob R) (hpost : ∀ ⦃x y⦄, R x y → R' x y) :
    RelTriple oa ob R' :=
  relTriple_iff_relWP.2 ((relTriple_iff_relWP.1 h).mono fun _ _ hR => hpost hR)

/-- Two computations whose outputs satisfy independent support-wide postconditions are related
by their conjunction, through the independent product coupling. -/
theorem relTriple_prod {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {P : α → Prop} {Q : β → Prop} (hP : ∀ a ∈ support oa, P a) (hQ : ∀ b ∈ support ob, Q b) :
    RelTriple oa ob (fun a b => P a ∧ Q b) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have : IsProbabilityMeasure 𝒟[oa] := ⟨evalDist_apply_univ_eq_one oa⟩
  have : IsProbabilityMeasure 𝒟[ob] := ⟨evalDist_apply_univ_eq_one ob⟩
  let c := Measure.Coupling.prod 𝒟[oa] 𝒟[ob]
  exact relTriple_iff_relWP.2 ⟨c, (ae_mem_support_prod c).mono fun z hz ↦
    ⟨hP z.1 hz.1, hQ z.2 hz.2⟩⟩

/-- The independent product coupling relates any two computations by the constantly true
postcondition. This discharges any `RelTriple` goal whose postcondition is structurally
`fun _ _ => True` and is the foundation of the trivial-leaf closer in
`tryCloseRelGoalImmediate`. -/
lemma relTriple_true (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) :
    RelTriple oa ob (fun _ _ => True) :=
  relTriple_post_mono (relTriple_prod (P := fun _ ↦ True) (Q := fun _ ↦ True)
    (fun _ _ ↦ trivial) fun _ _ ↦ trivial) fun _ _ _ ↦ trivial

/-- Any postcondition that is unconditionally true gives a valid relational triple,
via the product coupling. Useful as a closing rule for vacuous postconditions. -/
lemma relTriple_post_const {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β}
    (h : ∀ a b, R a b) :
    RelTriple oa ob R :=
  relTriple_post_mono (relTriple_true oa ob) (fun _ _ _ => h _ _)

/-- Symmetry for relational triples, swapping the two computations and the postcondition. -/
lemma relTriple_symm {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β}
    (h : RelTriple oa ob R) :
    RelTriple ob oa (fun b a => R a b) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c.swap, ?_⟩
  exact (MeasurableEquiv.prodComm (α := α) (β := β)).measurableEmbedding.ae_map_iff.2 hc

/-- Transport a relational triple across equality of the left output measure. -/
lemma relTriple_of_evalDist_eq_left
    {ι₃ : Type w} {spec₃ : OracleSpec.{w, 0} ι₃} [∀ t, MeasurableSpace (spec₃.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec₃.Range t)] [IsMeasureSpec spec₃]
    [∀ t, Finite (spec₃.Range t)]
    {oa : OracleComp spec₁ α} {oa' : OracleComp spec₂ α}
    {ob : OracleComp spec₃ β} {R : RelPost α β}
    (heq : (letI : MeasurableSpace α := ⊤; 𝒟[oa] = 𝒟[oa'])) (h : RelTriple oa' ob R) :
    RelTriple oa ob R := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  exact relTriple_iff_relWP.2
    ⟨⟨c.joint, ⟨c.isCoupling.fst_eq.trans heq.symm, c.isCoupling.snd_eq⟩⟩, hc⟩

/-- Transport a relational triple across equality of the right output measure. -/
lemma relTriple_of_evalDist_eq_right
    {ι₃ : Type w} {spec₃ : OracleSpec.{w, 0} ι₃} [∀ t, MeasurableSpace (spec₃.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec₃.Range t)] [IsMeasureSpec spec₃]
    [∀ t, Finite (spec₃.Range t)]
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {ob' : OracleComp spec₃ β} {R : RelPost α β}
    (heq : (letI : MeasurableSpace β := ⊤; 𝒟[ob] = 𝒟[ob'])) (h : RelTriple oa ob R) :
    RelTriple oa ob' R := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  exact relTriple_iff_relWP.2
    ⟨⟨c.joint, ⟨c.isCoupling.fst_eq, c.isCoupling.snd_eq.trans heq⟩⟩, hc⟩

/-- Bind composition rule for relational triples. -/
lemma relTriple_bind
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {fa : α → OracleComp spec₁ γ}
    {fb : β → OracleComp spec₂ δ} {R : RelPost α β} {S : RelPost γ δ}
    (hxy : RelTriple oa ob R) (hfg : ∀ a b, R a b → RelTriple (fa a) (fb b) S) :
    RelTriple (oa >>= fa) (ob >>= fb) S :=
  MAlgRelOrdered.triple_bind hxy fun a b hR => hfg a b hR trivial

/-- Equality of programs gives an equality-relation relational triple. -/
lemma relTriple_eqRel_of_eq {oa ob : OracleComp spec₁ α}
    (h : oa = ob) : RelTriple (spec₁ := spec₁) (spec₂ := spec₁) oa ob (EqRel α) :=
  h ▸ relTriple_refl oa

/-- Equality of output measures gives an equality-relation relational triple. -/
lemma relTriple_eqRel_of_evalDist_eq {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : (letI : MeasurableSpace α := ⊤; 𝒟[oa] = 𝒟[ob])) :
    RelTriple oa ob (EqRel α) :=
  relTriple_of_evalDist_eq_right h (relTriple_refl oa)

/-- If two computations have equal output measures, any reflexive postcondition holds. -/
lemma relTriple_of_evalDist_eq
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α} {R : RelPost α α}
    (h : (letI : MeasurableSpace α := ⊤; 𝒟[oa] = 𝒟[ob])) (hR : ∀ x, R x x) :
    RelTriple oa ob R :=
  relTriple_post_mono (relTriple_eqRel_of_evalDist_eq h) fun x _ hxy => hxy ▸ hR x

/-- Swapping two adjacent independent binds preserves the output distribution. -/
lemma relTriple_bind_bind_swap_eqRel
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₁ β}
    {f : α → β → OracleComp spec₁ γ} :
    RelTriple
      (oa >>= fun a => ob >>= fun b => f a b)
      (ob >>= fun b => oa >>= fun a => f a b)
      (EqRel γ) := by
  let : MeasurableSpace γ := ⊤
  exact relTriple_eqRel_of_evalDist_eq (OracleComp.evalDist_bind_bind_swap oa ob f)

/-- Equality-relation relational triples identify the output measures. -/
lemma evalDist_eq_of_relTriple_eqRel {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple oa ob (EqRel α)) :
    letI : MeasurableSpace α := ⊤; 𝒟[oa] = 𝒟[ob] := by
  let : MeasurableSpace α := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  calc 𝒟[oa] = c.joint.map Prod.fst := c.isCoupling.fst_eq.symm
    _ = c.joint.map Prod.snd := Measure.map_congr hc
    _ = 𝒟[ob] := c.isCoupling.snd_eq

/-- Equality-relation relational triples give every event the same probability. -/
lemma prEvent_eq_of_relTriple_eqRel {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ α}
    (h : RelTriple oa ob (EqRel α)) (p : α → Prop) :
    Pr{let a ← oa}[p a] = Pr{let b ← ob}[p b] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
    evalDist_eq_of_relTriple_eqRel h]

/-- Event monotonicity from a relational triple: if `RelTriple oa ob R` and `R a b` forces
`p a → q b`, then `Pr{let a ← oa}[p a] ≤ Pr{let b ← ob}[q b]`. Both events are read through the
coupling's marginals, where the implication holds almost everywhere. -/
lemma prEvent_le_of_relTriple {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (h : RelTriple oa ob R)
    {p : α → Prop} {q : β → Prop} (himp : ∀ a b, R a b → p a → q b) :
    Pr{let a ← oa}[p a] ≤ Pr{let b ← ob}[q b] := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
  calc 𝒟[oa] {a | p a} = c.joint.fst {a | p a} := by rw [c.isCoupling.fst_eq]
    _ = c.joint (Prod.fst ⁻¹' {a | p a}) := Measure.fst_apply MeasurableSet.of_discrete
    _ ≤ c.joint (Prod.snd ⁻¹' {b | q b}) :=
      measure_mono_ae (hc.mono fun z hR hp ↦ himp z.1 z.2 hR hp)
    _ = c.joint.snd {b | q b} := (Measure.snd_apply MeasurableSet.of_discrete).symm
    _ = 𝒟[ob] {b | q b} := by rw [c.isCoupling.snd_eq]

/-- Transitivity through an intermediate computation related to the left side by `EqRel`. -/
lemma relTriple_trans_eqRel_left
    {ι₃ : Type w} {spec₃ : OracleSpec.{w, 0} ι₃} [∀ t, MeasurableSpace (spec₃.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec₃.Range t)] [IsMeasureSpec spec₃]
    [∀ t, Finite (spec₃.Range t)]
    {oa : OracleComp spec₁ α} {mid : OracleComp spec₂ α}
    {ob : OracleComp spec₃ β} {R : RelPost α β}
    (hleft : RelTriple oa mid (EqRel α)) (hright : RelTriple mid ob R) :
    RelTriple oa ob R :=
  relTriple_of_evalDist_eq_left (evalDist_eq_of_relTriple_eqRel hleft) hright

/-- Transitivity through an intermediate computation related to the right side by `EqRel`. -/
lemma relTriple_trans_eqRel_right
    {ι₃ : Type w} {spec₃ : OracleSpec.{w, 0} ι₃} [∀ t, MeasurableSpace (spec₃.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec₃.Range t)] [IsMeasureSpec spec₃]
    [∀ t, Finite (spec₃.Range t)]
    {oa : OracleComp spec₁ α} {mid : OracleComp spec₂ β}
    {ob : OracleComp spec₃ β} {R : RelPost α β}
    (hleft : RelTriple oa mid R) (hright : RelTriple mid ob (EqRel β)) :
    RelTriple oa ob R :=
  relTriple_of_evalDist_eq_right (evalDist_eq_of_relTriple_eqRel hright) hleft

/-- Transitivity of equality-relation relational triples through an intermediate computation. -/
lemma relTriple_trans_eqRel
    {ι₃ : Type w} {spec₃ : OracleSpec.{w, 0} ι₃} [∀ t, MeasurableSpace (spec₃.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec₃.Range t)] [IsMeasureSpec spec₃]
    [∀ t, Finite (spec₃.Range t)]
    {oa : OracleComp spec₁ α} {mid : OracleComp spec₂ α} {ob : OracleComp spec₃ α}
    (hleft : RelTriple oa mid (EqRel α)) (hright : RelTriple mid ob (EqRel α)) :
    RelTriple oa ob (EqRel α) :=
  relTriple_trans_eqRel_left hleft hright

/-! ## Oracle query coupling rules (pRHL level) -/

/-- Same-type identity coupling: querying the same oracle on both sides yields equal outputs. -/
lemma relTriple_query (t : spec₁.Domain) :
    RelTriple
      (spec₁ := spec₁) (spec₂ := spec₁)
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (EqRel (spec₁.Range t)) :=
  relTriple_refl (liftM (query t) : OracleComp spec₁ (spec₁.Range t))

/-- Mapping both sides of a relational triple by `f` and `g` transports the
postcondition along `f` and `g`. -/
lemma relTriple_map {R : RelPost γ δ} {f : α → γ} {g : β → δ}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    (h : RelTriple oa ob (fun a b => R (f a) (g b))) :
    RelTriple (f <$> oa) (g <$> ob) R :=
  h.trans ((MAlgRelOrdered.relWP_map_right g oa ob _).trans
    (MAlgRelOrdered.relWP_map_left f oa (g <$> ob) _))

/-- If a relational triple holds for `fun a b => f a = g b`, then mapping by `f` and `g`
produces equal output measures. Generalizes `evalDist_eq_of_relTriple_eqRel`. -/
lemma evalDist_map_eq_of_relTriple {σ : Type} {f : α → σ} {g : β → σ} {oa : OracleComp spec₁ α}
    {ob : OracleComp spec₂ β} (h : RelTriple oa ob (fun a b => f a = g b)) :
    letI : MeasurableSpace σ := ⊤; 𝒟[f <$> oa] = 𝒟[g <$> ob] :=
  evalDist_eq_of_relTriple_eqRel (relTriple_map h)

private lemma list_eq_of_forall₂_eqRel {xs ys : List α}
    (hxy : List.Forall₂ (EqRel α) xs ys) : xs = ys := by
  rwa [EqRel, List.forall₂_eq_eq_eq] at hxy

/-- Lift a one-step coupling through bounded iteration. -/
lemma relTriple_replicate
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β} {R : RelPost α β} (n : ℕ)
    (hstep : RelTriple oa ob R) :
    RelTriple (oa.replicate n) (ob.replicate n) (List.Forall₂ R) := by
  induction n with
  | zero =>
    simp only [OracleComp.replicate_zero]
    exact relTriple_pure_pure List.Forall₂.nil
  | succ n ih =>
    simp only [OracleComp.replicate_succ_bind]
    exact relTriple_bind hstep fun a b hab =>
      relTriple_bind ih fun xs ys hxy => relTriple_pure_pure (List.Forall₂.cons hab hxy)

/-- Equality coupling version of `relTriple_replicate`. -/
lemma relTriple_replicate_eqRel
    {oa ob : OracleComp spec₁ α} (n : ℕ)
    (hstep : RelTriple oa ob (EqRel α)) :
    RelTriple (oa.replicate n) (ob.replicate n) (EqRel (List α)) :=
  relTriple_post_mono
    (h := relTriple_replicate (n := n) (R := EqRel α) hstep)
    fun _ _ => list_eq_of_forall₂_eqRel

/-- Lift pointwise relational reasoning through finite list traversals. -/
lemma relTriple_list_mapM
    {xs : List α} {ys : List β}
    {f : α → OracleComp spec₁ γ} {g : β → OracleComp spec₂ δ}
    {Rin : α → β → Prop} {Rout : γ → δ → Prop}
    (hxy : List.Forall₂ Rin xs ys)
    (hfg : ∀ a b, Rin a b → RelTriple (f a) (g b) Rout) :
    RelTriple (xs.mapM f) (ys.mapM g) (List.Forall₂ Rout) := by
  induction hxy with
  | nil =>
    simp only [List.mapM_nil]
    exact relTriple_pure_pure (R := List.Forall₂ Rout) (a := []) (b := []) List.Forall₂.nil
  | @cons a b xs ys hab htl ih =>
    simp only [List.mapM_cons]
    exact relTriple_bind (hfg a b hab) fun x y hxy =>
      relTriple_bind ih fun xs' ys' hxs => relTriple_pure_pure (List.Forall₂.cons hxy hxs)

/-- Same-input equality-coupling specialization of `relTriple_list_mapM`. -/
lemma relTriple_list_mapM_eqRel
    {xs : List α}
    {f : α → OracleComp spec₁ β} {g : α → OracleComp spec₂ β}
    (hfg : ∀ a, RelTriple (f a) (g a) (EqRel β)) :
    RelTriple (xs.mapM f) (xs.mapM g) (EqRel (List β)) :=
  relTriple_post_mono
    (h := relTriple_list_mapM (Rin := EqRel α) (Rout := EqRel β)
      (hxy := by rw [EqRel, List.forall₂_eq_eq_eq])
      (hfg := by rintro a _ rfl; simpa using hfg a))
    fun _ _ => list_eq_of_forall₂_eqRel

/-- Loop-invariant rule for bounded left folds over related input lists. -/
lemma relTriple_list_foldlM
    {σ₁ σ₂ : Type}
    {xs : List α} {ys : List β}
    {f : σ₁ → α → OracleComp spec₁ σ₁}
    {g : σ₂ → β → OracleComp spec₂ σ₂}
    {Rin : α → β → Prop} {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hxy : List.Forall₂ Rin xs ys)
    (hfg : ∀ a b, Rin a b → ∀ t₁ t₂, S t₁ t₂ → RelTriple (f t₁ a) (g t₂ b) S) :
    RelTriple (xs.foldlM f s₁) (ys.foldlM g s₂) S := by
  induction hxy generalizing s₁ s₂ with
  | nil =>
    rw [List.foldlM_nil, List.foldlM_nil]
    exact relTriple_pure_pure (R := S) (a := s₁) (b := s₂) hs
  | @cons a b xs ys hab htl ih =>
    rw [List.foldlM_cons, List.foldlM_cons]
    exact relTriple_bind (hfg a b hab s₁ s₂ hs) fun t₁ t₂ ht => ih ht

/-- Same-input specialization of `relTriple_list_foldlM`. -/
lemma relTriple_list_foldlM_same
    {σ₁ σ₂ : Type}
    {xs : List α}
    {f : σ₁ → α → OracleComp spec₁ σ₁}
    {g : σ₂ → α → OracleComp spec₂ σ₂}
    {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hfg : ∀ a t₁ t₂, S t₁ t₂ → RelTriple (f t₁ a) (g t₂ a) S) :
    RelTriple (xs.foldlM f s₁) (xs.foldlM g s₂) S := by
  refine relTriple_list_foldlM
    (Rin := EqRel α) (hs := hs)
    (hxy := by simp [EqRel]) ?_
  intro a b hab t₁ t₂ ht
  dsimp [EqRel] at hab
  cases hab
  simpa using hfg a t₁ t₂ ht

/-! ## Synchronized branching rule -/

/-- Synchronized conditional: if both sides branch on the same condition, the
relational triple holds if it holds on both branches. -/
lemma relTriple_if {c : Prop} [Decidable c]
    {oa₁ oa₂ : OracleComp spec₁ α} {ob₁ ob₂ : OracleComp spec₂ β}
    {R : RelPost α β}
    (htrue : c → RelTriple oa₁ ob₁ R)
    (hfalse : ¬c → RelTriple oa₂ ob₂ R) :
    RelTriple (if c then oa₁ else oa₂) (if c then ob₁ else ob₂) R := by
  split_ifs with h
  · exact htrue h
  · exact hfalse h

/-- Pure-left rule: the left side is a pure value, applied via bind decomposition. -/
lemma relTriple_pure_left {a : α} {ob : OracleComp spec₂ β}
    {R : RelPost α β}
    (h : RelTriple (pure a : OracleComp spec₁ α) ob
      (fun x y => x = a ∧ R x y)) :
    RelTriple (pure a : OracleComp spec₁ α) ob R :=
  relTriple_post_mono h (fun _ _ ⟨_, hr⟩ => hr)

/-- Pure-right rule: the right side is a pure value, applied via bind decomposition. -/
lemma relTriple_pure_right {oa : OracleComp spec₁ α} {b : β}
    {R : RelPost α β}
    (h : RelTriple oa (pure b : OracleComp spec₂ β)
      (fun x y => y = b ∧ R x y)) :
    RelTriple oa (pure b : OracleComp spec₂ β) R :=
  relTriple_post_mono h (fun _ _ ⟨_, hr⟩ => hr)

end finite

end measureSpec

/-! ## Anchoring and bijection rules under uniform response measures -/

section uniformMeasureSpec

variable [∀ t, DiscreteMeasurableSpace (spec₁.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec₂.Range t)]
  [IsUniformMeasureSpec spec₁] [IsUniformMeasureSpec spec₂]

/-- A coupling with a Dirac first marginal forces the first coordinate, so an almost-sure
relation holds between that value and every structurally reachable output of the second
computation, each of which has positive mass under uniform response measures. -/
private theorem forall_mem_support_of_couplingPost_pure_left {a : α} {y : OracleComp spec₂ β}
    {post : RelPost α β} (h : CouplingPost (pure a : OracleComp spec₁ α) y post) :
    ∀ b ∈ support y, post a b := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := h
  intro b hb
  by_contra hpost
  have hmeas : MeasurableSet {x : α | x = a} := measurableSet_singleton a
  have hfst : ∀ᵐ z ∂c.joint, z.1 = a := by
    refine (ae_map_iff measurable_fst.aemeasurable hmeas).1 ?_
    rw [show c.joint.map Prod.fst = 𝒟[(pure a : OracleComp spec₁ α)] from c.isCoupling.fst_eq,
      evalDist_pure]
    exact (ae_dirac_iff hmeas).2 rfl
  have hbad : c.joint {z | ¬(z.1 = a ∧ post z.1 z.2)} = 0 := ae_iff.1 (hfst.and hc)
  have hnull : c.joint (Prod.snd ⁻¹' {b}) = 0 := by
    refine measure_mono_null (t := {z | ¬(z.1 = a ∧ post z.1 z.2)}) ?_ hbad
    intro z hz hgood
    refine hpost ?_
    obtain ⟨h₁, h₂⟩ := hgood
    have h₃ : z.2 = b := hz
    rwa [h₁, h₃] at h₂
  have hpos := (mem_support_iff_evalDist_singleton_pos y b).1 hb
  rw [← c.isCoupling.snd_eq, Measure.snd_apply (measurableSet_singleton b), hnull] at hpos
  exact lt_irrefl 0 hpos

/-- A pure first computation is coupled with any computation whose reachable outputs all
satisfy the relation with its value. -/
private theorem couplingPost_pure_left_of_forall_mem_support {a : α} {y : OracleComp spec₂ β}
    {post : RelPost α β} (h : ∀ b ∈ support y, post a b) :
    CouplingPost (pure a : OracleComp spec₁ α) y post := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have : IsProbabilityMeasure 𝒟[y] := ⟨evalDist_apply_univ_eq_one y⟩
  let c := Measure.Coupling.prod 𝒟[(pure a : OracleComp spec₁ α)] 𝒟[y]
  refine ⟨c, (ae_mem_support_prod c).mono fun z hz ↦ ?_⟩
  obtain ⟨hz₁, hz₂⟩ := hz
  have hz₁ : z.1 = a := by simpa using hz₁
  exact hz₁ ▸ h z.2 hz₂

variable [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]

/-- Anchoring instance for the qualitative `Prop`-valued relational logic on `OracleComp`.

When one of the two computations is `pure`, the relational coupling logic collapses to the
unary support-based logic of the other side. Every reachable output has positive mass under
uniform response measures, so an almost-sure relation holds on the whole structural support.

Together with the unary `Prop` algebra in `VCVio/ProgramLogic/Unary/HoarePropTriple.lean`,
this lets `wpExc` / `rwpExc`-style honest exception combinators (in
`ToMathlib/Control/Monad/RelationalAlgebraAnchored.lean`) be derived uniformly. -/
instance instAnchored : MAlgRelOrdered.Anchored (OracleComp spec₁) (OracleComp spec₂) Prop where
  rwp_pure_left {α β} a y post := by
    refine propext ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support]
      exact forall_mem_support_of_couplingPost_pure_left h
    · rw [OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support] at h
      exact couplingPost_pure_left_of_forall_mem_support h
  rwp_pure_right {α β} x b post := by
    refine propext ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support]
      exact forall_mem_support_of_couplingPost_pure_left
        (relTriple_iff_relWP.1 (relTriple_symm (relTriple_iff_relWP.2 h)))
    · rw [OracleComp.ProgramLogic.PropLogic.wp_iff_forall_support] at h
      exact relTriple_iff_relWP.1 (relTriple_symm (spec₁ := spec₂) (spec₂ := spec₁)
        (relTriple_iff_relWP.2 (couplingPost_pure_left_of_forall_mem_support h)))

/-- Bijection coupling (the "rnd" rule from EasyCrypt):
querying the same oracle on both sides, related by a bijection `f`. -/
lemma relTriple_query_bij (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t}
    (hf : Function.Bijective f) :
    RelTriple
      (spec₁ := spec₁) (spec₂ := spec₁)
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (liftM (query t) : OracleComp spec₁ (spec₁.Range t))
      (fun a b => f a = b) := by
  have := IsUniformMeasureSpec.nonempty_range (spec := spec₁) t
  have hq := OracleComp.evalDist_liftM_query_eq_uniformOn_top (spec := spec₁) t
  let : MeasurableSpace (spec₁.Range t) := ⊤
  have hgraph : Measurable fun a : spec₁.Range t ↦ (a, f a) := Measurable.of_discrete
  refine relTriple_iff_relWP.2 ⟨⟨𝒟[(liftM (query t) : OracleComp spec₁ _)].map
    fun a ↦ (a, f a), ?_, ?_⟩, ?_⟩
  · rw [Measure.fst, Measure.map_map measurable_fst hgraph]
    exact Measure.map_id
  · rw [Measure.snd, Measure.map_map measurable_snd hgraph]
    change Measure.map f _ = _
    rw [hq]
    exact map_uniformOn_univ_of_bijective Measurable.of_discrete hf
  · exact (ae_map_iff hgraph.aemeasurable (Set.to_countable _).measurableSet).2
      (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Bind rule specialized to two equal oracle queries coupled by a bijection.

The continuation is stated over the left sample only, with the right sample
already rewritten to `f a`. This is the stable continuation shape used by
the relational tactic for unary bijection hints. -/
lemma relTriple_bind_query_bij (t : spec₁.Domain)
    {f : spec₁.Range t → spec₁.Range t} {fa : spec₁.Range t → OracleComp spec₁ γ}
    {fb : spec₁.Range t → OracleComp spec₁ δ} {S : RelPost γ δ}
    (hfg : ∀ a, RelTriple (fa a) (fb (f a)) S)
    (hf : Function.Bijective f) :
    RelTriple
      ((liftM (query t) : OracleComp spec₁ (spec₁.Range t)) >>= fa)
      ((liftM (query t) : OracleComp spec₁ (spec₁.Range t)) >>= fb)
      S :=
  relTriple_bind (R := fun a b => b = f a)
    (relTriple_post_mono (relTriple_query_bij t hf) fun _ _ h => h.symm)
    fun a b hb => by simpa [hb] using hfg a

end uniformMeasureSpec

section Sampling

variable [SampleableType α]

/-- Relational coupling for uniform sampling via bijection.
Given a bijection `f : α → α` such that `R x (f x)` for all `x`,
the two uniform samples are related by `R`. -/
lemma relTriple_uniformSample_bij
    {f : α → α} (hf : Function.Bijective f) (R : RelPost α α)
    (hR : ∀ x, R x (f x)) :
    RelTriple ($ᵗ α) ($ᵗ α) R := by
  let : MeasurableSpace α := ⊤
  have hgraph : Measurable fun a : α ↦ (a, f a) := Measurable.of_discrete
  refine relTriple_iff_relWP.2 ⟨⟨𝒟[($ᵗ α : ProbComp α)].map fun a ↦ (a, f a), ?_, ?_⟩, ?_⟩
  · rw [Measure.fst, Measure.map_map measurable_fst hgraph]
    exact Measure.map_id
  · rw [Measure.snd, Measure.map_map measurable_snd hgraph]
    change Measure.map f _ = _
    rw [SampleableType.evalDist_uniformSample]
    exact map_uniformOn_univ_of_bijective Measurable.of_discrete hf
  · exact (ae_map_iff hgraph.aemeasurable (Set.to_countable _).measurableSet).2
      (Filter.Eventually.of_forall hR)

/-- Bind rule specialized to two uniform samples coupled by a bijection.

The continuation is stated over the left sample only, with the right sample
already rewritten to `f a`. This avoids exposing an auxiliary equality witness
to proof scripts after `rvcstep using f`. -/
lemma relTriple_bind_uniformSample_bij
    {f : α → α}
    {fa : α → ProbComp γ} {fb : α → ProbComp δ}
    {S : RelPost γ δ}
    (hfg : ∀ a, RelTriple (fa a) (fb (f a)) S)
    (hf : Function.Bijective f) :
    RelTriple (($ᵗ α : ProbComp α) >>= fa) (($ᵗ α : ProbComp α) >>= fb) S := by
  refine relTriple_bind (R := fun a b => b = f a) ?_ ?_
  · exact relTriple_uniformSample_bij hf _ (fun _ => rfl)
  · intro a b hb
    simpa [hb] using hfg a

/-- Identity coupling for uniform sampling. -/
lemma relTriple_uniformSample_refl :
    RelTriple ($ᵗ α) ($ᵗ α) (EqRel α) :=
  relTriple_uniformSample_bij Function.bijective_id (EqRel α) fun _ => rfl

end Sampling

end OracleComp.ProgramLogic.Relational
