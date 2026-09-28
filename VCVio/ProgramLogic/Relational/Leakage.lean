/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.ProgramLogic.Relational.Basic
public import ToMathlib.MeasureTheory.Measure.TotalVariation.Bind

/-!
# Leakage Judgments for Side-Channel Reasoning

This file defines three leakage judgments of increasing strength, enabling formal
side-channel reasoning within the VCVio framework. All three operate on observed
computations (outputs of `runObs`) that produce a result paired with an accumulated trace.
Trace laws are compared in the discrete structure on the trace type.

## Main Definitions

* `TraceNoninterference`: exact trace equality along a coupling (a pRHL triple).
  Two observed computations satisfy this when their trace components always match,
  regardless of the result. This is the VCVio analogue of constant-time execution.
* `ProbLeakFree`: distributional trace independence.
  The trace distribution does not depend on secrets.
* `LeakageBound`: approximate trace independence via total variation distance.
  The trace distributions differ by at most `ε`.

## Main Results

* `traceNoninterference_implies_probLeakFree`: exact trace equality implies distributional
  independence.
* `probLeakFree_iff_leakageBound_zero`: `ProbLeakFree` is the `ε = 0` case of `LeakageBound`.
* `leakageBound_triangle`: transitivity for game-hopping arguments.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal MeasureTheory

universe u

namespace OracleComp.Leakage

variable {ι₁ : Type u} {ι₂ : Type u} {ι₃ : Type u}
variable {spec₁ : OracleSpec.{u, 0} ι₁} {spec₂ : OracleSpec.{u, 0} ι₂}
  {spec₃ : OracleSpec.{u, 0} ι₃}
variable [∀ t, MeasurableSpace (spec₁.Range t)] [∀ t, MeasurableSpace (spec₂.Range t)]
  [∀ t, MeasurableSpace (spec₃.Range t)]
  [IsMeasureSpec spec₁] [IsMeasureSpec spec₂] [IsMeasureSpec spec₃]
variable {α β γ : Type} {ω : Type}

/-! ### TraceNoninterference -/

/-- Exact trace noninterference: two observed computations produce equal trace components
along some coupling of their outputs. This is the strongest leakage judgment, corresponding to
constant-time execution for deterministic channels. -/
def TraceNoninterference [∀ t, DiscreteMeasurableSpace (spec₁.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec₂.Range t)]
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]
    (oa₁ : OracleComp spec₁ (α × ω))
    (oa₂ : OracleComp spec₂ (β × ω)) : Prop :=
  ProgramLogic.Relational.RelTriple oa₁ oa₂ (fun z₁ z₂ => z₁.2 = z₂.2)

/-! ### ProbLeakFree -/

/-- Distributional trace independence: the trace distributions are identical regardless
of which computation produced them. This captures the property that an adversary observing
only the trace cannot distinguish between the two computations.

The trace laws are compared as measures in the discrete structure on the trace type, allowing
computations over different oracle specs to be compared. -/
def ProbLeakFree (oa₁ : OracleComp spec₁ (α × ω)) (oa₂ : OracleComp spec₂ (β × ω)) : Prop :=
  letI : MeasurableSpace ω := ⊤; 𝒟[Prod.snd <$> oa₁] = 𝒟[Prod.snd <$> oa₂]

/-! ### LeakageBound -/

/-- Approximate trace independence: the trace distributions differ by at most `ε` in total
variation distance. This enables game-hopping arguments where each hop introduces a small
leakage discrepancy. -/
def LeakageBound (ε : ℝ≥0∞) (oa₁ : OracleComp spec₁ (α × ω))
    (oa₂ : OracleComp spec₂ (β × ω)) : Prop :=
  letI : MeasurableSpace ω := ⊤; 𝒟[Prod.snd <$> oa₁].etvDist 𝒟[Prod.snd <$> oa₂] ≤ ε

/-! ### Bridge Lemmas -/

/-- Exact trace noninterference implies distributional trace independence:
if traces always match along a coupling, their distributions must be equal. -/
theorem traceNoninterference_implies_probLeakFree
    [∀ t, DiscreteMeasurableSpace (spec₁.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec₂.Range t)]
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : TraceNoninterference oa₁ oa₂) :
    ProbLeakFree oa₁ oa₂ :=
  evalDistEq_iff_evalDist_eq.mp (ProgramLogic.Relational.evalDistEq_map_of_relTriple h)

/-- `ProbLeakFree` is equivalent to `LeakageBound 0`. -/
theorem probLeakFree_iff_leakageBound_zero
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)} :
    ProbLeakFree oa₁ oa₂ ↔ LeakageBound 0 oa₁ oa₂ := by
  let : MeasurableSpace ω := ⊤
  rw [ProbLeakFree, LeakageBound, nonpos_iff_eq_zero, Measure.etvDist_eq_zero_iff]

/-- Transitivity of `LeakageBound` for game-hopping: if the first pair of computations
has leakage at most `ε₁` and the second pair at most `ε₂`, then the outer pair has
leakage at most `ε₁ + ε₂`. -/
theorem leakageBound_triangle
    {ε₁ ε₂ : ℝ≥0∞}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    {oa₃ : OracleComp spec₃ (γ × ω)}
    (h₁₂ : LeakageBound ε₁ oa₁ oa₂) (h₂₃ : LeakageBound ε₂ oa₂ oa₃) :
    LeakageBound (ε₁ + ε₂) oa₁ oa₃ := by
  let : MeasurableSpace ω := ⊤
  exact (Measure.etvDist_triangle _ _ _).trans (add_le_add h₁₂ h₂₃)

/-- `ProbLeakFree` is reflexive. -/
theorem probLeakFree_refl (oa : OracleComp spec₁ (α × ω)) :
    ProbLeakFree oa oa := rfl

/-- `ProbLeakFree` is symmetric. -/
theorem probLeakFree_symm
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂) :
    ProbLeakFree oa₂ oa₁ := h.symm

/-- `LeakageBound` with `ε = 0` implies `ProbLeakFree`. -/
theorem probLeakFree_of_leakageBound_zero
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound 0 oa₁ oa₂) :
    ProbLeakFree oa₁ oa₂ :=
  probLeakFree_iff_leakageBound_zero.mpr h

/-- `LeakageBound` is reflexive with bound `0`. -/
@[simp]
theorem leakageBound_refl (oa : OracleComp spec₁ (α × ω)) :
    LeakageBound 0 oa oa := by
  let : MeasurableSpace ω := ⊤
  exact (Measure.etvDist_self _).le

/-- `LeakageBound` is symmetric. -/
theorem leakageBound_symm
    {ε : ℝ≥0∞} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) :
    LeakageBound ε oa₂ oa₁ := by
  let : MeasurableSpace ω := ⊤
  exact (Measure.etvDist_comm _ _).trans_le h

/-- Monotonicity: a smaller leakage bound implies a larger one. -/
theorem leakageBound_mono
    {ε₁ ε₂ : ℝ≥0∞} (hε : ε₁ ≤ ε₂)
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε₁ oa₁ oa₂) :
    LeakageBound ε₂ oa₁ oa₂ := le_trans h hε

/-! ### Compositional Lemmas: Map -/

/-- Mapping the result component preserves distributional trace independence. -/
theorem probLeakFree_map_fst
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂) {δ : Type} (f₁ : α → γ) (f₂ : β → δ) :
    ProbLeakFree (Prod.map f₁ id <$> oa₁) (Prod.map f₂ id <$> oa₂) := by
  simpa only [ProbLeakFree, Functor.map_map, Function.comp_def, Prod.map, id_eq] using h

/-- Mapping the result component preserves approximate trace independence. -/
theorem leakageBound_map_fst
    {ε : ℝ≥0∞} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) {δ : Type} (f₁ : α → γ) (f₂ : β → δ) :
    LeakageBound ε (Prod.map f₁ id <$> oa₁) (Prod.map f₂ id <$> oa₂) := by
  simpa only [LeakageBound, Functor.map_map, Function.comp_def, Prod.map, id_eq] using h

variable [∀ t, DiscreteMeasurableSpace (spec₁.Range t)]
  [∀ t, DiscreteMeasurableSpace (spec₂.Range t)]

/-- Mapping the result component preserves trace noninterference. -/
theorem traceNoninterference_map_fst
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : TraceNoninterference oa₁ oa₂) {δ : Type} (f₁ : α → γ) (f₂ : β → δ) :
    TraceNoninterference (Prod.map f₁ id <$> oa₁) (Prod.map f₂ id <$> oa₂) := by
  simp only [TraceNoninterference] at h ⊢
  exact ProgramLogic.Relational.relTriple_map h

/-- Mapping the trace component with the same function preserves distributional trace
independence. -/
theorem probLeakFree_map_snd
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂) {ω' : Type} (g : ω → ω') :
    ProbLeakFree (Prod.map id g <$> oa₁) (Prod.map id g <$> oa₂) := by
  let : MeasurableSpace ω := ⊤
  let : MeasurableSpace ω' := ⊤
  change 𝒟[Prod.snd <$> (Prod.map id g <$> oa₁)] = 𝒟[Prod.snd <$> (Prod.map id g <$> oa₂)]
  rw [snd_map_prod_map_eq_map, snd_map_prod_map_eq_map,
    evalDist_map_of_discrete (Prod.snd <$> oa₁), evalDist_map_of_discrete (Prod.snd <$> oa₂),
    show 𝒟[Prod.snd <$> oa₁] = 𝒟[Prod.snd <$> oa₂] from h]

/-- Mapping the trace component with the same function preserves approximate trace
independence. -/
theorem leakageBound_map_snd
    {ε : ℝ≥0∞} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) {ω' : Type} (g : ω → ω') :
    LeakageBound ε (Prod.map id g <$> oa₁) (Prod.map id g <$> oa₂) := by
  let : MeasurableSpace ω := ⊤
  let : MeasurableSpace ω' := ⊤
  change 𝒟[Prod.snd <$> (Prod.map id g <$> oa₁)].etvDist
    𝒟[Prod.snd <$> (Prod.map id g <$> oa₂)] ≤ ε
  rw [snd_map_prod_map_eq_map, snd_map_prod_map_eq_map,
    evalDist_map_of_discrete (Prod.snd <$> oa₁), evalDist_map_of_discrete (Prod.snd <$> oa₂)]
  exact (Measure.etvDist_map_le _ _ g Measurable.of_discrete).trans h

/-- Mapping the trace component with the same function preserves trace noninterference. -/
theorem traceNoninterference_map_snd
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : TraceNoninterference oa₁ oa₂) {ω' : Type} (g : ω → ω') :
    TraceNoninterference (Prod.map id g <$> oa₁) (Prod.map id g <$> oa₂) := by
  simp only [TraceNoninterference] at h ⊢
  exact ProgramLogic.Relational.relTriple_map
    (ProgramLogic.Relational.relTriple_post_mono h fun {_ _} hw => congrArg g hw)

/-! ### Compositional Lemmas: Bind -/

private lemma snd_map_bind_snd {m : Type → Type _} [Monad m] [LawfulMonad m]
    {α' ω₁ γ' ω₂ : Type} (mx : m (α' × ω₁)) (f : ω₁ → m (γ' × ω₂)) :
    Prod.snd <$> (mx >>= fun z => f z.2) =
    (Prod.snd <$> mx) >>= fun w => Prod.snd <$> f w := by
  simp only [monad_norm, Function.comp_apply]

/-- Trace noninterference is preserved by sequential composition (bind).
The continuations may depend on both the result and the trace, but whenever the
traces match, the continuations must themselves be trace noninterfering. -/
theorem traceNoninterference_bind
    [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)]
    {δ ω' : Type}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    {f₁ : (α × ω) → OracleComp spec₁ (γ × ω')}
    {f₂ : (β × ω) → OracleComp spec₂ (δ × ω')}
    (h : TraceNoninterference oa₁ oa₂)
    (hf : ∀ a b w, TraceNoninterference (f₁ (a, w)) (f₂ (b, w))) :
    TraceNoninterference (oa₁ >>= f₁) (oa₂ >>= f₂) := by
  simp only [TraceNoninterference] at h ⊢
  refine ProgramLogic.Relational.relTriple_bind h fun ⟨a, w₁⟩ ⟨b, w₂⟩ hw => ?_
  subst hw
  exact hf a b w₁

/-- Distributional trace independence is preserved by bind when the continuation
depends only on the trace (second component). -/
theorem probLeakFree_bind_of_trace_only
    {δ ω' : Type}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂)
    {f : ω → OracleComp spec₁ (γ × ω')} {g : ω → OracleComp spec₂ (δ × ω')}
    (hfg : ∀ w, ProbLeakFree (f w) (g w)) :
    ProbLeakFree (oa₁ >>= fun z => f z.2) (oa₂ >>= fun z => g z.2) := by
  let : MeasurableSpace ω := ⊤
  let : MeasurableSpace ω' := ⊤
  change 𝒟[Prod.snd <$> (oa₁ >>= fun z => f z.2)] = 𝒟[Prod.snd <$> (oa₂ >>= fun z => g z.2)]
  rw [snd_map_bind_snd _ f, snd_map_bind_snd _ g, evalDist_bind_of_discrete (Prod.snd <$> oa₁),
    evalDist_bind_of_discrete (Prod.snd <$> oa₂),
    show 𝒟[Prod.snd <$> oa₁] = 𝒟[Prod.snd <$> oa₂] from h,
    show (fun w => 𝒟[Prod.snd <$> f w]) = fun w => 𝒟[Prod.snd <$> g w] from funext hfg]

/-- Approximate trace independence is preserved by bind when the continuation depends
only on the trace and produces identical trace distributions. -/
theorem leakageBound_bind_of_trace_only
    {ε : ℝ≥0∞} {δ ω' : Type}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂)
    {f : ω → OracleComp spec₁ (γ × ω')} {g : ω → OracleComp spec₂ (δ × ω')}
    (hfg : ∀ w, ProbLeakFree (f w) (g w)) :
    LeakageBound ε (oa₁ >>= fun z => f z.2) (oa₂ >>= fun z => g z.2) := by
  let : MeasurableSpace ω := ⊤
  let : MeasurableSpace ω' := ⊤
  change 𝒟[Prod.snd <$> (oa₁ >>= fun z => f z.2)].etvDist
    𝒟[Prod.snd <$> (oa₂ >>= fun z => g z.2)] ≤ ε
  rw [snd_map_bind_snd _ f, snd_map_bind_snd _ g, evalDist_bind_of_discrete (Prod.snd <$> oa₁),
    evalDist_bind_of_discrete (Prod.snd <$> oa₂),
    show (fun w => 𝒟[Prod.snd <$> g w]) = fun w => 𝒟[Prod.snd <$> f w] from
      funext fun w => (hfg w).symm]
  exact (Measure.etvDist_bind_le _ _ _ Measurable.of_discrete).trans h

end OracleComp.Leakage
