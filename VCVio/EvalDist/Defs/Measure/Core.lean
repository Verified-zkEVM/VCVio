/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import ToMathlib.MeasureTheory.Measure.Prop
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measure-valued evaluation and its composition laws

`EvalDistSemantics` denotes successful outputs by subprobability measures.
`LawfulPureEvalDistSemantics` supplies the Dirac equation independently of bind, while
`LawfulEvalDistSemantics` adds the measurable-bind equation.
Measurable spaces and continuations are explicit; discrete source spaces discharge
continuation measurability without constraining the result space.
-/

public section

open MeasureTheory

universe u v

/-- A measure-valued subprobability semantics for a type constructor. -/
class EvalDistSemantics (m : Type u → Type v) where
  /-- Interpret a computation as its measure of successful outputs. -/
  denote : {α : Type u} → [MeasurableSpace α] → m α → Measure α
  /-- Successful output mass is at most one. -/
  apply_univ_le_one : ∀ {α : Type u} [MeasurableSpace α] (mx : m α),
    denote mx Set.univ ≤ 1

/-- The measure of successful outputs produced by `mx`. -/
@[expose, reducible, inline]
noncomputable def evalDist {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : Measure α :=
  EvalDistSemantics.denote mx

/-- Evaluation-measure notation. -/
notation "𝒟[" mx "]" => evalDist mx

/-- Denotation commutes with conditional choice of a computation. -/
theorem evalDist_ite {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (p : Prop) [Decidable p] (mx my : m α) :
    𝒟[if p then mx else my] = if p then 𝒟[mx] else 𝒟[my] := by
  by_cases h : p <;> simp [h]

/-- Denotation commutes with dependent conditional choice of a computation. -/
theorem evalDist_dite {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (p : Prop) [Decidable p]
    (mx : p → m α) (my : ¬p → m α) :
    𝒟[if h : p then mx h else my h] =
      if h : p then 𝒟[mx h] else 𝒟[my h] := by
  by_cases h : p <;> simp [h]

/-- The mass of an event commutes with conditional choice of a computation. -/
@[simp high]
theorem evalDist_ite_apply {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (p : Prop) [Decidable p]
    (mx my : m α) (s : Set α) :
    𝒟[if p then mx else my] s = if p then 𝒟[mx] s else 𝒟[my] s := by
  by_cases h : p <;> simp [h]

/-- Event mass commutes with dependent conditional choice of a computation. -/
@[simp high]
theorem evalDist_dite_apply {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (p : Prop) [Decidable p]
    (mx : p → m α) (my : ¬p → m α) (s : Set α) :
    𝒟[if h : p then mx h else my h] s =
      if h : p then 𝒟[mx h] s else 𝒟[my h] s := by
  by_cases h : p <;> simp [h]

theorem evalDist_apply_univ_le_one {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : 𝒟[mx] Set.univ ≤ 1 :=
  EvalDistSemantics.apply_univ_le_one mx

/-- Every computation denotation is a subprobability measure. -/
instance evalDist.instIsSubprobabilityMeasure {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : IsSubprobabilityMeasure 𝒟[mx] :=
  ⟨evalDist_apply_univ_le_one mx⟩

/-- No event of a computation has mass above one. -/
@[simp]
theorem evalDist_apply_le_one {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) (s : Set α) : 𝒟[mx] s ≤ 1 :=
  MeasureTheory.measure_le_one 𝒟[mx] s

/-- A measure-valued semantics sends `pure` to a Dirac measure. This law is separate from the
bind law because a semantics can preserve pure even when continuous effects prevent a global
measurability proof for arbitrary bind continuations. -/
class LawfulPureEvalDistSemantics (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : Prop where
  /-- `pure` denotes a Dirac measure. -/
  denote_pure {α : Type u} [MeasurableSpace α] (x : α) :
    𝒟[(pure x : m α)] = Measure.dirac x

/-- A measure-valued semantics also respects measurable `bind` in the Giry monad. -/
class LawfulEvalDistSemantics (m : Type u → Type v) [Monad m]
    [EvalDistSemantics m] : Prop extends LawfulPureEvalDistSemantics m where
  /-- Monadic bind denotes Giry bind whenever its measure-valued continuation is measurable. -/
  denote_bind {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
      (mx : m α) (f : α → m β) (hf : Measurable fun x => 𝒟[f x]) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x]

@[simp]
theorem evalDist_pure {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulPureEvalDistSemantics m] {α : Type u} [MeasurableSpace α] (x : α) :
    𝒟[(pure x : m α)] = Measure.dirac x :=
  LawfulPureEvalDistSemantics.denote_pure x

instance evalDist.instIsProbabilityMeasurePure {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulPureEvalDistSemantics m] {α : Type u}
    [MeasurableSpace α] (x : α) : IsProbabilityMeasure 𝒟[(pure x : m α)] := by
  rw [evalDist_pure]
  infer_instance

theorem evalDist_bind {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (f : α → m β) (hf : Measurable fun x => 𝒟[f x]) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x] :=
  LawfulEvalDistSemantics.denote_bind mx f hf

/-- On a discrete source type, every measure-valued continuation is measurable. -/
theorem evalDist_bind_of_discrete {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β) :
    𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x] :=
  evalDist_bind mx f Measurable.of_discrete

/-- Almost-everywhere equal measurable continuation measures give equal composed measures. -/
theorem evalDist_bind_congr_ae {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (f g : α → m β)
    (hf : Measurable fun x ↦ 𝒟[f x]) (hg : Measurable fun x ↦ 𝒟[g x])
    (h : (fun x ↦ 𝒟[f x]) =ᵐ[𝒟[mx]] fun x ↦ 𝒟[g x]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  rw [evalDist_bind mx f hf, evalDist_bind mx g hg]
  exact Measure.bind_congr_right h

/-- Pointwise equality of continuation measures gives equality after a common bind. No
measurable structure is required on the unobserved intermediate type: the common continuation
measure supplies its observation's pullback measurable space. -/
theorem evalDist_bind_congr {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace β]
    (mx : m α) (f g : α → m β) (h : ∀ x, 𝒟[f x] = 𝒟[g x]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  let : MeasurableSpace α := MeasurableSpace.comap (fun x ↦ 𝒟[f x]) inferInstance
  have hf : Measurable fun x ↦ 𝒟[f x] := comap_measurable _
  have hg : Measurable fun x ↦ 𝒟[g x] := by simpa only [← h] using hf
  exact evalDist_bind_congr_ae mx f g hf hg (Filter.Eventually.of_forall h)

/-- `Functor.map` along a measurable function denotes the pushforward measure. -/
theorem evalDist_map {m : Type u → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) {f : α → β} (hf : Measurable f) : 𝒟[f <$> mx] = 𝒟[mx].map f := by
  have hd : Measurable fun x => 𝒟[(pure (f x) : m β)] := by
    simp only [evalDist_pure]
    exact Measure.measurable_dirac.comp hf
  rw [map_eq_bind_pure_comp, evalDist_bind mx (pure ∘ f) hd]
  simp only [Function.comp_apply, evalDist_pure]
  exact Measure.bind_dirac_eq_map 𝒟[mx] hf

/-- On a discrete source type, every `Functor.map` denotes a pushforward. -/
theorem evalDist_map_of_discrete {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → β) :
    𝒟[f <$> mx] = 𝒟[mx].map f :=
  evalDist_map mx Measurable.of_discrete

/-- Independent sequential draws denote Mathlib's product measure. -/
theorem evalDist_pair {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (my : m β) :
    𝒟[do let x ← mx; let y ← my; return (x, y)] = 𝒟[mx].prod 𝒟[my] := by
  have h (x : α) :
      𝒟[my >>= fun y => pure (x, y)] = (𝒟[my]).map (Prod.mk x) := by
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      (evalDist_map my (measurable_const.prodMk measurable_id :
        Measurable (Prod.mk x : β → α × β)))
  rw [evalDist_bind mx _ (by simpa only [h] using
    (Measurable.map_prodMk_left (ν := 𝒟[my])))]
  simp only [h, Measure.prod]

/-- A constant continuation scales the continuation's measure by the success mass
(`Measure.bind_const`); the measure form of `probOutput_bind_const`. -/
@[simp]
theorem evalDist_bind_const {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (my : m β) : 𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my] := by
  rw [evalDist_bind mx (fun _ => my) measurable_const, Measure.bind_const]

/-- A constant map denotes the success mass at a point (`Measure.map_const`); the measure form
of `probOutput_map_const`. -/
@[simp]
theorem evalDist_map_const {m : Type u → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (c : β) : 𝒟[(fun _ => c) <$> mx] = 𝒟[mx] Set.univ • Measure.dirac c := by
  rw [evalDist_map mx measurable_const, Measure.map_const]

/-- An AE-measurable valuation of composed outputs satisfies the integral tower law. -/
theorem lintegral_evalDist_bind_of_aemeasurable {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β)
    (hf : Measurable fun x ↦ 𝒟[f x]) {g : β → ENNReal}
    (hg : AEMeasurable g 𝒟[mx >>= f]) :
    ∫⁻ y, g y ∂𝒟[mx >>= f] = ∫⁻ x, ∫⁻ y, g y ∂𝒟[f x] ∂𝒟[mx] := by
  rw [evalDist_bind mx f hf] at hg ⊢
  exact Measure.lintegral_bind hf.aemeasurable hg

/-- Integrating a bind first integrates each measurable continuation, then its common draw. -/
theorem lintegral_evalDist_bind {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [MeasurableSpace β] (mx : m α) (f : α → m β)
    (hf : Measurable fun x ↦ 𝒟[f x]) {g : β → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂𝒟[mx >>= f] = ∫⁻ x, ∫⁻ y, g y ∂𝒟[f x] ∂𝒟[mx] := by
  exact lintegral_evalDist_bind_of_aemeasurable mx f hf hg.aemeasurable

/-- For a discrete common draw, the tower law needs no continuation measurability proof. -/
theorem lintegral_evalDist_bind_of_discrete {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β)
    {g : β → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂𝒟[mx >>= f] = ∫⁻ x, ∫⁻ y, g y ∂𝒟[f x] ∂𝒟[mx] :=
  lintegral_evalDist_bind mx f .of_discrete hg

/-- An AE-measurable valuation of a measurable output map integrates the composed functional. -/
theorem lintegral_evalDist_map_of_aemeasurable {m : Type u → Type v} [Monad m]
    [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β] (mx : m α)
    {f : α → β} (hf : Measurable f) {g : β → ENNReal}
    (hg : AEMeasurable g 𝒟[f <$> mx]) :
    ∫⁻ y, g y ∂𝒟[f <$> mx] = ∫⁻ x, g (f x) ∂𝒟[mx] := by
  rw [evalDist_map mx hf] at hg ⊢
  exact lintegral_map' hg hf.aemeasurable

/-- Integrating a measurable output map integrates the composed functional. -/
theorem lintegral_evalDist_map {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [MeasurableSpace β] (mx : m α) {f : α → β} (hf : Measurable f) {g : β → ENNReal}
    (hg : Measurable g) : ∫⁻ y, g y ∂𝒟[f <$> mx] = ∫⁻ x, g (f x) ∂𝒟[mx] := by
  exact lintegral_evalDist_map_of_aemeasurable mx hf hg.aemeasurable

/-- On discrete source and target spaces, output-map integration needs no measurability
proofs. -/
@[simp high]
theorem lintegral_evalDist_map_of_discrete {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (mx : m α) (f : α → β) (g : β → ENNReal) :
    ∫⁻ y, g y ∂𝒟[f <$> mx] = ∫⁻ x, g (f x) ∂𝒟[mx] :=
  lintegral_evalDist_map mx .of_discrete .of_discrete

/-- Adding to a natural-valued observation adds the constant scaled by the successful output
mass. The observed computation's intermediate result needs no measurable-space instance. -/
@[simp high + 1]
theorem lintegral_evalDist_map_add_nat {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    (mx : m α) (f : α → ℕ) (c : ℕ) :
    (∫⁻ n, (n : ENNReal) ∂𝒟[(fun x ↦ f x + c) <$> mx]) =
      (∫⁻ n, (n : ENNReal) ∂𝒟[f <$> mx]) + c * 𝒟[f <$> mx] Set.univ := by
  rw [show (fun x ↦ f x + c) <$> mx =
    (fun n : ℕ ↦ n + c) <$> (f <$> mx) by simp [Functor.map_map],
    lintegral_evalDist_map_of_discrete]
  simp [lintegral_add_right]

/-- Adding a fixed natural to an observed count scales that increment by successful mass.
The curried addition form supplies a binder-free pattern for `grind`. -/
@[grind =]
theorem lintegral_evalDist_map_const_add_nat {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    (mx : m α) (f : α → ℕ) (c : ℕ) :
    (∫⁻ n, (n : ENNReal) ∂𝒟[Nat.add c <$> (f <$> mx)]) =
      (∫⁻ n, (n : ENNReal) ∂𝒟[f <$> mx]) + c * 𝒟[f <$> mx] Set.univ := by
  simpa only [Functor.map_map, Function.comp_def, Nat.add_eq, Nat.add_comm] using
    lintegral_evalDist_map_add_nat mx f c

/-- The success mass of a bind is the integral of its continuation's success mass. -/
theorem evalDist_bind_apply_univ {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) (f : α → m β) (hf : Measurable fun x ↦ 𝒟[f x]) :
    𝒟[mx >>= f] Set.univ = ∫⁻ x, 𝒟[f x] Set.univ ∂𝒟[mx] := by
  rw [evalDist_bind mx f hf, Measure.bind_apply MeasurableSet.univ hf.aemeasurable]

/-- A measurable map preserves the successful-output mass. -/
theorem evalDist_map_apply_univ {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) {f : α → β} (hf : Measurable f) :
    𝒟[f <$> mx] Set.univ = 𝒟[mx] Set.univ := by
  rw [evalDist_map mx hf, Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

/-- Implication between Boolean results bounds their pure successful masses. -/
theorem evalDist_pure_apply_le_of_imp {m : Type → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    (a b : Bool) (h : a = true → b = true) :
    𝒟[(pure a : m Bool)] {true} ≤ 𝒟[(pure b : m Bool)] {true} := by
  cases a <;> cases b <;> simp_all

/-- A pure Boolean result covered by either of two results has mass bounded by their sum. -/
theorem evalDist_pure_apply_le_add_of_imp {m : Type → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    (a b c : Bool) (h : a = true → b = true ∨ c = true) :
    𝒟[(pure a : m Bool)] {true} ≤
      𝒟[(pure b : m Bool)] {true} + 𝒟[(pure c : m Bool)] {true} := by
  cases a <;> cases b <;> cases c <;> simp_all
