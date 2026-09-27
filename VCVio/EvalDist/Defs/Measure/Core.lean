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
continuation measurability without constraining the result space.  The closing section states
the laws of the average `∫⁻ r, r ∂𝒟[f <$> mx]` of a scalar observation, all but one of
which need no measurable space on the observed type.
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

@[simp]
theorem evalDist_apply_univ_le_one {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : 𝒟[mx] Set.univ ≤ 1 :=
  EvalDistSemantics.apply_univ_le_one mx

/-- Every computation denotation is a subprobability measure. -/
instance evalDist.instIsSubprobabilityMeasure {m : Type u → Type v} [EvalDistSemantics m]
    {α : Type u} [MeasurableSpace α] (mx : m α) : IsSubprobabilityMeasure 𝒟[mx] :=
  ⟨evalDist_apply_univ_le_one mx⟩

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

/-- Pointwise equality of continuation measures gives equality after a common bind. The
intermediate type uses a local discrete measurable space, so callers need no measurable-space
instance for it. -/
theorem evalDist_bind_congr {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace β]
    (mx : m α) (f g : α → m β) (h : ∀ x, 𝒟[f x] = 𝒟[g x]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  let : MeasurableSpace α := ⊤
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  exact Measure.bind_congr_right (Filter.Eventually.of_forall h)

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

/-- Integrating a bind first integrates each measurable continuation, then its common draw. -/
theorem lintegral_evalDist_bind {m : Type u → Type v} [Monad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [MeasurableSpace β] (mx : m α) (f : α → m β)
    (hf : Measurable fun x ↦ 𝒟[f x]) {g : β → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂𝒟[mx >>= f] = ∫⁻ x, ∫⁻ y, g y ∂𝒟[f x] ∂𝒟[mx] := by
  rw [evalDist_bind mx f hf, Measure.lintegral_bind hf.aemeasurable hg.aemeasurable]

/-- For a discrete common draw, the tower law needs no continuation measurability proof. -/
theorem lintegral_evalDist_bind_of_discrete {m : Type u → Type v} [Monad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β)
    {g : β → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂𝒟[mx >>= f] = ∫⁻ x, ∫⁻ y, g y ∂𝒟[f x] ∂𝒟[mx] :=
  lintegral_evalDist_bind mx f .of_discrete hg

/-- Integrating a measurable output map integrates the composed functional. -/
theorem lintegral_evalDist_map {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α]
    [MeasurableSpace β] (mx : m α) {f : α → β} (hf : Measurable f) {g : β → ENNReal}
    (hg : Measurable g) : ∫⁻ y, g y ∂𝒟[f <$> mx] = ∫⁻ x, g (f x) ∂𝒟[mx] := by
  rw [evalDist_map mx hf, lintegral_map hg hf]

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
    {α β : Type u} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β] (mx : m α) (f : α → m β) :
    𝒟[mx >>= f] Set.univ = ∫⁻ x, 𝒟[f x] Set.univ ∂𝒟[mx] := by
  rw [evalDist_bind_of_discrete mx f,
    Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]

/-- A measurable map preserves the successful-output mass. -/
theorem evalDist_map_apply_univ {m : Type u → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (mx : m α) {f : α → β} (hf : Measurable f) :
    𝒟[f <$> mx] Set.univ = 𝒟[mx] Set.univ := by
  rw [evalDist_map mx hf, Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

/-! ## Averages of a scalar observation

`∫⁻ r, r ∂𝒟[f <$> mx]` is the average of `f : α → ℝ≥0∞` over the successful outputs of `mx`.
Pushing `f` through the computation before integrating means only `ENNReal` needs a measurable
space: apart from `lintegral_id_evalDist_map`, which relates the average to an integral against
`𝒟[mx]` and so needs a discrete measurable space on `α`, none of these statements constrains
`α` with an instance.  Under `MeasureProgramLogic.toMAlgOrdered` this average is the quantitative
weakest precondition `wp mx f`, whose laws in `VCVio.ProgramLogic.Unary.WP.Measure` are stated
at a discrete measurable space on `α`. -/

/-- Averaging a scalar observation is integrating it against the observed computation's
measure, at any discrete measurable space on the output type. -/
theorem lintegral_id_evalDist_map {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (mx : m α) (f : α → ENNReal) :
    ∫⁻ r, r ∂𝒟[f <$> mx] = ∫⁻ x, f x ∂𝒟[mx] :=
  lintegral_evalDist_map mx .of_discrete measurable_id

/-- A uniform bound on a scalar observation bounds its average. -/
theorem lintegral_id_evalDist_map_le_of_le {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    {f : α → ENNReal} {c : ENNReal} (hf : ∀ x, f x ≤ c) : ∫⁻ r, r ∂𝒟[f <$> mx] ≤ c := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map]
  calc ∫⁻ x, f x ∂𝒟[mx] ≤ ∫⁻ _, c ∂𝒟[mx] := lintegral_mono hf
    _ = c * 𝒟[mx] Set.univ := lintegral_const c
    _ ≤ c := mul_le_of_le_one_right' (evalDist_apply_univ_le_one mx)

/-- Averaging a scalar observation is monotone in the observation. -/
theorem lintegral_id_evalDist_map_mono {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    {f g : α → ENNReal} (hfg : ∀ x, f x ≤ g x) :
    ∫⁻ r, r ∂𝒟[f <$> mx] ≤ ∫⁻ r, r ∂𝒟[g <$> mx] := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
  exact lintegral_mono hfg

/-- Averaging a scalar observation is additive in the observation. -/
theorem lintegral_id_evalDist_map_add {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α)
    (f g : α → ENNReal) :
    ∫⁻ r, r ∂𝒟[(fun x ↦ f x + g x) <$> mx] =
      (∫⁻ r, r ∂𝒟[f <$> mx]) + ∫⁻ r, r ∂𝒟[g <$> mx] := by
  let _ : MeasurableSpace α := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map, lintegral_id_evalDist_map,
    lintegral_add_left Measurable.of_discrete]

/-- The constant-zero observation averages to zero. -/
theorem lintegral_id_evalDist_map_zero {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α) :
    ∫⁻ r, r ∂𝒟[(fun _ ↦ (0 : ENNReal)) <$> mx] = 0 :=
  le_zero_iff.mp (lintegral_id_evalDist_map_le_of_le mx fun _ ↦ le_rfl)

/-- **The tower law for averages.**  Averaging an observation of a bind averages, over the
head's outputs, the average of that observation over the continuation. -/
theorem lintegral_id_evalDist_map_bind {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type} (mx : m α)
    (g : α → m β) (f : β → ENNReal) :
    ∫⁻ r, r ∂𝒟[f <$> (mx >>= g)] = ∫⁻ r, r ∂𝒟[(fun x ↦ ∫⁻ r, r ∂𝒟[f <$> g x]) <$> mx] := by
  let _ : MeasurableSpace α := ⊤
  let _ : MeasurableSpace β := ⊤
  rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map,
    lintegral_evalDist_bind_of_discrete mx g (g := f) Measurable.of_discrete]
  simp only [lintegral_id_evalDist_map]
