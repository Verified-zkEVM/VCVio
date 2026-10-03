/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.Defs.Measure.Core
public import PolyFun.Control.Monad.Algebra.WP

/-!
# Expectations of computations

Under lawful measure semantics a computation `mx : m α` has an expectation for every
nonnegative observation `g : α → ℝ≥0∞`: the integral of `g` against the successful-output
measure of `mx`. It is core's weakest precondition `wp mx g ⊥` under the measure interpretation
`wpMonad m`, written `wp⟦mx⟧ g`; `𝔼{let x ← mx}[g x]` (`VCVio.EvalDist.ProbabilityNotation`)
writes it through a `do` sequence. The interpretation is exact (`ExactWPMonad`), so `simp`
distributes `wp⟦·⟧ ` over `pure`, `bind`, and `map` with core's own equations; the laws below
relate it to Mathlib's lintegral and to the order and arithmetic of `ℝ≥0∞`.

The laws need no measurable structure on the outputs: when an argument integrates, it selects
the σ-algebra that the observation itself induces. `wp_eq_lintegral` states the integral form
for a chosen output space.

`ExpectationWP m EPred` names the expectation interpretation of a monad. A monad with lawful
measure semantics is interpreted by `wpMonad m`, and `OptionT m` and `ExceptT ε m` by core's lift
of the base monad's interpretation. A transformer stack therefore has a single `wp`, which core's
transformer rules decompose and whose exception assertions are those of the stack's layers.
-/

public section

open MeasureTheory Std.WP
open scoped ENNReal

universe v

/-! ## Indicators -/

open scoped Classical in
/-- The indicator of a proposition in the expectation carrier: `1` if it holds and `0`
otherwise. -/
@[expose] noncomputable def propInd (P : Prop) : ℝ≥0∞ := if P then 1 else 0

@[simp] theorem propInd_true : propInd True = 1 := ite_eq_left trivial
@[simp] theorem propInd_false : propInd False = 0 := ite_eq_right id

theorem propInd_eq_ite {P : Prop} [Decidable P] : propInd P = if P then 1 else 0 := by
  simp [propInd]

open scoped Classical in
theorem propInd_and {P Q : Prop} : propInd (P ∧ Q) = propInd P * propInd Q := by
  unfold propInd; split_ifs <;> simp_all

/-- A product of indicators is the indicator of the conjunction. -/
@[simp, grind norm]
theorem propInd_mul_propInd {P Q : Prop} : propInd P * propInd Q = propInd (P ∧ Q) :=
  propInd_and.symm

open scoped Classical in
@[gcongr] theorem propInd_mono {P Q : Prop} (h : P → Q) : propInd P ≤ propInd Q := by
  unfold propInd; split_ifs <;> simp_all

theorem propInd_le_one (P : Prop) : propInd P ≤ 1 := by
  unfold propInd; split_ifs <;> simp

open scoped Classical in
theorem propInd_eq_one_iff {P : Prop} : propInd P = 1 ↔ P := by simp [propInd]

open scoped Classical in
theorem propInd_eq_zero_iff {P : Prop} : propInd P = 0 ↔ ¬P := by simp [propInd]

open scoped Classical in
/-- An indicator reaches `1` exactly when its proposition holds: the verification condition a
lower-bound triple leaves at an indicator postcondition. -/
@[simp]
theorem one_le_propInd_iff {P : Prop} : 1 ≤ propInd P ↔ P := by
  unfold propInd; split_ifs with h <;> simp [h]

open scoped Classical in
theorem propInd_or_le {P Q : Prop} : propInd (P ∨ Q) ≤ propInd P + propInd Q := by
  unfold propInd; split_ifs <;> simp_all

open scoped Classical in
theorem propInd_not {P : Prop} : propInd (¬P) = 1 - propInd P := by
  unfold propInd; split_ifs <;> simp_all

/-- The indicator of a predicate as an observation: `1` where the predicate holds and `0`
elsewhere. An event is the expectation of `predInd p`, so its predicate is an argument that
`simp` and `grind` can match. -/
@[expose] noncomputable def predInd {α : Type*} (p : α → Prop) : α → ℝ≥0∞ := fun x ↦ propInd (p x)

@[simp, grind norm] theorem predInd_apply {α : Type*} (p : α → Prop) (a : α) :
    predInd p a = propInd (p a) := rfl

open scoped Classical in
/-- A weighted sum of the indicators of one point is the weight at that point. -/
@[simp]
theorem tsum_propInd_eq_mul {α : Type*} (a : α) (f : α → ℝ≥0∞) :
    ∑' x, propInd (a = x) * f x = f a := by
  simp [propInd_eq_ite]

open scoped Classical in
/-- A weighted sum of the indicators of one point is the weight at that point. -/
@[simp]
theorem tsum_propInd_eq_mul' {α : Type*} (a : α) (f : α → ℝ≥0∞) :
    ∑' x, propInd (x = a) * f x = f a := by
  simp [propInd_eq_ite]

/-! ## The measure interpretation -/

namespace ExpectationWP

variable (m : Type → Type v) [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- The ordered algebra of nonnegative expectations under successful-output measures. -/
@[expose, instance_reducible]
noncomputable def algebra : MAlgOrdered m ℝ≥0∞ where
  μ mx := ∫⁻ x, x ∂𝒟[mx]
  μ_pure x := by simp
  μ_bind_mono {α} f g hfg mx := by
    let obs : α → Measure ℝ≥0∞ × Measure ℝ≥0∞ := fun a ↦ (𝒟[f a], 𝒟[g a])
    let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
    have hobs : Measurable obs := comap_measurable obs
    rw [lintegral_evalDist_bind mx f (measurable_fst.comp hobs)
      (g := fun x ↦ x) measurable_id,
      lintegral_evalDist_bind mx g (measurable_snd.comp hobs)
        (g := fun x ↦ x) measurable_id]
    exact lintegral_mono hfg

/-- Core weakest preconditions under successful-output measures: `wp mx g ⊥` is the expectation
of `g` over the outputs of `mx`. -/
@[expose, reducible]
noncomputable def wpMonad [LawfulMonad m] : WPMonad m ℝ≥0∞ EStack⟨⟩ :=
  @MAlgOrdered.toWPMonad m ℝ≥0∞ _ _ (algebra m) _

end ExpectationWP

/-! ## Expectation interpretations

`ExpectationWP m EPred` is the expectation interpretation of `m`: an exact core `WPMonad` over
`ℝ≥0∞` whose exception assertions `EPred` are those of `m`'s transformer stack. A monad with
lawful measure semantics is interpreted by its successful-output measures (`ofMeasure`, the
interpretation `wpMonad m`, with no exception layer). `OptionT m` and `ExceptT ε m` are
interpreted by core's lifts of `m`'s interpretation, which take precedence over the stack's own
measure interpretation. On a stack, `wp⟦x⟧ g` is the weakest precondition that core's transformer
rules decompose, and `OptionT.wp_apply_eq` and `ExceptT.wp_apply_eq` read it as an expectation
over the run. -/

/-- The expectation interpretation of `m`: exact core weakest preconditions over `ℝ≥0∞`, with the
exception assertions `EPred` of `m`'s stack.

The class states no law relating `wp` to an output measure, so the instance found for a monad is
what fixes the meaning of `Pr{…}[…]` and `𝔼{…}[…]` there. `ofMeasure` is the successful-output
measure of a monad with lawful measure semantics, and on `OptionT` and `ExceptT` the lifts, which
take precedence, agree with it by `OptionT.wp_ofMeasure_eq` and `ExceptT.wp_ofMeasure_eq`. -/
class ExpectationWP (m : Type → Type v) [Monad m] (EPred : outParam Type) [Assertion EPred] where
  /-- The interpretation. -/
  toWPMonad : WPMonad m ℝ≥0∞ EPred
  /-- The interpretation distributes over `pure` and `bind` as equations. -/
  exact : @ExactWPMonad m ℝ≥0∞ EPred _ _ _ toWPMonad

namespace ExpectationWP

/-- A monad with lawful measure semantics is interpreted by its successful-output measures. -/
noncomputable instance (priority := low) ofMeasure (m : Type → Type v) [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] : ExpectationWP m EStack⟨⟩ where
  toWPMonad := wpMonad m
  exact := letI := wpMonad m; inferInstance

set_option warn.classDefReducibility false in
/-- Core's `OptionT` lift of an interpretation over `ℝ≥0∞`, wrapped in a definition so that
`simp` keeps a lifted expectation over the `OptionT` computation: core's `OptionT.wp_apply_eq`
does not fire on it, and `wp_liftOptionT_apply` rewrites it to an expectation over the run on
request. The definition is semireducible on purpose. `vcgen` unfolds it to match core's rules,
while `simp` matches instances only up to instance reducibility and so leaves it folded. -/
noncomputable def liftOptionT (m : Type → Type v) [Monad m] {EPred : Type} [Assertion EPred]
    (base : WPMonad m ℝ≥0∞ EPred) : WPMonad (OptionT m) ℝ≥0∞ ((Unit → ℝ≥0∞) × EPred) :=
  @OptionT.instWPMonad m EPred ℝ≥0∞ _ _ _ base

/-- The lift of an interpretation reads an optional computation through its run (core's
`OptionT.wp_apply_eq`). -/
theorem wp_liftOptionT_apply (m : Type → Type v) [Monad m] {EPred : Type} [Assertion EPred]
    (base : WPMonad m ℝ≥0∞ EPred) {α : Type} (x : OptionT m α) (post : α → ℝ≥0∞)
    (epost : (Unit → ℝ≥0∞) × EPred) :
    @WP.wp _ _ _ _ _ _ (@instWPOfWPMonad _ _ _ _ _ _ _ (liftOptionT m base)) x post epost =
      @WP.wp _ _ _ _ _ _ (@instWPOfWPMonad _ _ _ _ _ _ _ base) x.run
        (Lean.Order.pushOption post epost.1) epost.2 := by
  unfold liftOptionT
  exact OptionT.wp_apply_eq x post epost

set_option warn.classDefReducibility false in
/-- Core's `ExceptT` lift of an interpretation over `ℝ≥0∞`, wrapped as `liftOptionT` is. -/
noncomputable def liftExceptT (m : Type → Type v) [Monad m] (ε : Type) {EPred : Type}
    [Assertion EPred] (base : WPMonad m ℝ≥0∞ EPred) :
    WPMonad (ExceptT ε m) ℝ≥0∞ ((ε → ℝ≥0∞) × EPred) :=
  @ExceptT.instWPMonad m EPred ε ℝ≥0∞ _ _ _ base

/-- The lift of an interpretation reads an exceptional computation through its run (core's
`ExceptT.wp_apply_eq`). -/
theorem wp_liftExceptT_apply (m : Type → Type v) [Monad m] (ε : Type) {EPred : Type}
    [Assertion EPred] (base : WPMonad m ℝ≥0∞ EPred) {α : Type} (x : ExceptT ε m α)
    (post : α → ℝ≥0∞) (epost : (ε → ℝ≥0∞) × EPred) :
    @WP.wp _ _ _ _ _ _ (@instWPOfWPMonad _ _ _ _ _ _ _ (liftExceptT m ε base)) x post epost =
      @WP.wp _ _ _ _ _ _ (@instWPOfWPMonad _ _ _ _ _ _ _ base) x.run
        (Lean.Order.pushExcept post epost.1) epost.2 := by
  unfold liftExceptT
  exact ExceptT.wp_apply_eq x post epost

/-- `OptionT m` is interpreted by core's lift of `m`'s interpretation: failure is an exception
assertion, and the expectation of a successful output is read over the run. -/
noncomputable instance optionT (m : Type → Type v) [Monad m] {EPred : Type} [Assertion EPred]
    [ExpectationWP m EPred] : ExpectationWP (OptionT m) ((Unit → ℝ≥0∞) × EPred) where
  toWPMonad := liftOptionT m (toWPMonad (m := m))
  exact := by
    unfold liftOptionT
    let : WPMonad m ℝ≥0∞ EPred := toWPMonad (m := m)
    have : ExactWPMonad m ℝ≥0∞ EPred := exact (m := m)
    infer_instance

/-- `ExceptT ε m` is interpreted by core's lift of `m`'s interpretation. -/
noncomputable instance exceptT (m : Type → Type v) [Monad m] {ε : Type} {EPred : Type}
    [Assertion EPred] [ExpectationWP m EPred] :
    ExpectationWP (ExceptT ε m) ((ε → ℝ≥0∞) × EPred) where
  toWPMonad := liftExceptT m ε (toWPMonad (m := m))
  exact := by
    unfold liftExceptT
    let : WPMonad m ℝ≥0∞ EPred := toWPMonad (m := m)
    have : ExactWPMonad m ℝ≥0∞ EPred := exact (m := m)
    infer_instance

/-- The expectation carrier is a chain-complete partial order, as core's assertion lattices are:
the bottom exception assertion of a transformer stack over `ℝ≥0∞` elaborates without opening
`Std.WP`'s scope. -/
noncomputable instance instCCPOENNReal : Lean.Order.CCPO ℝ≥0∞ :=
  Lean.Order.instCCPOOfCompleteLattice

/-- The exactness of an expectation interpretation, for instance search. -/
instance instExactWPMonad (m : Type → Type v) [Monad m] {EPred : Type} [Assertion EPred]
    [inst : ExpectationWP m EPred] : @ExactWPMonad m ℝ≥0∞ EPred _ _ _ inst.toWPMonad :=
  inst.exact

/-! ### The bottom assertion of a stack

A stack's exception assertions are products of function assertions over the base's; the bottom
exception assertion `⊥` that `wp⟦·⟧` passes charges every failure `0`. -/

/-- The bottom of a product of assertions is the pair of bottoms. -/
theorem bot_eq_prod {A B : Type} [Lean.Order.CCPO A] [Lean.Order.CCPO B] :
    (Lean.Order.bot : A × B) = (Lean.Order.bot, Lean.Order.bot) :=
  Lean.Order.PartialOrder.rel_antisymm (Lean.Order.bot_le _)
    (show Lean.Order.PartialOrder.rel (Lean.Order.bot : A) (Lean.Order.bot : A × B).1 ∧
        Lean.Order.PartialOrder.rel (Lean.Order.bot : B) (Lean.Order.bot : A × B).2 from
      ⟨Lean.Order.bot_le _, Lean.Order.bot_le _⟩)

/-- The first component of the bottom of a product of assertions. -/
@[simp]
theorem bot_fst {A B : Type} [Lean.Order.CCPO A] [Lean.Order.CCPO B] :
    (Lean.Order.bot : A × B).1 = Lean.Order.bot :=
  congrArg Prod.fst bot_eq_prod

/-- The second component of the bottom of a product of assertions. -/
@[simp]
theorem bot_snd {A B : Type} [Lean.Order.CCPO A] [Lean.Order.CCPO B] :
    (Lean.Order.bot : A × B).2 = Lean.Order.bot :=
  congrArg Prod.snd bot_eq_prod

/-- The bottom of the expectation carrier is `0`. -/
@[simp]
theorem bot_eq_zero : (Lean.Order.bot : ℝ≥0∞) = 0 :=
  Lean.Order.PartialOrder.rel_antisymm (Lean.Order.bot_le 0) (show (0 : ℝ≥0∞) ≤ _ from zero_le)

end ExpectationWP

/-- The expectation `wp⟦mx⟧ g` of `g` over the outputs of `mx`: core's `wp mx g ⊥` under the
expectation interpretation `ExpectationWP` of `mx`'s monad. Standalone, `wp⟦mx⟧ ` is the
function `fun g => wp⟦mx⟧ g`.

The notation writes its `WP` instance as `Std.WP.instWPOfWPMonad` applied to the interpretation.
Core's generic `wp` laws produce that instance term on their right-hand sides, so an expectation
written with the notation and one produced by normalization carry the same instance. -/
syntax:max (name := measureWpStx) "wp⟦" term "⟧ " : term

@[inherit_doc measureWpStx]
syntax:max (name := measureWpAppStx) "wp⟦" term "⟧ " term:max : term

macro_rules
  | `(wp⟦ $mx ⟧ $g:term) =>
    `(@Std.WP.WP.wp _ _ ENNReal _ _ _
      (@Std.WP.instWPOfWPMonad _ ENNReal _ _ _ _ _
        (ExpectationWP.toWPMonad (m := _))) $mx $g
      Lean.Order.bot)
  | `(wp⟦ $mx ⟧) => `(fun g => wp⟦ $mx ⟧ g)

namespace ExpectationWP

section Exact

variable {m : Type → Type v} [Monad m] {EPred : Type} [Assertion EPred] [ExpectationWP m EPred]
  {α : Type}

/-- The expectation of a returned value is the observation at that value. -/
@[grind norm]
theorem wp_pure (a : α) (g : α → ℝ≥0∞) : wp⟦(pure a : m α)⟧ g = g a :=
  letI := toWPMonad (m := m)
  letI := exact (m := m)
  ExactWPMonad.wp_pure a g _

/-- The expectation after a bind is the expectation of the continuations' expectations. -/
@[grind norm]
theorem wp_bind {β : Type} (mx : m α) (f : α → m β) (g : β → ℝ≥0∞) :
    wp⟦mx >>= f⟧ g = wp⟦mx⟧ fun a => wp⟦f a⟧ g :=
  letI := toWPMonad (m := m)
  letI := exact (m := m)
  ExactWPMonad.wp_bind mx f g _

/-- The expectation of mapped outputs is the expectation of the composed observation. -/
@[grind norm]
theorem wp_map {β : Type} (f : α → β) (mx : m α) (g : β → ℝ≥0∞) :
    wp⟦f <$> mx⟧ g = wp⟦mx⟧ fun a => g (f a) :=
  letI := toWPMonad (m := m)
  letI := exact (m := m)
  ExactWPMonad.wp_map f mx g _

/-- Observations that agree on every output have the same expectation. -/
theorem wp_congr (mx : m α) {f g : α → ℝ≥0∞} (hfg : ∀ x, f x = g x) :
    wp⟦mx⟧ f = wp⟦mx⟧ g := by
  rw [show f = g from funext hfg]

end Exact

section Laws

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α : Type}

omit [LawfulMonad m] in
/-- The expectation algebra integrates its actual nonnegative output. -/
theorem μ_algebra (mx : m ℝ≥0∞) :
    (algebra m).μ mx = ∫⁻ x, x ∂𝒟[mx] := rfl

/-- An expectation integrates the observation's image measure. -/
theorem wp_eq_lintegral_map (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = ∫⁻ y, y ∂𝒟[g <$> mx] := by
  change (algebra m).μ (mx >>= fun a => pure (g a)) = _
  rw [bind_pure_comp]
  rfl

/-- An expectation is the integral of a measurable observation. -/
theorem wp_eq_lintegral [MeasurableSpace α] (mx : m α) (g : α → ℝ≥0∞) (hg : Measurable g) :
    wp⟦mx⟧ g = ∫⁻ x, g x ∂𝒟[mx] := by
  have hf : Measurable (fun x ↦ 𝒟[(pure (g x) : m ℝ≥0∞)]) := by
    simpa only [evalDist_pure, Function.comp_def] using Measure.measurable_dirac.comp hg
  change (algebra m).μ (mx >>= fun x ↦ pure (g x)) = _
  rw [μ_algebra,
    lintegral_evalDist_bind mx (fun x ↦ pure (g x)) hf (g := fun y ↦ y) measurable_id]
  simp

/-- An expectation is the integral of its observation in the σ-algebra the observation
induces, so no measurable structure on the outputs is needed. -/
theorem wp_eq_lintegral_comap (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = @lintegral α (MeasurableSpace.comap g inferInstance)
      (@evalDist m _ α (MeasurableSpace.comap g inferInstance) mx) g := by
  let : MeasurableSpace α := MeasurableSpace.comap g inferInstance
  exact wp_eq_lintegral mx g (comap_measurable g)

/-- Pointwise comparison of observations is understood by generalized congruence; the comparison
on possible outputs, `wp_mono_of_support`, takes precedence. -/
@[gcongr low]
theorem wp_mono (mx : m α) {f g : α → ℝ≥0∞} (hfg : ∀ x, f x ≤ g x) : wp⟦mx⟧ f ≤ wp⟦mx⟧ g :=
  @MAlgOrdered.μ_bind_pure_mono m ℝ≥0∞ _ _ (algebra m) α mx f g hfg

/-- The zero observation has expectation zero. -/
@[simp]
theorem wp_zero (mx : m α) : wp⟦mx⟧ (fun _ ↦ 0) = 0 := by
  let : MeasurableSpace α := ⊤
  rw [wp_eq_lintegral mx _ measurable_const, lintegral_zero]

/-- Expectation is additive. -/
theorem wp_add (mx : m α) (f g : α → ℝ≥0∞) :
    wp⟦mx⟧ (fun x ↦ f x + g x) = wp⟦mx⟧ f + wp⟦mx⟧ g := by
  let obs : α → ℝ≥0∞ × ℝ≥0∞ := fun a ↦ (f a, g a)
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hf : Measurable f := measurable_fst.comp (comap_measurable obs)
  have hg : Measurable g := measurable_snd.comp (comap_measurable obs)
  rw [wp_eq_lintegral mx (fun x ↦ f x + g x) (hf.add hg), wp_eq_lintegral mx f hf,
    wp_eq_lintegral mx g hg, lintegral_add_left hf]

/-- A constant factor on the right of an observation factors out of its expectation. -/
theorem wp_mul_const (mx : m α) (g : α → ℝ≥0∞) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun x ↦ g x * c) = wp⟦mx⟧ g * c := by
  let : MeasurableSpace α := MeasurableSpace.comap g inferInstance
  have hg : Measurable g := comap_measurable g
  rw [wp_eq_lintegral mx _ (hg.mul_const c), wp_eq_lintegral mx g hg, lintegral_mul_const c hg]

/-- A constant factor on the left of an observation factors out of its expectation. -/
theorem wp_const_mul (mx : m α) (c : ℝ≥0∞) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ (fun x ↦ c * g x) = c * wp⟦mx⟧ g := by
  simpa only [mul_comm] using wp_mul_const mx g c

/-- Finite sums of observations commute with expectation. -/
theorem wp_finsetSum {κ : Type*} (mx : m α) (s : Finset κ) (f : κ → α → ℝ≥0∞) :
    wp⟦mx⟧ (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, wp⟦mx⟧ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [wp_add, ih]

/-- Almost-everywhere comparison suffices for measurable observations. -/
theorem wp_mono_ae [MeasurableSpace α] (mx : m α) {f g : α → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ g x) : wp⟦mx⟧ f ≤ wp⟦mx⟧ g := by
  rw [wp_eq_lintegral mx _ hf, wp_eq_lintegral mx _ hg]
  exact lintegral_mono_ae hfg

/-- Monotone convergence for expectations of measurable observations. -/
theorem wp_iSup [MeasurableSpace α] (mx : m α) (f : ℕ → α → ℝ≥0∞) (hf : Monotone f)
    (hmeas : ∀ n, Measurable (f n)) :
    wp⟦mx⟧ (fun x ↦ ⨆ n, f n x) = ⨆ n, wp⟦mx⟧ (f n) := by
  rw [wp_eq_lintegral mx _ (Measurable.iSup hmeas), lintegral_iSup hmeas hf]
  simp only [wp_eq_lintegral mx _ (hmeas _)]

/-- Bounding a measurable observation almost everywhere bounds its expectation by the bound
times the success mass. -/
theorem wp_le_mul_mass [MeasurableSpace α] (mx : m α) {g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hmeas : Measurable g) (hg : ∀ᵐ x ∂𝒟[mx], g x ≤ c) :
    wp⟦mx⟧ g ≤ c * 𝒟[mx] Set.univ := by
  rw [wp_eq_lintegral mx _ hmeas]
  exact (lintegral_mono_ae hg).trans_eq (lintegral_const c)

/-- Bounding a measurable observation almost everywhere bounds its expectation. -/
theorem wp_le_const [MeasurableSpace α] (mx : m α) {g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hmeas : Measurable g) (hg : ∀ᵐ x ∂𝒟[mx], g x ≤ c) : wp⟦mx⟧ g ≤ c :=
  (wp_le_mul_mass mx hmeas hg).trans <|
    (mul_le_mul' le_rfl (evalDist_apply_univ_le_one mx)).trans_eq (mul_one c)

/-- An additive almost-everywhere comparison retains the success-mass factor of the constant. -/
theorem wp_le_const_mul_mass_add [MeasurableSpace α] (mx : m α) {f g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∀ᵐ x ∂𝒟[mx], f x ≤ c + g x) :
    wp⟦mx⟧ f ≤ c * 𝒟[mx] Set.univ + wp⟦mx⟧ g := by
  rw [wp_eq_lintegral mx _ hf, wp_eq_lintegral mx _ hg]
  exact (lintegral_mono_ae hfg).trans_eq <| by
    rw [lintegral_add_left measurable_const, lintegral_const]

end Laws

end ExpectationWP

/-! ## Expectation names

The laws above are named after core's `wp`, the constant they are stated on, so that they sit
with core's and PolyFun's `wp` lemmas. The `expect_*` aliases find them by what they state. -/

alias expect_pure := ExpectationWP.wp_pure
alias expect_bind := ExpectationWP.wp_bind
alias expect_map := ExpectationWP.wp_map
alias expect_eq_lintegral_map := ExpectationWP.wp_eq_lintegral_map
alias expect_eq_lintegral := ExpectationWP.wp_eq_lintegral
alias expect_eq_lintegral_comap := ExpectationWP.wp_eq_lintegral_comap
alias expect_mono := ExpectationWP.wp_mono
alias expect_congr := ExpectationWP.wp_congr
alias expect_zero := ExpectationWP.wp_zero
alias expect_add := ExpectationWP.wp_add
alias expect_mul_const := ExpectationWP.wp_mul_const
alias expect_const_mul := ExpectationWP.wp_const_mul
alias expect_finsetSum := ExpectationWP.wp_finsetSum
alias expect_mono_ae := ExpectationWP.wp_mono_ae
alias expect_iSup := ExpectationWP.wp_iSup
alias expect_le_mul_mass := ExpectationWP.wp_le_mul_mass
alias expect_le_const := ExpectationWP.wp_le_const
alias expect_le_const_mul_mass_add := ExpectationWP.wp_le_const_mul_mass_add
