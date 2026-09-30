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
`measureWP m`, written `wp⟦mx⟧ g`; `𝔼{let x ← mx}[g x]` (`VCVio.EvalDist.ProbabilityNotation`)
writes it through a `do` sequence. The interpretation is exact (`ExactWPMonad`), so `simp`
distributes `wp⟦·⟧ ` over `pure`, `bind`, and `map` with core's own equations; the laws below
relate it to Mathlib's lintegral and to the order and arithmetic of `ℝ≥0∞`.

The laws need no measurable structure on the outputs: when an argument integrates, it selects
the σ-algebra that the observation itself induces. `wp_eq_lintegral` states the integral form
for a chosen output space.

`measureWP m` is supplied explicitly rather than found by instance search. An instance for every
`m` with measure semantics would overlap core's transformer lifts, which interpret `StateT σ m`
or `OptionT m` over other assertion carriers.
-/

public section

open MeasureTheory Std.Internal.Do
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
@[simp] theorem propInd_and {P Q : Prop} : propInd (P ∧ Q) = propInd P * propInd Q := by
  unfold propInd; split_ifs <;> simp_all

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
theorem propInd_or_le {P Q : Prop} : propInd (P ∨ Q) ≤ propInd P + propInd Q := by
  unfold propInd; split_ifs <;> simp_all

open scoped Classical in
theorem propInd_not {P : Prop} : propInd (¬P) = 1 - propInd P := by
  unfold propInd; split_ifs <;> simp_all

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

namespace MeasureProgramLogic

variable (m : Type → Type v) [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- The ordered algebra of nonnegative expectations under successful-output measures. -/
@[expose, instance_reducible]
noncomputable def toMAlgOrdered : MAlgOrdered m ℝ≥0∞ where
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
noncomputable def measureWP [LawfulMonad m] : WPMonad m ℝ≥0∞ EPost.Nil :=
  @MAlgOrdered.toWPMonad m ℝ≥0∞ _ _ (toMAlgOrdered m) _

end MeasureProgramLogic

/-- The expectation `wp⟦mx⟧ g` of `g` over the outputs of `mx`: core's `wp mx g ⊥` under the
measure interpretation `MeasureProgramLogic.measureWP`. Standalone, `wp⟦mx⟧ ` is the function
`fun g => wp⟦mx⟧ g`. -/
syntax:max (name := measureWpStx) "wp⟦" term "⟧ " : term

@[inherit_doc measureWpStx]
syntax:max (name := measureWpAppStx) "wp⟦" term "⟧ " term:max : term

macro_rules
  | `(wp⟦ $mx ⟧ $g:term) =>
    `(@Std.Internal.Do.WP.wp _ _ ENNReal Std.Internal.Do.EPost.Nil _ _
      (@Std.Internal.Do.instWPOfWPMonad _ ENNReal Std.Internal.Do.EPost.Nil _ _ _ _
        (MeasureProgramLogic.measureWP _)) $mx $g
      (open Lean.Order in (Lean.Order.bot : Std.Internal.Do.EPost.Nil)))
  | `(wp⟦ $mx ⟧) => `(fun g => wp⟦ $mx ⟧ g)

namespace MeasureProgramLogic

section Laws

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α : Type}

/-- The expectation of a returned value is the observation at that value. -/
theorem wp_pure (a : α) (g : α → ℝ≥0∞) : wp⟦(pure a : m α)⟧ g = g a :=
  letI := measureWP m
  ExactWPMonad.wp_pure a g _

/-- The expectation after a bind is the expectation of the continuations' expectations. -/
theorem wp_bind {β : Type} (mx : m α) (f : α → m β) (g : β → ℝ≥0∞) :
    wp⟦mx >>= f⟧ g = wp⟦mx⟧ fun a => wp⟦f a⟧ g :=
  letI := measureWP m
  ExactWPMonad.wp_bind mx f g _

/-- The expectation of mapped outputs is the expectation of the composed observation. -/
theorem wp_map {β : Type} (f : α → β) (mx : m α) (g : β → ℝ≥0∞) :
    wp⟦f <$> mx⟧ g = wp⟦mx⟧ fun a => g (f a) :=
  letI := measureWP m
  ExactWPMonad.wp_map f mx g _

omit [LawfulMonad m] in
/-- The expectation algebra integrates its actual nonnegative output. -/
theorem μ_toMAlgOrdered (mx : m ℝ≥0∞) :
    (toMAlgOrdered m).μ mx = ∫⁻ x, x ∂𝒟[mx] := rfl

/-- An expectation integrates the observation's image measure. -/
theorem wp_eq_lintegral_map (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = ∫⁻ y, y ∂𝒟[g <$> mx] := by
  change (toMAlgOrdered m).μ (mx >>= fun a => pure (g a)) = _
  rw [bind_pure_comp]
  rfl

/-- An expectation is the integral of a measurable observation. -/
theorem wp_eq_lintegral [MeasurableSpace α] (mx : m α) (g : α → ℝ≥0∞) (hg : Measurable g) :
    wp⟦mx⟧ g = ∫⁻ x, g x ∂𝒟[mx] := by
  have hf : Measurable (fun x ↦ 𝒟[(pure (g x) : m ℝ≥0∞)]) := by
    simpa only [evalDist_pure, Function.comp_def] using Measure.measurable_dirac.comp hg
  change (toMAlgOrdered m).μ (mx >>= fun x ↦ pure (g x)) = _
  rw [μ_toMAlgOrdered,
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
  @MAlgOrdered.μ_bind_pure_mono m ℝ≥0∞ _ _ (toMAlgOrdered m) α mx f g hfg

/-- Observations that agree on every output have the same expectation. -/
theorem wp_congr (mx : m α) {f g : α → ℝ≥0∞} (hfg : ∀ x, f x = g x) :
    wp⟦mx⟧ f = wp⟦mx⟧ g := by
  rw [show f = g from funext hfg]

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

end MeasureProgramLogic

/-! ## Expectation names

The laws above are named after core's `wp`, the constant they are stated on, so that they sit
with core's and PolyFun's `wp` lemmas. The `expect_*` aliases find them by what they state. -/

alias expect_pure := MeasureProgramLogic.wp_pure
alias expect_bind := MeasureProgramLogic.wp_bind
alias expect_map := MeasureProgramLogic.wp_map
alias expect_eq_lintegral_map := MeasureProgramLogic.wp_eq_lintegral_map
alias expect_eq_lintegral := MeasureProgramLogic.wp_eq_lintegral
alias expect_eq_lintegral_comap := MeasureProgramLogic.wp_eq_lintegral_comap
alias expect_mono := MeasureProgramLogic.wp_mono
alias expect_congr := MeasureProgramLogic.wp_congr
alias expect_zero := MeasureProgramLogic.wp_zero
alias expect_add := MeasureProgramLogic.wp_add
alias expect_mul_const := MeasureProgramLogic.wp_mul_const
alias expect_const_mul := MeasureProgramLogic.wp_const_mul
alias expect_finsetSum := MeasureProgramLogic.wp_finsetSum
alias expect_mono_ae := MeasureProgramLogic.wp_mono_ae
alias expect_iSup := MeasureProgramLogic.wp_iSup
alias expect_le_mul_mass := MeasureProgramLogic.wp_le_mul_mass
alias expect_le_const := MeasureProgramLogic.wp_le_const
alias expect_le_const_mul_mass_add := MeasureProgramLogic.wp_le_const_mul_mass_add
