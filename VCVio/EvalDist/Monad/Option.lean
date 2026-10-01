/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.OptionT
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.EvalDist.Monad.Failure
public import ToMathlib.Control.OptionT

/-!
# Events of optional computations

An optional computation is interpreted by core's lift of its base monad's expectation
interpretation (`ExpectationWP.optionT`): `wp⟦mx⟧ g` is the expectation of `g` over the present
values of the run, `wp⟦mx.run⟧ fun o => o.elim 0 g` (`wp_eq_run`), so a failure contributes
nothing. The measure interpretation of the stack agrees (`wp_ofMeasure_eq`), which carries the
laws of successful-output measures over. A sampled guard is a condition on the sampled value, and
sequencing a lossless prefix with continuations that succeed on its reachable outputs preserves
probability-one events.
-/

public section

open MeasureTheory Std.WP
open scoped ENNReal

universe v

namespace OptionT

section lift

variable {m : Type → Type v} [Monad m] {EPred : Type} [Assertion EPred] [ExpectationWP m EPred]
  {α : Type}

/-- An expectation over an optional computation is the expectation over the present values of
its run, with a failure worth `0`. -/
theorem wp_eq_run (mx : OptionT m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = wp⟦mx.run⟧ fun o => o.elim 0 g := by
  rw [ExpectationWP.wp_liftOptionT_apply, ExpectationWP.bot_snd]
  refine ExpectationWP.wp_congr _ fun o => ?_
  cases o <;> simp [Lean.Order.pushOption]

/-- Successful events are the events of present values in the underlying run. -/
theorem prEvent_eq_run (mx : OptionT m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = Pr{let value ← mx.run}[value.elim False p] := by
  rw [wp_eq_run]
  refine ExpectationWP.wp_congr _ fun o => ?_
  cases o <;> simp

/-- Failure has every expectation `0`. -/
@[simp↓ high, grind norm↓]
theorem wp_failure (g : α → ℝ≥0∞) : wp⟦(failure : OptionT m α)⟧ g = 0 := by
  rw [wp_eq_run, OptionT.run_failure, ExpectationWP.wp_pure]
  rfl

/-- Lifting into the optional monad preserves every expectation. -/
@[simp high, grind norm↓]
theorem wp_lift (mx : m α) (g : α → ENNReal) : wp⟦OptionT.lift mx⟧ g = wp⟦mx⟧ g := by
  simp only [wp_eq_run, OptionT.run_lift, ExpectationWP.wp_bind, ExpectationWP.wp_pure,
    Option.elim]

/-- Lifting into the optional monad preserves the probability of an observed event. -/
theorem prEvent_lift (mx : m α) (p : α → Prop) :
    Pr{let x ← OptionT.lift mx}[p x] = Pr{let x ← mx}[p x] :=
  wp_lift mx _

/-- A monadic lift into the optional monad preserves every expectation. -/
@[simp high]
theorem wp_liftM (mx : m α) (g : α → ENNReal) : wp⟦(liftM mx : OptionT m α)⟧ g = wp⟦mx⟧ g :=
  wp_lift mx g

/-- The lift instance of the optional monad preserves every expectation. -/
@[simp high]
theorem wp_monadLift (mx : m α) (g : α → ENNReal) :
    wp⟦(MonadLift.monadLift mx : OptionT m α)⟧ g = wp⟦mx⟧ g :=
  wp_lift mx g

/-- The lift instance of the optional monad preserves the probability of an observed event. -/
theorem prEvent_monadLift (mx : m α) (p : α → Prop) :
    Pr{let x ← (MonadLift.monadLift mx : OptionT m α)}[p x] = Pr{let x ← mx}[p x] :=
  prEvent_lift mx p

/-- A monadic lift into the optional monad preserves the probability of an observed event. -/
theorem prEvent_liftM (mx : m α) (p : α → Prop) :
    Pr{let x ← (liftM mx : OptionT m α)}[p x] = Pr{let x ← mx}[p x] :=
  prEvent_lift mx p

/-- A guard weights the observation by its condition. -/
@[simp high, grind norm]
theorem wp_guard (c : Prop) [Decidable c] (g : Unit → ℝ≥0∞) :
    wp⟦(guard c : OptionT m Unit)⟧ g = propInd c * g () := by
  by_cases hc : c <;> simp [guard, hc]

/-- A guard contributes its condition to the observed event after a lifted draw. -/
theorem prEvent_bind_guard (mx : m α) (p q : α → Prop) [DecidablePred p] :
    Pr{let x ← OptionT.lift mx; guard (p x)}[q x] =
      Pr{let x ← mx}[p x ∧ q x] := by
  classical
  rw [wp_lift]
  refine ExpectationWP.wp_congr mx fun x ↦ ?_
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

/-- A successful event of a wrapped computation is the event of present values that satisfy it
in the underlying computation. -/
theorem prEvent_mk (mx : m (Option α)) (p : α → Prop) :
    Pr{let x ← OptionT.mk mx}[p x] = Pr{let o ← mx}[o.elim False p] := by
  rw [prEvent_eq_run, OptionT.run_mk]

end lift

section measure

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α : Type}

/-- The measure interpretation of an optional computation agrees with the lift: both integrate
the observation over the present values. -/
@[simp, grind norm]
theorem wp_ofMeasure_eq (mx : OptionT m α) (g : α → ℝ≥0∞) :
    @Std.WP.WP.wp _ _ ENNReal _ _ _ (@Std.WP.instWPOfWPMonad _ ENNReal _ _ _ _ _
      (ExpectationWP.toWPMonad (self := ExpectationWP.ofMeasure (OptionT m)))) mx g
        Lean.Order.bot = wp⟦mx⟧ g := by
  let : MeasurableSpace α := ⊤
  rw [wp_eq_run, ExpectationWP.wp_eq_lintegral (m := OptionT m) mx g Measurable.of_discrete,
    OptionT.evalDist_eq_dropNone, Measure.lintegral_dropNone _ Measurable.of_discrete,
    ExpectationWP.wp_eq_lintegral (m := m) mx.run _ Measurable.of_discrete]

/-- The zero observation has expectation zero. -/
@[simp]
theorem wp_zero (mx : OptionT m α) : wp⟦mx⟧ (fun _ => 0) = 0 := by
  rw [← wp_ofMeasure_eq]
  exact ExpectationWP.wp_zero mx

/-- A constant observation has the expectation of the constant times the success mass. -/
@[simp]
theorem wp_const (mx : OptionT m α) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun _ => c) = c * Pr{let _ ← mx}[True] := by
  rw [← wp_ofMeasure_eq, ← wp_ofMeasure_eq]
  exact _root_.wp_const mx c

/-- An indicator observation scaled on the right is the scaled event. -/
@[simp]
theorem wp_propInd_mul (mx : OptionT m α) (p : α → Prop) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun a => propInd (p a) * c) = Pr{let x ← mx}[p x] * c := by
  rw [← wp_ofMeasure_eq, ← wp_ofMeasure_eq]
  exact _root_.wp_propInd_mul mx p c

/-- An indicator observation scaled on the left is the scaled event. -/
@[simp]
theorem wp_mul_propInd (mx : OptionT m α) (p : α → Prop) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun a => c * propInd (p a)) = c * Pr{let x ← mx}[p x] := by
  rw [← wp_ofMeasure_eq, ← wp_ofMeasure_eq]
  exact _root_.wp_mul_propInd mx p c

/-- Events of independent optional draws have the product of their probabilities. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_bind_and {β : Type} (mx : OptionT m α) (my : OptionT m β) (p : α → Prop)
    (q : β → Prop) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] = Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] := by
  simp only [← wp_ofMeasure_eq]
  exact _root_.prEvent_bind_bind_and mx my p q

/-- A lifted draw followed by a guard puts its successful event mass at the unit output. -/
@[simp↓ high]
theorem evalDist_lift_bind_guard (mx : m α) (p : α → Prop) [DecidablePred p] :
    𝒟[do let x ← OptionT.lift mx; guard (p x)] =
      Pr{let x ← mx}[p x] • Measure.dirac () := by
  apply Measure.ext_of_singleton
  rintro ⟨⟩
  rw [← prEvent_eq_evalDist_singleton, wp_ofMeasure_eq, prEvent_bind, wp_lift,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton ()), smul_eq_mul, mul_one]
  refine ExpectationWP.wp_congr mx fun x => ?_
  by_cases hp : p x <;> simp [hp]

/-- A monadic lift followed by a guard puts its successful event mass at the unit output. -/
@[simp↓ high]
theorem evalDist_liftM_bind_guard (mx : m α) (p : α → Prop) [DecidablePred p] :
    𝒟[do let x ← (liftM mx : OptionT m α); guard (p x)] =
      Pr{let x ← mx}[p x] • Measure.dirac () :=
  evalDist_lift_bind_guard mx p

/-- Lifting into the optional monad adds no failure. -/
@[simp]
theorem prFail_lift (mx : m α) : prFail (OptionT.lift mx) = prFail mx := by
  rw [prFail_def, prFail_def, wp_lift]

/-- `failure` always fails. -/
@[simp]
theorem prFail_failure : prFail (failure : OptionT m α) = 1 := by
  simp [prFail_def]

/-- `guard p` fails exactly when `p` does not hold. -/
@[simp↓ high]
theorem prFail_guard (p : Prop) [Decidable p] : prFail (guard p : OptionT m Unit) =
    if p then 0 else 1 := by
  by_cases hp : p <;> simp [prFail_def, hp]

/-- A monadic lift into the optional monad adds no failure. -/
@[simp]
theorem prFail_liftM (mx : m α) : prFail (liftM mx : OptionT m α) = prFail mx :=
  prFail_lift mx

end measure

section sequencing

variable {m : Type → Type v} [Monad m] [LawfulMonad m] {α β : Type}

/-- A wrapped bind is a lifted prefix followed by the wrapped continuations. -/
theorem mk_bind_eq_lift_bind (mx : m α) (f : α → m (Option β)) :
    OptionT.mk (mx >>= f) = (OptionT.lift mx >>= fun a ↦ OptionT.mk (f a) : OptionT m β) := by
  simp [OptionT.ext_iff]

variable [MonadAttach m] [ExactMonadAttach m]

/-- Reachable outputs of a lifted computation are reachable in the computation. -/
theorem mem_support_of_mem_support_lift {mx : m α} {a : α}
    (ha : a ∈ support (OptionT.lift mx)) : a ∈ support mx := by
  rw [MonadAttach.mem_support, MonadAttach.OptionT.canReturn_iff, OptionT.run_lift,
    MonadAttach.mem_support_bind] at ha
  obtain ⟨a', ha', h⟩ := ha
  rw [MonadAttach.mem_support_pure] at h
  exact Option.some_injective _ h ▸ ha'

variable [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- A lossless prefix followed by continuations that each satisfy an event with probability one
on the prefix's reachable outputs satisfies the event with probability one. -/
theorem prEvent_mk_bind_eq_one_of_support (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1)
    (f : α → m (Option β)) (p : β → Prop)
    (h : ∀ a ∈ support mx, Pr{let y ← OptionT.mk (f a)}[p y] = 1) :
    Pr{let y ← OptionT.mk (mx >>= f)}[p y] = 1 := by
  rw [prEvent_mk, prEvent_bind]
  refine le_antisymm (wp_le_of_forall_le _ fun _ ↦ prEvent_le_one _) ?_
  exact le_prEvent_bind_of_forall_le_of_support mx hmx _ _ fun a ha ↦
    ((prEvent_mk (f a) p).symm.trans (h a ha)).ge

/-- An upper bound on the wrapped continuation event over reachable prefixes. -/
theorem prEvent_mk_bind_le_of_forall_le (mx : m α) (f : α → m (Option β)) (q : β → Prop)
    {ε : ENNReal} (h : ∀ a ∈ support mx, Pr{let y ← OptionT.mk (f a)}[q y] ≤ ε) :
    Pr{let y ← OptionT.mk (mx >>= f)}[q y] ≤ ε := by
  rw [prEvent_mk, prEvent_bind]
  exact prEvent_bind_le_of_forall_le_of_support mx _ _ fun a ha ↦
    (prEvent_mk (f a) q).symm.trans_le (h a ha)

end sequencing

end OptionT
