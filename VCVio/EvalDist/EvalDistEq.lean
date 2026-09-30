/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.ProbabilityNotation

/-!
# Equality in distribution

`mx =ᵈ my` says that two computations, possibly in different monads, give every event the same
probability. The relation needs no measurable space on the output. Under lawful semantics it is
equality of the output measures in the discrete structure (`evalDistEq_iff_evalDist_eq`), and it
gives equal output measures in every structure (`EvalDistEq.evalDist_eq`).

Equality in distribution is preserved by maps and binds (`EvalDistEq.map`, `EvalDistEq.bind`),
is an equivalence, and composes in `calc` through its `Trans` instance.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v v' v''

section defs

variable {m : Type → Type v} {m' : Type → Type v'} [EvalDistSemantics m] [EvalDistSemantics m']
  [Monad m] [Monad m'] {α : Type}

/-- Two computations are equal in distribution when every event has the same probability under
both. -/
def EvalDistEq (mx : m α) (my : m' α) : Prop :=
  ∀ p : α → Prop, prEvent mx p = prEvent my p

@[inherit_doc] infix:50 " =ᵈ " => EvalDistEq

end defs

namespace EvalDistEq

variable {m : Type → Type v} {m' : Type → Type v'} {m'' : Type → Type v''}
  [Monad m] [Monad m'] [Monad m''] [EvalDistSemantics m] [EvalDistSemantics m']
  [EvalDistSemantics m''] {α β : Type}

/-- Equality in distribution gives every event the same probability. -/
theorem prEvent_eq {mx : m α} {my : m' α} (h : mx =ᵈ my) (p : α → Prop) :
    prEvent mx p = prEvent my p :=
  h p

/-- Computations whose events all have the same probabilities are equal in distribution. -/
theorem of_forall_prEvent_eq {mx : m α} {my : m' α}
    (h : ∀ p : α → Prop, prEvent mx p = prEvent my p) : mx =ᵈ my :=
  h

@[refl, simp]
theorem refl (mx : m α) : mx =ᵈ mx := fun _ ↦ rfl

protected theorem rfl {mx : m α} : mx =ᵈ mx := refl mx

@[symm]
theorem symm {mx : m α} {my : m' α} (h : mx =ᵈ my) : my =ᵈ mx := fun p ↦ (h p).symm

theorem trans {mx : m α} {my : m' α} {mz : m'' α} (h₁ : mx =ᵈ my) (h₂ : my =ᵈ mz) :
    mx =ᵈ mz :=
  fun p ↦ (h₁ p).trans (h₂ p)

instance : @Trans (m α) (m' α) (m'' α) EvalDistEq EvalDistEq EvalDistEq := ⟨trans⟩

instance : Std.Refl (α := m α) EvalDistEq := ⟨refl⟩

instance : Std.Symm (α := m α) EvalDistEq := ⟨fun _ _ ↦ symm⟩

instance : IsTrans (m α) EvalDistEq := ⟨fun _ _ _ ↦ trans⟩

/-- A common map preserves equality in distribution. -/
theorem map [LawfulMonad m] [LawfulMonad m'] {mx : m α} {my : m' α} (h : mx =ᵈ my) (f : α → β) :
    f <$> mx =ᵈ f <$> my :=
  fun p ↦ by simpa only [prEvent_map] using h fun x ↦ p (f x)

section lawful

variable [LawfulMonad m] [LawfulMonad m'] [LawfulEvalDistSemantics m]
  [LawfulEvalDistSemantics m']

/-- Computations equal in distribution have the same output measure in every measurable
structure on their outputs. -/
theorem evalDist_eq [MeasurableSpace α] {mx : m α} {my : m' α} (h : mx =ᵈ my) :
    𝒟[mx] = 𝒟[my] := by
  ext s hs
  have hp : Measurable fun x : α ↦ x ∈ s := measurableSet_setOfPred.mp hs
  simpa using (prEvent_eq_evalDist mx _ hp).symm.trans ((h _).trans (prEvent_eq_evalDist my _ hp))

/-- Computations with the same output measure in a discrete structure are equal in
distribution. -/
theorem of_evalDist_eq {_ : MeasurableSpace α} [DiscreteMeasurableSpace α] {mx : m α}
    {my : m' α} (h : 𝒟[mx] = 𝒟[my]) : mx =ᵈ my := fun p ↦ by
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete, h]

/-- Equality in distribution is equality of the output measures in the discrete structure. -/
theorem _root_.evalDistEq_iff_evalDist_eq {mx : m α} {my : m' α} :
    mx =ᵈ my ↔ (letI : MeasurableSpace α := ⊤; 𝒟[mx] = 𝒟[my]) :=
  letI : MeasurableSpace α := ⊤
  ⟨evalDist_eq, of_evalDist_eq⟩

/-- On a countable output type, equality in distribution is equality of every point mass. -/
theorem _root_.evalDistEq_iff_forall_prEvent_eq_output [Countable α] {mx : m α} {my : m' α} :
    mx =ᵈ my ↔ ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x] := by
  let : MeasurableSpace α := ⊤
  refine ⟨fun h x ↦ h (· = x), fun h ↦ of_evalDist_eq (Measure.ext_of_singleton fun x ↦ ?_)⟩
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  exact h x

/-- Computations equal in distribution give every observation the same expectation. -/
theorem wp_eq {mx : m α} {my : m' α} (h : mx =ᵈ my) (g : α → ℝ≥0∞) : wp⟦mx⟧ g = wp⟦my⟧ g := by
  let : MeasurableSpace α := ⊤
  rw [MeasureProgramLogic.wp_eq_lintegral mx g Measurable.of_discrete,
    MeasureProgramLogic.wp_eq_lintegral my g Measurable.of_discrete, h.evalDist_eq]

/-- Binds of computations and continuations equal in distribution are equal in distribution. -/
theorem bind {mx : m α} {my : m' α} (h : mx =ᵈ my) {f : α → m β} {g : α → m' β}
    (hfg : ∀ a, f a =ᵈ g a) : mx >>= f =ᵈ my >>= g := fun p ↦ by
  rw [prEvent_bind, prEvent_bind, h.wp_eq]
  exact MeasureProgramLogic.wp_congr my fun a ↦ hfg a p

end lawful

section sameMonad

/-- A common map is a congruence for equality in distribution within one monad. -/
@[gcongr]
theorem map_congr [LawfulMonad m] (f : α → β) {mx my : m α} (h : mx =ᵈ my) :
    f <$> mx =ᵈ f <$> my :=
  h.map f

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- Bind is a congruence for equality in distribution within one monad. -/
@[gcongr]
theorem bind_congr {mx my : m α} {f g : α → m β} (h : mx =ᵈ my) (hfg : ∀ a, f a =ᵈ g a) :
    mx >>= f =ᵈ my >>= g :=
  h.bind hfg

/-- A computation equal in distribution may replace the first draw of a bind. -/
theorem bind_left {mx my : m α} (h : mx =ᵈ my) (f : α → m β) : mx >>= f =ᵈ my >>= f :=
  h.bind fun _ ↦ .rfl

/-- Continuations equal in distribution may replace one another after a common draw. -/
theorem bind_right (mx : m α) {f g : α → m β} (hfg : ∀ a, f a =ᵈ g a) :
    mx >>= f =ᵈ mx >>= g :=
  EvalDistEq.rfl.bind hfg

end sameMonad

end EvalDistEq
