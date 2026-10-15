/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.EvalDist.Monad.Except
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Defs.Measure.FinRatPMF
public import VCVioTest.MeasureSemantics
public import VCVio.EvalDist.Inequalities
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.EvalDist.PFunctorPath
public import VCVio.EvalDist.Defs.Measure.ExceptT
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Computation probability notation canaries

These examples exercise the same `Pr{...}[...]` syntax with a finite computation and an optional
computation, and the measure semantics of a continuous oracle, whose events are stated on the
measure.
-/

public section

open MeasureTheory ProbabilityTheory OracleComp PFunctor ProbComp
open scoped ENNReal
open scoped OracleComp.Lower

namespace VCVioTest.ProbabilityNotation

/-- A closed draw whose implementation is opaque to consumers. -/
opaque opaqueDraw : ProbComp ℝ := pure 0

example : IsProbabilityMeasure 𝒟[opaqueDraw] := inferInstance

example : IsSubprobabilityMeasure 𝒟[opaqueDraw] := inferInstance

example (mx : ProbComp ℝ) : IsProbabilityMeasure 𝒟[OptionT.lift mx] := inferInstance

example (mx : ProbComp ℝ) : IsProbabilityMeasure 𝒟[(liftM mx : OptionT ProbComp ℝ)] :=
  inferInstance

example (mx : ProbComp ℝ) : IsProbabilityMeasure 𝒟[(liftM mx : ExceptT Bool ProbComp ℝ)] :=
  inferInstance

example {α : Type} [MeasurableSpace α] (mx : OptionT ProbComp α) :
    𝒟[mx] = (𝒟[mx.run]).comap some := OptionT.evalDist_eq_comap_some mx

example {α : Type} [MeasurableSpace α] (mx : ExceptT Bool ProbComp α) :
    𝒟[mx] = (𝒟[mx.run]).comap Except.ok := ExceptT.evalDist_eq_comap_ok mx

example {α : Type} [SampleableType α] [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    Pr{let x ← $ᵗ α}[p x] = (Finset.univ.filter p).card / (Fintype.card α : ENNReal) := by
  simp

example {α : Type} [SampleableType α] [Fintype α]
    (p : α → Prop) [DecidablePred p] {bound : ENNReal}
    (h : (Finset.univ.filter p).card / (Fintype.card α : ENNReal) ≤ bound) :
    Pr{let x ← $ᵗ α}[p x] ≤ bound := by grind

example (mx : ProbComp ℝ) : IsProbabilityMeasure 𝒟[mx] := inferInstance

example (mx : OracleComp coinSpec ℝ) : IsProbabilityMeasure 𝒟[mx] := inferInstance

example {α : Type} [MeasurableSpace α] (mx : OptionT ProbComp α) :
    IsSubprobabilityMeasure 𝒟[mx] := inferInstance

example (μ : Measure ℝ) [IsSubprobabilityMeasure μ] (f : ℝ → ℝ) :
    IsSubprobabilityMeasure (μ.map f) := inferInstance

example (μ : Measure ℝ) [IsSubprobabilityMeasure μ] (f : ℝ → Measure ℝ)
    [∀ x, IsSubprobabilityMeasure (f x)] (hf : AEMeasurable f μ) :
    IsSubprobabilityMeasure (μ.bind f) := MeasureTheory.isSubprobabilityMeasure_bind hf

example (mx : ProbComp ℝ) : IsProbabilityMeasure (FreeM.denote mx) := inferInstance

example (mx : ProbComp ℝ) [MeasurableSpace (FreeM.Path mx)] :
    IsProbabilityMeasure (FreeM.pathMeasure mx) := inferInstance

example (mx : ProbComp ℝ) : IsProbabilityMeasure (FreeM.queryCountMeasure mx) := inferInstance

example (mx : ProbComp ℝ) : ∫⁻ _, (1 : ENNReal) ∂𝒟[mx] = 1 := by simp

example {α : Type} (mx : ProbComp α) (b : Bool) :
    𝒟[(fun _ ↦ b) <$> mx] {b} = 1 := by simp

example {α : Type} (mx : ProbComp α) (f : α → ℕ) (c : ℕ) :
    (∫⁻ n, (n : ENNReal) ∂𝒟[(fun x ↦ f x + c) <$> mx]) =
      (∫⁻ n, (n : ENNReal) ∂𝒟[f <$> mx]) + c := by simp

example {α : Type} (mx : ProbComp α) (f : α → ℕ) (c : ℕ) :
    (∫⁻ n, (n : ENNReal) ∂𝒟[Nat.add c <$> (f <$> mx)]) =
      (∫⁻ n, (n : ENNReal) ∂𝒟[f <$> mx]) + c := by grind [measure_univ, mul_one]

example {α : Type} (mx : ProbComp α) (f : α → ℕ) (c : ℕ) {bound : ENNReal}
    (h : (∫⁻ n, (n : ENNReal) ∂𝒟[f <$> mx]) ≤ bound) :
    (∫⁻ n, (n : ENNReal) ∂𝒟[(fun x ↦ f x + c) <$> mx]) ≤ bound + c := by
  grw [lintegral_evalDist_map_add_nat, measure_univ, mul_one, h]

example : (∫⁻ _ : Fin 0, (⊤ : ENNReal) ∂uniformOn Set.univ) = 0 := by
  simp

example : (∫⁻ _, (⊤ : ENNReal) ∂𝒟[uniformFin 0]) = ⊤ := by
  simp only [lintegral_const, measure_univ, mul_one]

example (mx : ProbComp Bool) :
    Pr{let b ← mx}[b] = 𝒟[mx] {true} := by
  rw [prEvent_eq_evalDist_of_discrete]
  simp

example (mx : OptionT ProbComp Bool) :
    Pr{let b ← mx}[b] = 𝒟[mx] {true} := by
  rw [← OptionT.wp_ofMeasure_eq, prEvent_eq_evalDist_of_discrete]
  simp

example (mx : FinRatPMF.Raw Bool) :
    Pr{let b ← mx}[b] = ((mx.prob true : NNReal) : ENNReal) := by
  rw [prEvent_eq_evalDist_of_discrete]
  simp

example : FinRatPMF.Raw.coin.prob true = 1 / 2 := by
  simpa only [one_div] using FinRatPMF.Raw.prob_coin true

example (mx : ProbComp (Fin 3)) :
    Pr{let n ← mx; let value := n.val}[value = 1] =
      𝒟[mx] {n | n.val = 1} := by
  simpa only using prEvent_eq_evalDist_of_discrete mx (fun n => n.val = 1)

open VCVioTest.MeasureSemantics in
example : IsProbabilityMeasure 𝒟[(FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)] :=
  FreeM.isProbabilityMeasure_evalDist_lift (P := gaussSpec) _

open VCVioTest.MeasureSemantics in
example : IsProbabilityMeasure 𝒟[(pure (1 : ℝ) : FreeM gaussSpec ℝ)] := inferInstance

open VCVioTest.MeasureSemantics in
example : 𝒟[(failure : OptionT (FreeM gaussSpec) ℝ)] = 0 := by simp

open VCVioTest.MeasureSemantics in
example : ¬ IsProbabilityMeasure 𝒟[(failure : OptionT (FreeM gaussSpec) Bool)] := by
  simp [isProbabilityMeasure_iff]

/-! A continuous free monad has measure semantics but not lawful ones: a bind with a continuation
that is not measurable has no mass, so the monad's bind law fails. Its events are stated on the
measure; the event and expectation notations, which are core weakest preconditions, need lawful
semantics. -/

open VCVioTest.MeasureSemantics in
/--
error: an expectation needs an expectation interpretation of its monad (`ExpectationWP`): lawful measure semantics (`EvalDistSemantics`, `LawfulEvalDistSemantics`, `LawfulMonad`), or `OptionT` / `ExceptT` over such a monad; none for
  gaussSpec.FreeM
-/
#guard_msgs in
#check Pr{let x ← (FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)}[x > 0]

open VCVioTest.MeasureSemantics in
example :
    𝒟[(· > 0) <$> (FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)] {True} =
      gaussianReal 0 1 {x | x > 0} := by
  rw [map_eq_bind_pure_comp, Function.comp_def,
    FreeM.evalDist_lift_bind_pure (P := gaussSpec) _ _ (by fun_prop),
    FreeM.evalDist_eq_denote (P := gaussSpec), denote_gauss_lift,
    Measure.map_apply (by fun_prop) (measurableSet_singleton True)]
  simp

open VCVioTest.MeasureSemantics in
example (acc B : ℝ → ENNReal) (q hinv : ENNReal) (hacc : Measurable acc)
    (hle : ∀ x, acc x ≤ 1) (hper : ∀ x, acc x * (acc x / q - hinv) ≤ B x) :
    let mx := (FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)
    (∫⁻ x, acc x ∂𝒟[mx]) * ((∫⁻ x, acc x ∂𝒟[mx]) / q - hinv) ≤ ∫⁻ x, B x ∂𝒟[mx] :=
  OracleComp.EvalDist.marginalized_jensen_forking_bound _ acc B q hinv hacc.aemeasurable
    (Filter.Eventually.of_forall hle) (Filter.Eventually.of_forall hper)

open VCVioTest.MeasureSemantics in
example :
    𝒟[(pure (1 : ℝ) : OptionT (FreeM gaussSpec) ℝ)] {1} = 1 := by
  simp

open VCVioTest.MeasureSemantics in
example :
    𝒟[(· = 1) <$> (pure (1 : ℝ) : OptionT (FreeM gaussSpec) ℝ)] {True} = 1 := by
  simp

/-! Computations equal in distribution on an unmeasured payload have equal output measures after
real-valued continuations, and reach the same outputs. -/

example {α : Type} (mx my : ProbComp α) (h : mx =ᵈ my) (f : α → ProbComp ℝ) :
    𝒟[mx >>= f] = 𝒟[my >>= f] :=
  (h.bind_left f).evalDist_eq

example {α : Type} (mx my : ProbComp α) (h : mx =ᵈ my) (f : α → ℝ) :
    𝒟[f <$> mx] = 𝒟[f <$> my] :=
  (h.map f).evalDist_eq

example {α : Type} {mx my : ProbComp α} (h : mx =ᵈ my) : support mx = support my :=
  support_eq_of_evalDistEq h

/-! Equality in distribution compares computations in different monads and chains in `calc`. -/

example (n : ℕ) : (pure n : ProbComp ℕ) =ᵈ (some n : Option ℕ) :=
  EvalDistEq.of_forall_prEvent_eq fun p => by
    classical
    simp

example {α : Type} {mx my : ProbComp α} {mz : Option α} (h₁ : mx =ᵈ my) (h₂ : my =ᵈ mz) :
    mx =ᵈ mz :=
  calc mx =ᵈ my := h₁
    _ =ᵈ mz := h₂

example {α : Type} [Countable α] (mx my : ProbComp α)
    (h : ∀ x, Pr{let y ← mx}[y = x] = Pr{let y ← my}[y = x]) :
    mx =ᵈ my :=
  evalDistEq_iff_forall_prEvent_eq_output.mpr h

/-! ### Event notation

`Pr{items}[t]` is the expectation `𝔼{items}[𝟙⟦t⟧]` of the event's indicator: the translation of
the sequence into nested expectations of its draws, one `wp⟦a⟧ fun x => …` per draw, the last
observing the indicator `predInd p` of the event's predicate. Nothing is rewritten at
elaboration: a draw written as a bind, a map or a `do` block stays as written, and
`simp only [expect_norm]` brings it to the normal form of a draw chain. Goals display the draws
as `let` statements. -/

section eventNotation

open Lean.Order Std.WP

variable (mx : ProbComp Bool) (my : Bool → ProbComp ℕ) (mz : ProbComp ℕ)

/-! The specification: the notation is the nested expectation of its draws. -/

example : Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] =
    𝔼{let x ← mx; let y ← my x}[propInd (y = 3 ∧ x)] :=
  rfl
example : Pr{let x ← mx}[x = true] = wp⟦mx⟧ (predInd fun x => x = true) := by
  guard_target =ₛ wp⟦mx⟧ (predInd fun x => x = true) = wp⟦mx⟧ (predInd fun x => x = true)
  rfl
example (p : Bool → Prop) : Pr{let x ← mx}[p x] = wp⟦mx⟧ (predInd p) := by
  guard_target =ₛ wp⟦mx⟧ (predInd p) = wp⟦mx⟧ (predInd p)
  rfl
example : Pr{let x ← mx}[x] = wp⟦mx⟧ (predInd fun x => x = true) := rfl
example : Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] =
    wp⟦mx⟧ fun x => wp⟦my x⟧ (predInd fun y => y = 3 ∧ x = true) := rfl
example : Pr{let x : Bool ← mx}[x] = Pr{let x ← mx}[x = true] := rfl
example : Pr{let x ← mz}[x = 3] = wp⟦mz⟧ (predInd fun z => z = 3) := rfl
example : Pr{{let x ← mx}}[x] = Pr{let x ← mx}[x] := rfl
example : Pr{let _ ← mx; let y ← mz}[y = 3] = wp⟦mx⟧ fun _ => wp⟦mz⟧ (predInd fun y => y = 3) :=
  rfl
example : Pr{let x ← mz; mz}[x = 1] = wp⟦mz⟧ fun x => wp⟦mz⟧ (predInd fun _ => x = 1) := rfl
example : Pr{
    let x ← mz
    let y := x + 1}[y = 3] = wp⟦mz⟧ (predInd fun x => x + 1 = 3) := rfl
example : Pr{let x ← mz; let y := x + 1; let z ← my (y = 3)}[z = y] =
    wp⟦mz⟧ fun x => let y := x + 1; wp⟦my (y = 3)⟧ (predInd fun z => z = y) := rfl

/-- Draw annotations determine overloaded arithmetic before the observation is elaborated. -/
example : Pr{let x : ℤ ← (pure (1 - 2) : ProbComp _)}[x = -1] = 1 := by simp
example : Pr{let (x, y) : ℤ × ℤ ← (pure (1 - 2, -1) : ProbComp _)}[x = y] = 1 := by simp
example : Pr{let _ : ℤ ← (pure (1 - 2) : ProbComp _)}[True] =
    wp⟦(pure (-1) : ProbComp ℤ)⟧ (predInd fun _ => True) := rfl
example : Pr{let _ ← (pure () : ProbComp Unit); let x : ℤ ← pure (1 - 2)}[x = -1] = 1 :=
  by simp

-- Without an annotation, the event can still fix a type that a numeral leaves open, as in
-- ordinary `do`: these draw from `Fin 2`, `Fin 2 × _` and `ℤ`, with the values of the reference
-- `Pr{let r ← (do items; return (t : Prop))}[r]`.
example : Pr{let x ← (pure 2 : ProbComp _)}[x < (1 : Fin 2)] = 1 := by simp
example : Pr{let r ← (do let x ← (pure 2 : ProbComp _); return (x < (1 : Fin 2) : Prop))}[r] =
    1 := by simp
example : Pr{let x ← (pure (2, fun y => y) : ProbComp _)}[
    x.1 < (1 : Fin 2) ∧ x.2 true = true] = 1 := by simp
example : Pr{let x ← (pure (1 - 2) : ProbComp _)}[x = (-1 : ℤ)] = 1 := by simp
example : Pr{let b ← (pure true : ProbComp Bool); let mut m := 2; if b then m := m + 2}[
    m < (1 : Fin 2)] = 1 := by simp

example : True := by
  fail_if_success have : ℝ≥0∞ :=
    Pr{let x : Bool ← (pure (1 : ℕ) : ProbComp ℕ)}[True]
  fail_if_success have : ℝ≥0∞ :=
    Pr{let _ : Bool ← (pure (1 : ℕ) : ProbComp ℕ)}[True]
  fail_if_success have : ℝ≥0∞ :=
    Pr{let (x, y) : Bool × Bool ← (pure (1, 2) : ProbComp (ℕ × ℕ))}[True]
  fail_if_success have : ℝ≥0∞ :=
    Pr{let (x, y) : Bool × Bool ← (pure (1, 2) : ProbComp (ℕ × ℕ)); let _ ← mx}[True]
  trivial

/-! A draw written as a bind, a map, a returned value or a `do` block stays as written; the
normal form is one `simp only [expect_norm]` away. -/

example : Pr{let x ← mx >>= my}[x = 3] = wp⟦mx >>= my⟧ (predInd fun x => x = 3) := rfl
example : Pr{let x ← mx >>= my}[x = 3] = Pr{let x ← mx; let y ← my x}[y = 3] := by
  simp only [expect_norm]
example : Pr{let x ← not <$> mx}[x] = wp⟦not <$> mx⟧ (predInd fun x => x = true) := rfl
example : Pr{let x ← not <$> mx}[x] = wp⟦mx⟧ (predInd fun x => (!x) = true) := by
  simp only [expect_norm]
example (a : ℕ) : Pr{let x ← (pure a : ProbComp ℕ)}[x = 3] = propInd (a = 3) := by
  simp only [expect_norm]
example (f : ℕ → ℕ → ProbComp ℕ) :
    Pr{let z ← f (← mz) (← mz)}[z = 0] = Pr{let a ← mz; let b ← mz; let z ← f a b}[z = 0] := by
  simp only [expect_norm]

/-- A draw whose action continues on the following lines is laid out as in a `do` block, or its
action is parenthesized. -/
example (f : ℕ → ℕ → ProbComp ℕ) : Pr{
    let x ← f
      1 2
    let y ← f x
      x}[x = y] = Pr{let x ← f 1 2; let y ← f x x}[x = y] := rfl
example (f : ℕ → ℕ → ProbComp ℕ) : Pr{let x ← (f
    1 2)}[x = 1] = Pr{let x ← f 1 2}[x = 1] := rfl

/-- Branches and `match` on the right of a draw are ordinary draws. -/
example (m₁ m₂ : ProbComp ℕ) (c : Prop) [Decidable c] :
    Pr{let b ← $ᵗ Bool; let x ← if b then m₁ else m₂}[x = 3] =
      wp⟦$ᵗ Bool⟧ fun b => wp⟦if b then m₁ else m₂⟧ (predInd fun x => x = 3) := rfl
example (mo : ProbComp (Option ℕ)) :
    Pr{let o ← mo; let x ← match o with | some a => pure a | none => mz}[x = 1] =
      wp⟦mo⟧ fun o => wp⟦match o with | some a => pure a | none => mz⟧ (predInd fun x => x = 1) :=
  rfl

/-- A single-constructor destructuring draw matches on the drawn value, whether it is the last
draw or not, and whether its action is a term or a nested `do` block. -/
example (mp : ProbComp (ℕ × ℕ)) (init : ProbComp ℕ) (f : ℕ → ProbComp (ℕ × ℕ)) :
    Pr{let ⟨a, b⟩ ← mp}[a = b] = wp⟦mp⟧ (predInd fun z => z.1 = z.2) ∧
      Pr{let ⟨a, b⟩ ← do f (← init)}[a = b] =
        wp⟦init⟧ fun x => wp⟦f x⟧ (predInd fun z => z.1 = z.2) := by
  constructor <;> simp only [expect_norm]
example (mp : ProbComp (ℕ × ℕ)) (g : ℕ → ProbComp ℕ) :
    Pr{let (a, b) ← mp; let c ← g a}[b = c] =
      wp⟦mp⟧ fun z => wp⟦g z.1⟧ (predInd fun c => z.2 = c) := by
  simp only [expect_norm]

/-- An imperative tail (`let mut`, a loop, a do-level `if`) is one program whose result is the
tuple of the variables it binds, observed from outside. -/
example (g : ℕ → ProbComp ℕ) :
    Pr{let mut s := 0; for i in [1, 2, 3] do s := s + (← g i)}[s = 3] =
      Pr{let a ← g 1; let b ← g 2; let c ← g 3}[a + b + c = 3] := by
  simp
example : Pr{let b ← mx; let mut n : ℕ := 0; if b then n := 1}[n = 1] =
    𝔼{let b ← mx}[if b then 1 else 0] := by
  simp
example : Pr{let b ← (do if true then return true else return false : ProbComp Bool)}[b = true]
    = 1 := by
  simp

/-! The observation sees the tail's bindings as ordinary `do` scope does: a `have` that shadows
an earlier draw is the binding observed, and a name bound only by a `have` is visible. -/

example : Pr{
    let _b ← (pure true : ProbComp Bool)
    let mut n := 0
    have _b : Bool := false
    n := n + 1}[_b = true] = 0 := by
  simp
example : 𝔼{
    let _b ← (pure true : ProbComp Bool)
    let mut n := 0
    have _b : Bool := false
    n := n + 1}[if _b then 5 else 2] = 2 := by
  simp
example : Pr{
    let mut n ← (pure 0 : ProbComp ℕ)
    have c : Bool := false
    n := n + 1}[c = false ∧ n = 1] = 1 := by
  simp
example : Pr{
    let mut n ← (pure 0 : ProbComp ℕ)
    let x := 5
    n := n + x}[n = 5] = 1 := by
  simp

/-- Reassignment keeps the variables in the order they were introduced. -/
example (g : ℕ → ProbComp ℕ) (p : ℕ → ℕ → Prop) :
    Pr{let mut a ← g 0; let mut b ← g 1; a := a + 1}[p a b] =
      wp⟦do let a ← g 0; let b ← g 1; pure (a + 1, b)⟧ (predInd fun (a, b) => p a b) := by
  rfl

-- A proof bound by the tail cannot be returned; an event naming it would see an outer `h`, and
-- is rejected.
/--
error: the event reads `h`, which the imperative code binds but cannot return to it: a proof,
a type, a local instance, or a value whose type depends on another of its bindings

Rename it, or bind what the event needs to a value
-/
#guard_msgs (whitespace := lax) in
noncomputable example (h : ℕ) : ℝ≥0∞ := Pr{
    let mut n ← (pure 0 : ProbComp ℕ)
    have h : True := trivial
    n := n + 1}[h = 0]

/-- A name the observation binds itself is not the tail's. -/
example : Pr{
    let mut n ← (pure 0 : ProbComp ℕ)
    have h : True := trivial
    have _ : True := h
    n := n + 1}[(fun h : ℕ => h = 0) 0] = 1 := by
  simp

/-- A branch-local binding is not in scope after its branch: the event sees the outer one. -/
example (x : ℕ) (b : Bool) : Pr{
    let mut n ← (pure 0 : ProbComp ℕ)
    if b then
      let x := 7
      n := x
    else
      n := 9}[x = x ∧ n = if b then 7 else 9] = 1 := by
  cases b <;> simp

-- The event is resolved where ordinary `do` would resolve it: a macro reading a binding the tail
-- cannot return is rejected, and a qualified constant is not mistaken for a tail binding.
namespace TailResolution
def _p : Prop := True
local macro "readP" : term => `($(Lean.mkIdent `_p))
/--
error: the event reads `_p`, which the imperative code binds but cannot return to it: a proof,
a type, a local instance, or a value whose type depends on another of its bindings

Rename it, or bind what the event needs to a value
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{
    let mut _n ← (pure 0 : ProbComp ℕ)
    let _p : Prop := False}[readP]
def x : ℕ := 0
example : Pr{let mut x ← (pure 1 : ProbComp ℕ)}[x = TailResolution.x + 1] = 1 := by
  simp [TailResolution.x]
local macro "readX" : term => `($(Lean.mkIdent `x) < (1 : Fin 2))
example : Pr{let _ ← (pure () : ProbComp Unit); let mut x := 2; x := x + 2}[readX] = 1 := by
  simp
/-- An event elaborator that needs its expected type: the event is resolved at the end of the tail
under `Prop`, as it is outside, and reads the hidden `_p`. -/
local elab "needsProp " p:term : term <= expected => do
  if expected.isMVar then throwError "expected type required"
  Lean.Elab.Term.elabTermEnsuringType p expected
/--
error: the event reads `_p`, which the imperative code binds but cannot return to it: a proof,
a type, a local instance, or a value whose type depends on another of its bindings

Rename it, or bind what the event needs to a value
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{
    let mut _n ← (pure 0 : ProbComp ℕ)
    let _p : Prop := False}[needsProp _p]
-- A local instance of the tail is found by instance resolution, not by name; it cannot be
-- returned, so an event that uses it is rejected.
/--
error: the event reads an unnamed binding, which the imperative code binds but cannot return to
it: a proof, a type, a local instance, or a value whose type depends on another of its bindings,
here
  Inhabited Prop

Rename it, or bind what the event needs to a value
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{
    let mut _n ← (pure 0 : ProbComp ℕ)
    let _ : Inhabited Prop := ⟨False⟩}[default]
/--
error: the event reads an unnamed binding, which the imperative code binds but cannot return to
it: a proof, a type, a local instance, or a value whose type depends on another of its bindings,
here
  Inhabited ℝ≥0∞

Rename it, or bind what the event needs to a value
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := 𝔼{
    let mut _n ← (pure 0 : ProbComp ℕ)
    let _ : Inhabited ℝ≥0∞ := ⟨7⟩}[default]
-- An event the elaborator cannot resolve is reported once, from the end of the tail.
/--
error: Unknown identifier `nosuch`
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{let mut x ← (pure 3 : ProbComp ℕ)}[nosuch x]
end TailResolution

-- An observation written as a tactic block is completed before it is observed.
example : Pr{let mut _n ← (pure 0 : ProbComp ℕ)}[by exact True] = 1 := by simp
example : Pr{let _x ← (pure 0 : ProbComp ℕ)}[by exact True] = 1 := by simp
example : 𝔼{let mut n ← (pure 2 : ProbComp ℕ)}[by exact (n : ℝ≥0∞)] = 2 := by simp
example : 𝔼{let n ← (pure 2 : ProbComp ℕ)}[by exact (n : ℝ≥0∞)] = 2 := by simp
-- A hole for the event is left to unification, as in `do`.
set_option linter.unusedTactic false in
example : Pr{let mut n ← (pure 2 : ProbComp ℕ); n := n + 1}[n = 3] = 1 := by
  change Pr{let mut n ← (pure 2 : ProbComp ℕ); n := n + 1}[_] = _
  simp

-- `let pat ← e | alt` takes the rest of the block as its body, so the end of the tail is
-- inside it and the pattern's variables are observed, not an outer `x`.
set_option linter.unusedVariables false in
example (x : ℕ) : Pr{
    let mut n ← (pure 0 : OptionT ProbComp ℕ)
    let some x ← (pure (some 3) : OptionT ProbComp (Option ℕ)) | failure
    n := x}[n = 3 ∧ x = 3] = 1 := by
  simp
example : Pr{
    let mut n ← (pure 0 : OptionT ProbComp ℕ)
    let some x := (some 3 : Option ℕ) | failure
    n := x}[n = 3 ∧ x = 3] = 1 := by
  simp
-- `let_expr` keeps its trailing body too: `x` is the matched `Expr`, not the outer `ℕ`.
set_option linter.unusedVariables false in
noncomputable example (x : ℕ) : ℝ≥0∞ := Pr{
    let mut n ← (pure 0 : OptionT ProbComp ℕ)
    let_expr Nat.succ x := Lean.mkApp (Lean.mkConst ``Nat.succ) (Lean.mkRawNatLit 0) | failure
    n := 1}[x.isApp]
-- Written last, it has no body, and the end of the tail becomes its body.
set_option linter.unusedVariables false in
example (x : ℕ) : Pr{
    let mut n ← (pure 0 : OptionT ProbComp ℕ)
    let some x ← (pure (some 3) : OptionT ProbComp (Option ℕ)) | failure}[x = 3] = 1 := by
  simp
example : Pr{
    let b ← ($ᵗ Bool : ProbComp Bool)
    let mut _n : ℕ := 0
    let some x ← (pure (if b then some 3 else none) : OptionT ProbComp (Option ℕ)) | failure}[
    x = 3] = 1 / 2 := by
  simp

/-- A macro's hygienic tail binding is the one its own event observes, not an outer binding the
macro introduced under the same name. -/
local macro "shadowedByTail" : term => `(let b := true; Pr{
  let mut b ← (pure false : ProbComp Bool)
  b := false}[b = true])
example : shadowedByTail = 0 := by simp
local macro "tailOnly" : term => `(𝔼{
  let mut x ← (pure (0 : ℕ) : ProbComp ℕ)
  x := 3}[(x : ℝ≥0∞)])
example : tailOnly = 3 := by simp

/-- A draw whose program is a `let`-bound `do` block typed by its own binds elaborates once the
surrounding term has forced that block: the draw postpones instead of forcing its own binds. -/
noncomputable example (mx : OptionT ProbComp ℕ) : ℝ≥0∞ :=
  let exec := do
    let n ← mx
    return n + 1
  Pr{let x ← exec.run}[x = some 1]

/-! Each draw is read in the expectation interpretation of its own monad, so a sequence may
draw from several monads, and the failure of a draw contributes nothing to the event. -/

section mixedMonads

variable (outer : ProbComp Bool) (inner : OptionT ProbComp Bool) (p : Bool → Bool → Prop)

/-- info: Pr{let x ← outer; let y ← inner}[p x y] : ℝ≥0∞ -/
#guard_msgs in
#check 𝔼{let x ← outer}[Pr{let y ← inner}[p x y]]

example : 𝔼{let x ← outer}[Pr{let y ← inner}[p x y]] =
    Pr{let x ← outer; let y ← inner}[p x y] := rfl
example : Pr{let x ← outer; let y ← inner}[p x y] =
    wp⟦outer⟧ fun x => wp⟦inner⟧ (predInd fun y => p x y) := rfl
example : Pr{let _ ← outer; let _ ← (failure : OptionT ProbComp Bool)}[True] = 0 := by
  simp

/-- Imperative tails infer their own transformer monad, including through a nested stack. -/
example : Pr{
    let _ ← (pure () : ProbComp Unit)
    let mut _unused := 0
    let _ ← (failure : OptionT ProbComp Bool)}[True] = 0 := by simp
example : Pr{
    let _ ← (pure () : ProbComp Unit)
    let mut _unused := 0
    let _ ← (throw "error" : ExceptT String ProbComp Bool)}[True] = 0 := by simp
example : Pr{
    let _ ← (pure () : ProbComp Unit)
    let mut _unused := 0
    let _ ← (failure : OptionT (ExceptT String ProbComp) Bool)}[True] = 0 := by simp
example : Pr{
    let _ ← (pure () : ProbComp Unit)
    let mut _unused := 0
    let _ ← (throw "error" : ExceptT String (OptionT ProbComp) Bool)}[True] = 0 := by simp

/-- Base draws use the ordinary lift once the tail's transformer monad is determined. -/
example : Pr{
    let mut n := 0
    let b ← (pure true : OptionT ProbComp Bool)
    let x ← (pure 1 : ProbComp ℕ)
    if b then n := x}[n = 1] = 1 := by simp

/--
error: a draw in an imperative tail has a different monad; lift the draw or ascribe the tail's
monad explicitly
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{
    let mut n := 0
    let _ ← (pure () : ProbComp Unit)
    let _ ← (failure : OptionT ProbComp Bool)}[True]

/--
error: a draw in an imperative tail has a different monad; lift the draw or ascribe the tail's
monad explicitly
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{
    let mut n := 0
    let _ ← (pure () : ProbComp Unit)
    let _ ← (throw "error" : ExceptT String ProbComp Bool)}[True]

/--
error: a draw in an imperative tail has a different monad; lift the draw or ascribe the tail's
monad explicitly
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{
    let mut n := 0
    let _ ← (pure () : ProbComp Unit)
    let _ ← (failure : OptionT (ExceptT String ProbComp) Bool)}[True]

end mixedMonads

/-! A `return` at the top level of the braces is rejected; inside a bound computation it is
ordinary. -/

/--
error: `return` is not allowed at the top level of the braces: the sequence's bindings are what
the event observes; bind a computation that returns early as `let x ← (do …)`
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ :=
  Pr{let b ← (pure true : ProbComp Bool); if b then return (2 : ℝ≥0∞)}[False]

/--
error: `return` is not allowed at the top level of the braces: the sequence's bindings are what
the event observes; bind a computation that returns early as `let x ← (do …)`
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{let b ← mx; return b}[b = true]

/-- A `do` element expanding to an early return. -/
syntax "notationReturn" : doElem
macro_rules | `(doElem| notationReturn) => `(doElem| return (7 : ℕ))

/--
error: `return` is not allowed at the top level of the braces: the sequence's bindings are what
the event observes; bind a computation that returns early as `let x ← (do …)`
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{
    let _ ← (pure () : ProbComp Unit)
    let mut z := (0 : ℕ)
    notationReturn}[z = 7]

example : Pr{let x ← (do notationReturn : ProbComp ℕ)}[x = 7] = 1 := by simp

/-- A term macro expanding to a return before Lean introduces its `do` wrapper. -/
syntax "notationTermReturn" : term
macro_rules | `(notationTermReturn) => `(return (7 : ℕ))

/--
error: `return` is not allowed at the top level of the braces: the sequence's bindings are what
the event observes; bind a computation that returns early as `let x ← (do …)`
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ := Pr{
    let _ ← (pure () : ProbComp Unit)
    let mut z := (0 : ℕ)
    notationTermReturn}[z = 7]

/-- A term macro introducing a nested `do` scope. -/
syntax "notationNestedReturn" : term
macro_rules | `(notationNestedReturn) => `(do notationReturn)

example : Pr{let x ← (notationNestedReturn : ProbComp ℕ)}[x = 7] = 1 := by simp

/--
error: `return` is not allowed at the top level of the braces: the sequence's bindings are what
the event observes; bind a computation that returns early as `let x ← (do …)`
-/
#guard_msgs (whitespace := lax) in
noncomputable example : ℝ≥0∞ :=
  Pr{let mut s := 0; for i in [1, 2] do if i = 1 then return s}[s = 0]

/-- error: an event needs a draw: the braces hold only `let`s -/
#guard_msgs in
#check Pr{let y := 1}[y = 1]

/-! Goals display the draws as `let` statements on one line when they fit, an unused draw as
`_`, and an eta-reduced final selector applied to a name no draw binds. -/

/-- info: Pr{let x ← mx; let y ← my x}[y = 3 ∧ x = true] : ℝ≥0∞ -/
#guard_msgs in
#check Pr{let x ← mx; let y ← my x}[y = 3 ∧ x]

variable (q : ℕ → Prop) in
/-- info: Pr{let x ← mx; let y ← my x}[q y] : ℝ≥0∞ -/
#guard_msgs in
#check Pr{let x ← mx; let y ← my x}[q y]

/-- info: Pr{let x ← mz}[x = 3] : ℝ≥0∞ -/
#guard_msgs in
#check Pr{let x ← mz}[x = 3]

variable (S : Set ℕ) in
/-- info: Pr{let x ← mx; let y ← my x}[y ∈ S] : ℝ≥0∞ -/
#guard_msgs in
#check Pr{let x ← mx; let y ← my x}[y ∈ S]

/-- info: Pr{let _ ← mx; let y ← mz}[y = 3] : ℝ≥0∞ -/
#guard_msgs in
#check Pr{let _ ← mx; let y ← mz}[y = 3]

/-- info: Pr{let x ← mx >>= my}[x = 3] : ℝ≥0∞ -/
#guard_msgs in
#check Pr{let x ← mx >>= my}[x = 3]

variable (g : ℕ → ℝ≥0∞) in
/-- info: 𝔼{let x ← mz}[g x] : ℝ≥0∞ -/
#guard_msgs in
#check wp⟦mz⟧ g

/-- info: prFail mz : ℝ≥0∞ -/
#guard_msgs in
#check prFail mz

/--
trace: mx : ProbComp Bool
my : Bool → ProbComp ℕ
mz : ProbComp ℕ
h : Pr{let b ← mx; let y ← my b}[y = 3] = 0
⊢ Pr{let b ← mx; let x ← my b}[x = 3] = 0
-/
#guard_msgs in
/-- `simp` brings an explicit event to the normal form and keeps the program's binder names: `b`
from the bind, `x` from the map `(· = 3)`. -/
example (h : Pr{let b ← mx; let y ← my b}[y = 3] = 0) :
    wp⟦mx >>= fun b => (· = 3) <$> my b⟧ (predInd fun p => p) = 0 := by
  simp only [expect_norm]
  trace_state
  exact h

/-- `simp` keeps the notation in normal form and applies laws keyed on the head constant. -/
example (p : ℕ → Prop) (h : Pr{let x ← mz}[p x] = 0) : Pr{let x ← mz}[p x] = 0 := by
  fail_if_success simp only [bind_pure_comp] at h
  exact h

example (a : ℕ) : Pr{let x ← (pure a : ProbComp ℕ)}[x = a] = 1 := by simp

/-- A derived uniform program is closed by the uniform law after `simp` merges its maps. -/
example : Pr{let x ← (not <$> ($ᵗ Bool : ProbComp Bool))}[x = true] = 2⁻¹ := by
  simp [Finset.filter_insert, Finset.filter_singleton]

/-- Goals display in the draw form. -/
example : Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] = Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] := by
  guard_target =ₛ Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] = Pr{let x ← mx; let y ← my x}[y = 3 ∧ x]
  rfl

end eventNotation

/-! ### Expectation notation

`𝔼{items}[b]` is the nested expectation of the draws of `items`, observing `b`: a term of the
same shape as an event, whose innermost observation is the value rather than an indicator. Every
expectation under the measure interpretation displays as the notation it elaborates from. -/

section expectationNotation

open Lean.Order Std.WP

variable (mx : ProbComp Bool) (my : Bool → ProbComp ℕ) (mz : ProbComp ℕ) (g : ℕ → ℝ≥0∞)
  (f : Bool → ℕ → ℝ≥0∞)

/-! The translation. -/

example : 𝔼{let x ← mz}[g x] = wp⟦mz⟧ g := rfl
example : 𝔼{let x ← mx; let y ← my x}[f x y] = wp⟦mx⟧ fun x => wp⟦my x⟧ fun y => f x y := rfl
example : 𝔼{let y ← mx >>= my}[g y] = wp⟦mx >>= my⟧ g := rfl
example : 𝔼{let y ← mx >>= my}[g y] = wp⟦mx⟧ fun x => wp⟦my x⟧ fun y => g y := by
  simp only [expect_norm]
example : 𝔼{let x ← not <$> mx; let y ← my x}[g y] = wp⟦mx⟧ fun x => wp⟦my (!x)⟧ g := by
  simp only [expect_norm]
example (a : ℕ) : 𝔼{let x ← (pure a : ProbComp ℕ)}[g x] = g a := by simp only [expect_norm]
example (t : ℕ → Prop) : 𝔼{let x ← mz}[propInd (t x)] = Pr{let x ← mz}[t x] := rfl

/-! Display. -/

/-- info: 𝔼{let x ← mx; let y ← my x}[f x y] : ℝ≥0∞ -/
#guard_msgs in
#check 𝔼{let x ← mx; let y ← my x}[f x y]

/-- info: 𝔼{let x ← mx; let y ← my x}[f x y * 2] : ℝ≥0∞ -/
#guard_msgs in
#check 𝔼{let x ← mx; let y ← my x}[f x y * 2]

/-- info: 𝔼{let _ ← mz}[1] : ℝ≥0∞ -/
#guard_msgs in
#check 𝔼{let _ ← mz}[(1 : ℝ≥0∞)]

/-- info: 𝔼{let x ← mx >>= my}[g x] : ℝ≥0∞ -/
#guard_msgs in
#check wp⟦mx >>= my⟧ g

open Lean Elab Command Term Meta in
/-- Elaborate a term, display it, and check that the display elaborates back to the same term, up
to binder names, eta and reducible unfolding. -/
elab "guard_roundtrip " t:term : command => runTermElabM fun _ => do
  let e ← instantiateMVars (← withSynthesize (elabTerm t none))
  let stx ← PrettyPrinter.delab e
  let e' ← instantiateMVars (← withSynthesize (elabTerm stx none))
  unless ← withReducible (isDefEq e e') do
    throwError m!"the display{indentD stx}\nelaborates to{indentExpr e'}\nnot to{indentExpr e}"

guard_roundtrip 𝔼{let x ← mx; let y ← my x}[f x y]
guard_roundtrip wp⟦mz⟧ g
guard_roundtrip 𝔼{let x ← mx; let y ← my x}[propInd (y = 3) * f x y]
guard_roundtrip Pr{let x ← mx; let y ← my x}[y = 3]
guard_roundtrip Pr{let x : Bool ← mx}[x]
guard_roundtrip Pr{let _ ← mx; let y ← mz}[y = 3]
guard_roundtrip Pr{let ⟨a, b⟩ ← (mz >>= fun a => (a, ·) <$> mz)}[a = b]
guard_roundtrip Pr{let x ← mz; let y := x + 1}[y = 3]
guard_roundtrip Pr{let x ← mx >>= my}[x = 3]
guard_roundtrip Pr{let x ← not <$> mx}[x]
guard_roundtrip wp⟦mx >>= my⟧ g

section mixedMonads

variable (outer : ProbComp Bool) (inner : OptionT ProbComp Bool) (p : Bool → Bool → Prop)

guard_roundtrip 𝔼{let x ← outer}[Pr{let y ← inner}[p x y]]
guard_roundtrip Pr{let x ← outer; let y ← inner}[p x y]

end mixedMonads

/-- A computation behind a reducible definition. -/
abbrev wrapped (mz : ProbComp ℕ) : ProbComp ℕ := mz

guard_roundtrip wp⟦wrapped (pure 1)⟧ g

namespace interpretationDisplay

/-- A coin interpretation concentrating all mass on `true`. -/
@[reducible] noncomputable def alwaysTrue : OracleSpec.AnswerMeasure coinSpec where
  toMeasure _ := Measure.dirac true
  isProbabilityMeasure _ := by
    let : MeasurableSpace Bool := (_root_.Top.top : MeasurableSpace Bool)
    infer_instance

/-- The true event under the concentrated coin interpretation. -/
noncomputable def biasedEvent : ℝ≥0∞ :=
  letI : OracleSpec.AnswerMeasure coinSpec := alwaysTrue
  Pr{let b ← (HasQuery.query (spec := coinSpec) () : OracleComp coinSpec Bool)}[b = true]

/-- A numeric expectation under the concentrated coin interpretation. -/
noncomputable def biasedExpectation : ℝ≥0∞ :=
  letI : OracleSpec.AnswerMeasure coinSpec := alwaysTrue
  𝔼{let b ← (HasQuery.query (spec := coinSpec) () : OracleComp coinSpec Bool)}[if b then 2 else 0]

/-- The fair answer measure, made explicit to isolate the display canary from other fixtures. -/
noncomputable local instance : OracleSpec.AnswerMeasure coinSpec :=
  OracleSpec.UniformAnswerMeasure.coinSpec.toAnswerMeasure

/-- The true event under the fair coin interpretation. -/
noncomputable def fairEvent : ℝ≥0∞ :=
  Pr{let b ← (HasQuery.query (spec := coinSpec) () : OracleComp coinSpec Bool)}[b = true]

/-- A different expectation interpretation with the ambient fair answer measures unchanged. -/
@[reducible] noncomputable def alternativeWP : ExpectationWP (OracleComp coinSpec) EStack⟨⟩ :=
  letI : OracleSpec.AnswerMeasure coinSpec := alwaysTrue
  inferInstance

/-- The true event under the alternative expectation interpretation. -/
noncomputable def reinterpretedEvent : ℝ≥0∞ :=
  letI : ExpectationWP (OracleComp coinSpec) EStack⟨⟩ := alternativeWP
  Pr{let b ← (HasQuery.query (spec := coinSpec) () : OracleComp coinSpec Bool)}[b = true]

example : biasedEvent = 1 := by
  let : OracleSpec.AnswerMeasure coinSpec := alwaysTrue
  change Pr{let b ← (HasQuery.query (spec := coinSpec) () : OracleComp coinSpec Bool)}[b = true] = 1
  rw [OracleComp.ProgramLogic.wp_HasQuery_query]
  change (letI : MeasurableSpace Bool := (_root_.Top.top : MeasurableSpace Bool)
    ∫⁻ u : Bool, propInd (u = true) ∂Measure.dirac true) = 1
  simp

example : fairEvent = 2⁻¹ := by simp [fairEvent]

example : reinterpretedEvent = 1 := by
  change biasedEvent = 1
  let : OracleSpec.AnswerMeasure coinSpec := alwaysTrue
  change Pr{let b ← (HasQuery.query (spec := coinSpec) () : OracleComp coinSpec Bool)}[b = true] = 1
  rw [OracleComp.ProgramLogic.wp_HasQuery_query]
  change (letI : MeasurableSpace Bool := (_root_.Top.top : MeasurableSpace Bool)
    ∫⁻ u : Bool, propInd (u = true) ∂Measure.dirac true) = 1
  simp

/-! Default interpretations display compactly; other interpretations expose their instances.
Each displayed body elaborates back to the original in the ambient fair context. -/

open Lean Elab Command Term Meta in
run_cmd liftTermElabM do
  for (name, compact, instanceName) in
      [(``fairEvent, true, ""), (``biasedEvent, false, "alwaysTrue"),
        (``reinterpretedEvent, false, "alternativeWP"),
        (``biasedExpectation, false, "alwaysTrue")] do
    let .defnInfo info ← getConstInfo name | throwError "expected a definition"
    let e := info.value
    let stx ← withOptions (pp.analyze.set · true) (PrettyPrinter.delab e)
    let rendered := (← PrettyPrinter.ppTerm stx).pretty
    if compact then
      unless stx.raw.isOfKind ``prEventStx do throwError "the default event lost compact notation"
    else
      if stx.raw.isOfKind ``prEventStx || stx.raw.isOfKind ``expectStx then
        throwError "the display hides a different interpretation"
      unless (rendered.splitOn instanceName).length > 1 do
        throwError m!"the display hides {instanceName}: {rendered}"
    let e' ← instantiateMVars (← withSynthesize (elabTerm stx none))
    unless ← withReducibleAndInstances (isDefEq e e') do
      throwError m!"the displayed interpretation does not round-trip: {rendered}"

end interpretationDisplay

end expectationNotation

end VCVioTest.ProbabilityNotation
