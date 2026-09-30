/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.ProbabilityNotation
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

These examples exercise the same `Pr{...}[...]` syntax with a finite computation,
an optional computation, and a continuous oracle interpreted only by measures.
-/

public section

open MeasureTheory ProbabilityTheory OracleComp PFunctor ProbComp
open scoped ENNReal

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
  rw [prEvent_eq_evalDist_of_discrete]
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

open VCVioTest.MeasureSemantics in
example :
    Pr{let x ← (FreeM.lift PUnit.unit : FreeM gaussSpec ℝ)}[x > 0] =
      gaussianReal 0 1 {x | x > 0} := by
  rw [prEvent_def, map_eq_bind_pure_comp, Function.comp_def,
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
    Pr{let x ← (pure (1 : ℝ) : OptionT (FreeM gaussSpec) ℝ)}[x = 1] = 1 := by
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

`Pr{items}[t]` is the probability that the `do` sequence `items; return t` returns a true
proposition, `prEvent (do items; return t) fun b => b`. It is stored in the normal form `simp`
produces: every draw but the last becomes an expectation `wp⟦a⟧ fun x => …`, the last draw an
event, and goals display the draws as `let` statements. -/

section eventNotation

variable (mx : ProbComp Bool) (my : Bool → ProbComp ℕ) (mz : ProbComp ℕ)

/-! The specification: the notation equals the event of its literal `do` sequence. -/

example : Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] =
    prEvent (do let x ← mx; let y ← my x; return (y = 3 ∧ x = true)) fun b => b := by
  simp only [prEvent_norm]
example (m₁ m₂ : ProbComp ℕ) : Pr{let b ← $ᵗ Bool; let x ← if b then m₁ else m₂}[x = 3] =
    prEvent (do let b ← $ᵗ Bool; let x ← (if b then m₁ else m₂); return (x = 3)) fun b => b := by
  simp only [prEvent_norm]
example (mo : ProbComp (Option ℕ)) :
    Pr{let o ← mo; let x ← match o with | some a => pure a | none => mz}[x = 1] =
      prEvent (do
        let o ← mo
        let x ← match o with | some a => pure a | none => mz
        return (x = 1)) fun b => b := by
  simp only [prEvent_norm]

/-! The normal form. -/

example : Pr{let x ← mx}[x = true] = prEvent mx fun x => x = true := rfl
example : Pr{let x ← mx}[x] = prEvent mx fun x => x = true := rfl
example : Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] =
    wp⟦mx⟧ fun x => prEvent (my x) fun y => y = 3 ∧ x = true := rfl
example : Pr{let x ← mx >>= my}[x = 3] = wp⟦mx⟧ fun x => prEvent (my x) fun y => y = 3 := rfl
example : Pr{let x ← not <$> mx}[x] = prEvent mx fun x => (!x) = true := rfl
example : Pr{let x : Bool ← mx}[x] = Pr{let x ← mx}[x = true] := rfl
example : Pr{let x ← mz}[x = 3] = prEvent mz fun z => z = 3 := rfl
example : Pr{{let x ← mx}}[x] = Pr{let x ← mx}[x] := rfl
example : Pr{
    let x ← mz
    let y := x + 1}[y = 3] = prEvent mz fun x => x + 1 = 3 := rfl
example (a : ℕ) : Pr{let x ← (pure a : ProbComp ℕ)}[x = 3] = propInd (a = 3) := rfl

/-- A draw whose action continues on the following lines is laid out as in a `do` block, or its
action is parenthesized. -/
example (f : ℕ → ℕ → ProbComp ℕ) : Pr{
    let x ← f
      1 2
    let y ← f x
      x}[x = y] = Pr{let x ← f 1 2; let y ← f x x}[x = y] := rfl
example (f : ℕ → ℕ → ProbComp ℕ) : Pr{let x ← (f
    1 2)}[x = 1] = Pr{let x ← f 1 2}[x = 1] := rfl

/-- The braces take any `do` sequence, and the event may mention all its bindings: pure `let`s,
nested actions, branches and `match` on the right of a draw, and `let mut` with loops. -/
example (f : ℕ → ℕ → ProbComp ℕ) :
    Pr{let z ← f (← mz) (← mz)}[z = 0] = Pr{let a ← mz; let b ← mz; let z ← f a b}[z = 0] := rfl
example (g : ℕ → ProbComp ℕ) :
    Pr{let mut s := 0; for i in [1, 2, 3] do s := s + (← g i)}[s = 3] =
      Pr{let a ← g 1; let b ← g 2; let c ← g 3}[a + b + c = 3] := by
  simp

/-- A single-constructor destructuring draw becomes projections, whether it is the last draw or
not, and whether its action is a term or a nested `do` block. -/
example (mp : ProbComp (ℕ × ℕ)) (init : ProbComp ℕ) (f : ℕ → ProbComp (ℕ × ℕ)) :
    Pr{let ⟨a, b⟩ ← mp}[a = b] = prEvent mp (fun z => z.1 = z.2) ∧
      Pr{let ⟨a, b⟩ ← do f (← init)}[a = b] =
        wp⟦init⟧ fun x => prEvent (f x) fun z => z.1 = z.2 :=
  ⟨rfl, rfl⟩
example (mp : ProbComp (ℕ × ℕ)) (g : ℕ → ProbComp ℕ) :
    Pr{let (a, b) ← mp; let c ← g a}[b = c] =
      wp⟦mp⟧ fun z => prEvent (g z.1) fun c => z.2 = c := rfl

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

variable (g : ℕ → ℝ≥0∞) in
/-- info: wp⟦mz⟧ g : ℝ≥0∞ -/
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
    prEvent (mx >>= fun b => (· = 3) <$> my b) (fun p => p) = 0 := by
  simp only [prEvent_norm]
  trace_state
  exact h

/-- `simp` keeps the notation in normal form and applies laws keyed on the head constant. -/
example (p : ℕ → Prop) (h : Pr{let x ← mz}[p x] = 0) : Pr{let x ← mz}[p x] = 0 := by
  fail_if_success simp only [bind_pure_comp] at h
  exact h

example (a : ℕ) : Pr{let x ← (pure a : ProbComp ℕ)}[x = a] = 1 := by simp

/-- A derived uniform program is closed by the uniform law after `simp` merges its maps. -/
example : Pr{let x ← (not <$> ($ᵗ Bool : ProbComp Bool))}[x = true] = 2⁻¹ := by
  simp [SampleableType.prEvent_uniformSample, Finset.filter_insert, Finset.filter_singleton]

/-- Goals display in the draw form. -/
example : Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] = Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] := by
  guard_target =ₛ Pr{let x ← mx; let y ← my x}[y = 3 ∧ x] = Pr{let x ← mx; let y ← my x}[y = 3 ∧ x]
  rfl

end eventNotation

end VCVioTest.ProbabilityNotation
