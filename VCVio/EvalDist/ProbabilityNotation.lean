/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Expectation
public import VCVio.Prelude.Core
public import VCVio.EvalDist.ProbabilityNotation.Elab
public import VCVio.EvalDist.ProbabilityNotation.Delab

/-!
# Event probabilities and expectations of computations

`𝔼{…}[…]` is the expectation of a nonnegative value after a `do`-style sequence of draws, and
`Pr{…}[…]` the probability of an event, the expectation of its indicator: `Pr{items}[t]` is
`𝔼{items}[𝟙⟦t⟧]`, and `Pr{let x ← mx}[x = a]` is the probability that `mx` returns `a`. Both are
translations of the sequence into nested core weakest preconditions under the expectation
interpretation `ExpectationWP` of each draw's monad
(`VCVio.EvalDist.ProbabilityNotation.Elab`):
```
Pr{let x ← mx; let y ← my x}[p x y] = wp⟦mx⟧ fun x => wp⟦my x⟧ (predInd fun y => p x y)
```
The term is the translation and nothing is rewritten at elaboration; a draw written as a bind, a
map or a `do` block stays as written, and `simp only [expect_norm]` brings it to the normal form
of a draw chain (below). Because the predicate is an argument of `predInd`, `simp` keys, `grind`
patterns and `gcongr` see it. Neither notation needs measurable structure on the outputs;
`prEvent_eq_evalDist_map` relates an event to the mass its selector puts on `True`.

The display inverts the translation (`VCVio.EvalDist.ProbabilityNotation.Delab`): an expectation
prints as the notation it elaborates from, `Pr{…}[…]` when it observes an indicator and
`𝔼{…}[…]` otherwise, so what is displayed elaborates back to the term displayed.

`prFail mx` is the probability that `mx` fails or does not terminate: the mass its
successful-output measure is missing.
-/

public section

open MeasureTheory
open scoped Std.WP
open scoped ENNReal

universe v

/-! ## Normal form

`simp only [expect_norm]` brings an expectation to the normal form of a draw chain, one nested
expectation per draw: PolyFun's exact `wp` equations for program structure
(`ExactWPMonad.wp_bind`, …), with the following pre-procedures for `bind` and `map`, which name
each new binder after the program's own, and the fold of an indicator observation into
`predInd`. A multi-draw `Pr{…}[…]` elaborates to this form directly; a draw written as a bind, a
map or a `do` block reaches it by this simp set. -/

public meta section Rewriting

open Lean Meta

namespace ProbabilityNotation

/-- Rewrite `e` with the equation `thm`, whose instance arguments not determined by unification
are synthesized. Returns the right side and the proof. -/
def rewriteWith? (thm : Name) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let pf ← mkConstWithFreshMVarLevels thm
  let (xs, bis, ty) ← forallMetaTelescopeReducing (← inferType pf)
  let some (_, lhs, rhs) := ty.eq? | return none
  unless ← isDefEq lhs e do return none
  for x in xs, bi in bis do
    if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
      let some inst ← synthInstance? (← inferType x) | return none
      unless ← isDefEq x inst do return none
  return some (← instantiateMVars rhs, ← instantiateMVars (mkAppN pf xs))

/-- Name the binder of the `i`-th argument of `e`, a `fun`, after `n`. -/
def renameArg (e : Expr) (i : Nat) (n : Name) : Expr :=
  let args := e.getAppArgs
  match args[i]? with
  | some (.lam _ ty b bi) => mkAppN e.getAppFn (args.set! i (.lam n ty b bi))
  | _ => e

/-- The binder name of `f`, when it is a `fun`. Names that `do` generates, such as the
discriminant of a destructuring draw or a lifted action, become `x`. -/
def lamName? (f : Expr) : Option Name :=
  match f.cleanupAnnotations with
  | .lam n .. => some (if n.eraseMacroScopes.toString.startsWith "__" then `x else n)
  | _ => none

/-- Rewrite `e` with `thm` and name the binder of the `i`-th argument of the result, a `fun`, after
the first binder among `src`, or `x` when none of them is a `fun`. -/
def namedStep (thm : Name) (e : Expr) (i : Nat) (src : Array Expr) : SimpM Simp.Step := do
  let some (rhs, pf) ← rewriteWith? thm e | return .continue
  let rhs := renameArg rhs i ((src.findSome? lamName?).getD `x)
  return .visit { expr := ← Core.betaReduce rhs, proof? := pf }

end ProbabilityNotation

end Rewriting

open Lean Meta Simp ProbabilityNotation in
/-- `ExactWPMonad.wp_bind`, naming the new binder after the continuation's. -/
simproc ↓ [simp, expect_norm] wp_bind_named
    (@Std.WP.WP.wp _ _ _ _ _ _ ?_ (_ >>= _) _ _) := fun e => do
  unless e.isAppOfArity ``Std.WP.WP.wp 10 do return .continue
  let mb := e.getArg! 7
  unless mb.isAppOfArity ``Bind.bind 6 do return .continue
  namedStep ``ExactWPMonad.wp_bind e 8 #[mb.getArg! 5]

open Lean Meta Simp ProbabilityNotation in
/-- `ExactWPMonad.wp_map`, naming the observation's binder after the map's. -/
simproc ↓ [simp, expect_norm] wp_map_named
    (@Std.WP.WP.wp _ _ _ _ _ _ ?_ (_ <$> _) _ _) := fun e => do
  unless e.isAppOfArity ``Std.WP.WP.wp 10 do return .continue
  let mb := e.getArg! 7
  unless mb.isAppOfArity ``Functor.map 6 do return .continue
  namedStep ``ExactWPMonad.wp_map e 8 #[mb.getArg! 4, e.getArg! 8]

open Lean Meta Simp in
/-- An indicator observation `fun x => propInd t` is the indicator `predInd (fun x => t)` of its
predicate, eta-reduced, so that an event's predicate is an argument of its observation; the
observation `propInd` of a proposition-valued computation is `predInd (fun b => b)`. The two are
equal by definition. -/
simproc [simp, expect_norm] wp_predInd_fold
    (@Std.WP.WP.wp _ _ _ _ _ _ ?_ _ _ _) := fun e => do
  unless e.isAppOfArity ``Std.WP.WP.wp 10 do return .continue
  let some pred := ProbabilityNotation.indicatorPred? (e.getArg! 8) | return .continue
  let obs ← mkAppM ``predInd #[pred]
  return .visit { expr := mkAppN e.getAppFn (e.getAppArgs.set! 8 obs) }

/-- An indicator observation is the indicator of its predicate, by definition. `simp` folds it
through the simproc `wp_predInd_fold`; `grind` normalizes with this lemma. -/
@[grind norm]
theorem wp_fun_propInd {m : Type → Type v} [Monad m] {EPred : Type} [Std.WP.Assertion EPred]
    [ExpectationWP m EPred] {α : Type} (mx : m α) (p : α → Prop) :
    wp⟦mx⟧ (fun a => propInd (p a)) = wp⟦mx⟧ (predInd p) := rfl

attribute [expect_norm] ExactWPMonad.wp_pure ExactWPMonad.wp_bind ExactWPMonad.wp_map
  ExactWPMonad.wp_seq ExactWPMonad.wp_seqLeft ExactWPMonad.wp_seqRight ExactWPMonad.wp_ite
  ExactWPMonad.wp_dite ExactWPMonad.wp_option_elim ExactWPMonad.wp_sum_elim predInd_apply
  ExactWPMonad.wp_seq ExactWPMonad.wp_seqLeft ExactWPMonad.wp_seqRight ExactWPMonad.wp_ite
  ExactWPMonad.wp_dite ExactWPMonad.wp_option_elim ExactWPMonad.wp_sum_elim predInd_apply

/-! ## Events through program structure

An event is the expectation of the indicator `predInd p` of its predicate, so PolyFun's exact `wp`
equations move it through program structure; `simp` applies them. The following state what they
give for events. -/

section Structure

variable {m : Type → Type v} [Monad m] {EPred : Type} [Std.WP.Assertion EPred]
  [ExpectationWP m EPred] {α β : Type}

/-- An event after a bind is the expectation, over the first computation, of the event after
each continuation. -/
theorem prEvent_bind (mx : m α) (f : α → m β) (p : β → Prop) :
    wp⟦mx >>= f⟧ (predInd p) = Pr{let x ← mx; let y ← f x}[p y] :=
  ExpectationWP.wp_bind mx f _

/-- An event of mapped outputs is the event of the composed predicate. -/
theorem prEvent_map (mx : m α) (f : α → β) (p : β → Prop) :
    wp⟦f <$> mx⟧ (predInd p) = Pr{let x ← mx}[p (f x)] :=
  ExpectationWP.wp_map f mx _

/-- An event of a returned value is the indicator of the predicate at that value. -/
theorem prEvent_pure (a : α) (p : α → Prop) :
    wp⟦(pure a : m α)⟧ (predInd p) = propInd (p a) :=
  ExpectationWP.wp_pure a _

/-- An event of a conditional computation is the conditional event. -/
theorem prEvent_ite (c : Prop) [Decidable c] (mx my : m α) (p : α → Prop) :
    wp⟦if c then mx else my⟧ (predInd p) =
      if c then Pr{let x ← mx}[p x] else Pr{let x ← my}[p x] := by
  split <;> rfl

/-- An event of a dependent conditional computation is the dependent conditional event. -/
theorem prEvent_dite (c : Prop) [Decidable c] (mx : c → m α) (my : ¬c → m α) (p : α → Prop) :
    wp⟦if h : c then mx h else my h⟧ (predInd p) =
      if h : c then Pr{let x ← mx h}[p x] else Pr{let x ← my h}[p x] := by
  split <;> rfl

end Structure

/-! ## Constants and indicators -/

section Indicators

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α : Type}

/-- A constant observation has the expectation of the constant times the success mass. -/
@[simp]
theorem wp_const (mx : m α) (c : ℝ≥0∞) : wp⟦mx⟧ (fun _ => c) = c * Pr{let _ ← mx}[True] := by
  simpa only [predInd_apply, propInd_true, mul_one] using ExpectationWP.wp_const_mul mx c
    (predInd fun _ ↦ True)

/-- An indicator observation scaled on the right is the scaled event. -/
@[simp]
theorem wp_propInd_mul (mx : m α) (p : α → Prop) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun a => propInd (p a) * c) = Pr{let x ← mx}[p x] * c :=
  ExpectationWP.wp_mul_const mx _ c

/-- An indicator observation scaled on the left is the scaled event. -/
@[simp]
theorem wp_mul_propInd (mx : m α) (p : α → Prop) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun a => c * propInd (p a)) = c * Pr{let x ← mx}[p x] :=
  ExpectationWP.wp_const_mul mx c _

end Indicators


/-! ## Events as measures -/

section Measures

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β : Type}

/-- An event is the mass its propositional selector puts on `True`. It needs no measurable
structure on the outputs. -/
theorem prEvent_eq_evalDist_map (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 𝒟[p <$> mx] {True} := by
  have hind : (propInd : Prop → ℝ≥0∞) = Set.indicator {True} 1 := by
    classical
    funext b
    by_cases hb : b <;> simp [propInd, hb]
  change wp⟦mx⟧ (fun x ↦ propInd (p x)) = _
  rw [← ExpectationWP.wp_map p mx propInd,
    ExpectationWP.wp_eq_lintegral (p <$> mx) propInd Measurable.of_discrete, hind,
    lintegral_indicator_one (measurableSet_singleton True)]

/-- A family of events is measurable when the measures of its selectors are. -/
theorem measurable_prEvent {ρ : Type*} [MeasurableSpace ρ] {f : ρ → m α} {p : α → Prop}
    (hf : Measurable fun r ↦ 𝒟[p <$> f r]) : Measurable fun r ↦ Pr{let x ← f r}[p x] := by
  simpa only [prEvent_eq_evalDist_map, Function.comp_def] using
    (Measure.measurable_coe (measurableSet_singleton True)).comp hf

/-- The mass a proposition-valued computation puts on `True` is the event that it returns a true
proposition. -/
@[simp, grind norm]
theorem evalDist_singleton_true (mx : m Prop) : 𝒟[mx] {True} = Pr{let b ← mx}[b] := by
  have h := prEvent_eq_evalDist_map mx fun b ↦ b
  rw [id_map'] at h
  exact h.symm

/-- A measurable predicate returned by a computation has the probability of its event. -/
theorem prEvent_eq_evalDist [MeasurableSpace α] (mx : m α) (p : α → Prop) (hp : Measurable p) :
    Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} := by
  rw [prEvent_eq_evalDist_map, evalDist_map_apply mx hp (measurableSet_singleton True)]
  simp

/-- On a discrete output space every predicate is a measurable event. -/
theorem prEvent_eq_evalDist_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} :=
  prEvent_eq_evalDist mx p Measurable.of_discrete

/-- Equality to one output has its singleton mass whenever singletons are measurable. -/
theorem prEvent_eq_evalDist_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : m α) (a : α) : Pr{let x ← mx}[x = a] = 𝒟[mx] {a} := by
  simpa only [Set.ofPred_eq_eq_singleton] using
    prEvent_eq_evalDist mx (fun x ↦ x = a) (measurableSet_singleton a).mem

/-- A final decidable event has the same success mass whether it is returned as a proposition
or decided to a Boolean; no measurable structure on intermediate values is needed. -/
theorem prEvent_eq_evalDist_decide (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← mx}[p x] = 𝒟[do let x ← mx; return decide (p x)] {true} := by
  classical
  calc
    _ = 𝒟[p <$> mx] {True} := prEvent_eq_evalDist_map mx p
    _ = 𝒟[(fun b : Prop ↦ decide b) <$> (p <$> mx)] {true} := by
      rw [evalDist_map_apply (p <$> mx)
        (Measurable.of_discrete : Measurable fun b : Prop ↦ decide b)
        (measurableSet_singleton true)]
      congr 1
      ext b
      simp
    _ = _ := by
      congr 1
      congr 1
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      apply bind_congr
      intro x
      by_cases hx : p x <;> simp [hx]

/-- The trivially true event is the successful mass of the computation, in any measurable
structure on its outputs. -/
theorem prEvent_true_eq_evalDist_apply_univ [MeasurableSpace α] (mx : m α) :
    Pr{let _ ← mx}[True] = 𝒟[mx] Set.univ := by
  rw [prEvent_eq_evalDist_map,
    evalDist_map_apply mx measurable_const (measurableSet_singleton True)]
  simp

end Measures

/-! ## Order and bounds -/

section Bounds

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β γ : Type}

/-- Every event probability is at most one. -/
@[simp]
theorem prEvent_le_one (mx : m α) {p : α → Prop} : Pr{let x ← mx}[p x] ≤ 1 := by
  rw [prEvent_eq_evalDist_map]
  exact evalDist_apply_le_one _ _

/-- Every event probability is finite. -/
@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem prEvent_ne_top (mx : m α) {p : α → Prop} : Pr{let x ← mx}[p x] ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one mx)

/-- Every event probability is finite. -/
@[simp]
theorem prEvent_lt_top (mx : m α) {p : α → Prop} : Pr{let x ← mx}[p x] < ⊤ :=
  (prEvent_ne_top mx).lt_top

/-- Pointwise equivalent predicates have the same probability after a common computation. -/
theorem prEvent_congr (mx : m α) (p q : α → Prop) (h : ∀ x, p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  rw [show p = q from funext fun x ↦ propext (h x)]

/-- A true constant event after a lossless draw has probability one. -/
theorem prEvent_const_of_lossless (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1) {c : Prop}
    (hc : c) : Pr{let _ ← mx}[c] = 1 := by
  rw [← hmx]
  exact prEvent_congr mx _ _ fun _ ↦ by simp [hc]

/-- Measurable predicates agreeing almost everywhere have equal event probabilities. -/
theorem prEvent_congr_ae [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (h : ∀ᵐ x ∂𝒟[mx], p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_congr (h.mono fun _ hx ↦ propext hx)

/-- An event that never occurs has probability zero. -/
theorem prEvent_eq_zero_of_forall_not (mx : m α) (p : α → Prop) (h : ∀ x, ¬p x) :
    Pr{let x ← mx}[p x] = 0 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  simp [h]

/-- An impossible final observation has zero mass, including after a failed computation. -/
@[simp↓ high, grind norm↓]
theorem prEvent_false (mx : m α) : Pr{let _ ← mx}[False] = 0 :=
  prEvent_eq_zero_of_forall_not mx (fun _ ↦ False) (fun _ ↦ id)

/-- A false constant event has probability zero. -/
theorem prEvent_const_of_not (mx : m α) {c : Prop} (hc : ¬ c) : Pr{let _ ← mx}[c] = 0 :=
  prEvent_eq_zero_of_forall_not mx _ fun _ ↦ hc

/-- Almost-everywhere implication bounds probabilities of measurable events. -/
theorem prEvent_mono_ae [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (hpq : ∀ᵐ x ∂𝒟[mx], p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_mono_ae hpq

/-- Implication between events bounds their probabilities. -/
theorem prEvent_mono (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] :=
  ExpectationWP.wp_mono mx fun x ↦ propInd_mono (hpq x)

/-- A constant event conjoined on the left factors out as its indicator. -/
theorem prEvent_const_and_left (mx : m α) (P : Prop) (q : α → Prop) :
    Pr{let x ← mx}[P ∧ q x] = propInd P * Pr{let x ← mx}[q x] := by
  classical
  by_cases hP : P
  · simp [hP]
  · simp [hP]

/-- A constant event conjoined on the right factors out as its indicator. -/
theorem prEvent_const_and_right (mx : m α) (P : Prop) (q : α → Prop) :
    Pr{let x ← mx}[q x ∧ P] = Pr{let x ← mx}[q x] * propInd P := by
  rw [mul_comm, ← prEvent_const_and_left]
  exact prEvent_congr mx _ _ fun _ ↦ and_comm

/-- Events of independent draws have the product of their probabilities. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_bind_and (mx : m α) (my : m β) (p : α → Prop) (q : β → Prop) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] = Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] := by
  simp only [prEvent_const_and_left, wp_propInd_mul]

/-- An expectation of an observation bounded by a constant is at most that constant. -/
theorem wp_le_of_forall_le (mx : m α) {g : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, g x ≤ c) :
    wp⟦mx⟧ g ≤ c :=
  (ExpectationWP.wp_mono mx h).trans <| by
    rw [wp_const]
    exact mul_le_of_le_one_right' (prEvent_le_one mx)

/-- After a lossless computation, an observation bounded below by a constant has at least that
expectation. -/
theorem le_wp_of_forall_le (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1) {g : α → ℝ≥0∞}
    {c : ℝ≥0∞} (h : ∀ x, c ≤ g x) : c ≤ wp⟦mx⟧ g :=
  le_of_eq_of_le (by rw [wp_const, hmx, mul_one]) (ExpectationWP.wp_mono mx h)

/-- An expectation after a bind is at most the bound on each continuation's expectation. -/
theorem wp_le_prEvent_add (mx : m α) (bad : α → Prop) (g : α → ℝ≥0∞) {ε : ℝ≥0∞}
    (hg : ∀ x, ¬bad x → g x ≤ ε) (hle : ∀ x, g x ≤ 1) :
    wp⟦mx⟧ g ≤ Pr{let x ← mx}[bad x] + ε := by
  calc wp⟦mx⟧ g ≤ wp⟦mx⟧ fun x => propInd (bad x) + ε :=
        ExpectationWP.wp_mono mx fun x => by
          classical
          by_cases h : bad x
          · simpa [h] using (hle x).trans le_self_add
          · simpa [h] using hg x h
    _ ≤ Pr{let x ← mx}[bad x] + ε := by
        rw [ExpectationWP.wp_add, wp_const]
        exact add_le_add le_rfl (mul_le_of_le_one_right' (prEvent_le_one mx))

end Bounds

/-! ## Integrals and sums -/

section Sums

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β γ : Type}

/-- An expectation over a finite type is the finite sum of the point masses times the
observation. -/
theorem wp_eq_sum_fintype [Fintype α] (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = ∑ a, Pr{let x ← mx}[x = a] * g a := by
  let : MeasurableSpace α := ⊤
  rw [ExpectationWP.wp_eq_lintegral mx g Measurable.of_discrete, lintegral_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, prEvent_eq_evalDist_singleton]

/-- An expectation over a countable type is the sum of the point masses times the
observation. -/
theorem wp_eq_tsum_of_countable [Countable α] (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = ∑' a, Pr{let x ← mx}[x = a] * g a := by
  let : MeasurableSpace α := ⊤
  rw [ExpectationWP.wp_eq_lintegral mx g Measurable.of_discrete, lintegral_countable']
  refine tsum_congr fun a => ?_
  rw [mul_comm, prEvent_eq_evalDist_singleton]

/-- An event after a bind integrates the event probability of each measurable continuation.
Only the common draw needs a selected measurable space; the continuation is observed in `Prop`.
-/
theorem prEvent_bind_eq_lintegral [MeasurableSpace α] (mx : m α) (f : α → m β) (p : β → Prop)
    (hf : Measurable fun x ↦ 𝒟[p <$> f x]) :
    Pr{let x ← mx; let y ← f x}[p y] = ∫⁻ x, Pr{let y ← f x}[p y] ∂𝒟[mx] :=
  ExpectationWP.wp_eq_lintegral mx _ (measurable_prEvent hf)

/-- A discrete common draw discharges the observed continuation's measurability. -/
theorem prEvent_bind_eq_lintegral_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (f : α → m β) (p : β → Prop) :
    Pr{let x ← mx; let y ← f x}[p y] = ∫⁻ x, Pr{let y ← f x}[p y] ∂𝒟[mx] :=
  prEvent_bind_eq_lintegral mx f p Measurable.of_discrete

/-- AE equality of measurable observed continuation probabilities gives equality after a draw. -/
theorem prEvent_bind_congr_ae [MeasurableSpace α] (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop) (hf : Measurable fun x ↦ 𝒟[p <$> f x])
    (hg : Measurable fun x ↦ 𝒟[q <$> g x])
    (h : ∀ᵐ x ∂𝒟[mx], Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) :
    Pr{let x ← mx; let y ← f x}[p y] = Pr{let x ← mx; let z ← g x}[q z] := by
  rw [prEvent_bind_eq_lintegral mx f p hf, prEvent_bind_eq_lintegral mx g q hg]
  exact lintegral_congr_ae h

/-- Pointwise equality of observed continuation probabilities gives equality after a common
draw. -/
theorem prEvent_bind_congr (mx : m α) (f : α → m β) (g : α → m γ) (p : β → Prop) (q : γ → Prop)
    (h : ∀ x, Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) :
    Pr{let x ← mx; let y ← f x}[p y] = Pr{let x ← mx; let z ← g x}[q z] :=
  ExpectationWP.wp_congr mx h

/-- After a draw from a finite type, an event is the finite sum of the draw's point masses times
the conditional event probabilities. -/
theorem prEvent_bind_eq_sum_fintype [Fintype α] (mx : m α) (f : α → m β) (p : β → Prop) :
    Pr{let x ← mx; let y ← f x}[p y] = ∑ a, Pr{let x ← mx}[x = a] * Pr{let y ← f a}[p y] :=
  wp_eq_sum_fintype mx _

/-- After a draw from a countable type, an event is the sum of the draw's point masses times the
conditional event probabilities. -/
theorem prEvent_bind_eq_tsum_of_countable [Countable α] (mx : m α) (f : α → m β)
    (p : β → Prop) :
    Pr{let x ← mx; let y ← f x}[p y] = ∑' a, Pr{let x ← mx}[x = a] * Pr{let y ← f a}[p y] :=
  wp_eq_tsum_of_countable mx _

end Sums

/-! ## Failure

`prFail mx` is the mass the successful-output measure of `mx` is missing: the probability that
`mx` fails or does not terminate. It needs no measurable structure on the outputs. -/

section prFail

variable {m : Type → Type v} [Monad m] {EPred : Type} [Std.WP.Assertion EPred]
  [ExpectationWP m EPred] {α : Type}

/-- The probability that a computation fails or does not terminate: the mass its successful-output
measure is missing, under the expectation interpretation of its monad. -/
@[expose] noncomputable def prFail {α : Type} (mx : m α) : ℝ≥0∞ :=
  1 - Pr{let _ ← mx}[True]

theorem prFail_def (mx : m α) : prFail mx = 1 - Pr{let _ ← mx}[True] := rfl

end prFail

section prFailMeasure

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α : Type}


/-- Success and failure masses add up to one. -/
@[simp]
theorem prEvent_true_add_prFail (mx : m α) : Pr{let _ ← mx}[True] + prFail mx = 1 :=
  add_tsub_cancel_of_le (prEvent_le_one _)

/-- Failure and success masses add up to one. -/
@[simp]
theorem prFail_add_prEvent_true (mx : m α) : prFail mx + Pr{let _ ← mx}[True] = 1 := by
  rw [add_comm, prEvent_true_add_prFail]

@[simp]
theorem prFail_le_one (mx : m α) : prFail mx ≤ 1 := tsub_le_self

@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem prFail_ne_top (mx : m α) : prFail mx ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prFail_le_one mx)

/-- A computation never fails exactly when it succeeds with probability one. -/
theorem prFail_eq_zero_iff (mx : m α) : prFail mx = 0 ↔ Pr{let _ ← mx}[True] = 1 := by
  rw [prFail_def, tsub_eq_zero_iff_le]
  exact ⟨fun h ↦ le_antisymm (prEvent_le_one _) h, fun h ↦ h.ge⟩

/-- A computation always fails exactly when it succeeds with probability zero. -/
theorem prFail_eq_one_iff (mx : m α) : prFail mx = 1 ↔ Pr{let _ ← mx}[True] = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [prFail_def, h, tsub_zero]⟩
  by_contra hne
  exact (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hne).ne h

/-- A pure computation never fails. -/
@[simp, grind =]
theorem prFail_pure (a : α) : prFail (pure a : m α) = 0 := by
  simp [prFail_def]

/-- The failure probability of a branch is that of the branch taken. -/
@[simp]
theorem prFail_ite (c : Prop) [Decidable c] (mx my : m α) :
    prFail (if c then mx else my) = if c then prFail mx else prFail my := by
  split_ifs <;> rfl

/-- Mapping the outputs does not change the failure probability. -/
@[simp, grind =]
theorem prFail_map {β : Type} (f : α → β) (mx : m α) : prFail (f <$> mx) = prFail mx := by
  rw [prFail_def, prFail_def, prEvent_map]

/-- The failure probability is the mass missing from the output measure. -/
theorem prFail_eq_one_sub_evalDist_univ [MeasurableSpace α] (mx : m α) :
    prFail mx = 1 - 𝒟[mx] Set.univ := by
  rw [prFail_def, prEvent_true_eq_evalDist_apply_univ]

end prFailMeasure
