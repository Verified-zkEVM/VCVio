/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public import PolyFun.Realizability.Quantitative.Closure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Computational-complexity soundness checks

These checks exercise the load-bearing parts of strict oracle complexity without selecting a
particular quantitative backend. In particular, an oracle contract filters traces by an explicit
dependent answer relation, but every allowed answer remains subject to pathwise cost and
termination bounds independently of its probability under a later semantics.
-/

public section

universe u v w x

open PFunctor
open PFunctor.DynSystem.DynComputation
open PFunctor.DynSystem.DynComputation.QuantitativeRealization

namespace OracleComp.Complexity.SoundnessTest

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output} {label : Type x} {labelOf : p.A → label}

/-! ## Contract-relative traces -/

/-- A typed reply rejected by the resource model cannot occur in a conforming trace. -/
theorem illegal_reply_not_conforming
    (model : OracleResourceModel Q bd.interface labelOf)
    (R : QuantitativeRealization Q bd) {state : R.machine.State} {position : p.A}
    {next : p.B position → R.machine.State}
    (view_eq : R.machine.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position) (hillegal : ¬model.allows position direction) :
    ¬(ExecutionTrace.query (R := R) view_eq direction
      (ExecutionTrace.nil (R := R) (next direction))).Conforms model.allows := by
  simpa [ExecutionTrace.Conforms] using hillegal

/-- Every reply admitted by the contract is charged even when a later probabilistic semantics
assigns that reply probability zero. The probability distribution is deliberately not an input to
`RunsWithinUnder`; pathwise complexity therefore cannot discard its zero-mass branches. -/
theorem allowed_zero_probability_reply_is_charged
    (model : OracleResourceModel Q bd.interface labelOf)
    (R : QuantitativeRealization Q bd) (bound : input → ExecutionCost) (value : input)
    {position : p.A} {next : p.B position → R.machine.State}
    (view_eq : R.machine.view (R.machine.init value) = Sum.inr ⟨position, next⟩)
    (direction : p.B position) (hallowed : model.allows position direction)
    (distribution : PMF (p.B position)) (hzero : distribution direction = 0)
    (hruns : R.RunsWithinUnder model.allows bound) :
    ∃ trace : ExecutionTrace R (R.machine.init value) (next direction),
      trace.length = 1 ∧ R.executionCost value trace ≤ bound value ∧
        distribution direction = 0 := by
  let trace : ExecutionTrace R (R.machine.init value) (next direction) :=
    .query view_eq direction (.nil _)
  have hconforms : trace.Conforms model.allows := by
    exact ⟨hallowed, True.intro⟩
  exact ⟨trace, rfl, hruns.cost_le value trace hconforms, hzero⟩

/-- A legal first reply must also enter a resolving continuation, regardless of its probability
under a later semantics. -/
theorem allowed_zero_probability_reply_resolves
    (model : OracleResourceModel Q bd.interface labelOf)
    (R : QuantitativeRealization Q bd) (bound : input → ExecutionCost) (value : input)
    {position : p.A} {next : p.B position → R.machine.State}
    (view_eq : R.machine.view (R.machine.init value) = Sum.inr ⟨position, next⟩)
    (direction : p.B position) (hallowed : model.allows position direction)
    (distribution : PMF (p.B position)) (hzero : distribution direction = 0)
    (hruns : R.RunsWithinUnder model.allows bound) :
    ∃ remaining,
      (bound value).queries = remaining + 1 ∧
        R.machine.ResolvesInUnder model.allows remaining (next direction) ∧
          distribution direction = 0 := by
  have hresolves := hruns.resolvesIn value
  cases hbudget : (bound value).queries with
  | zero =>
      rw [hbudget] at hresolves
      exact (R.machine.not_resolvesInUnder_query_zero model.allows _ position next view_eq
        hresolves).elim
  | succ remaining =>
      rw [hbudget] at hresolves
      have hnext :=
        (R.machine.resolvesInUnder_query_succ_iff model.allows remaining _ position next
          view_eq).mp hresolves direction hallowed
      exact ⟨remaining, rfl, hnext, hzero⟩

/-! ## Progress is non-vacuous -/

/-- A conformingly reachable query with an empty response type rules out every restricted
resource bound. This is independent of the numeric query budget. -/
theorem reachable_empty_response_not_runsWithinUnder
    (R : QuantitativeRealization Q bd) (allows : ∀ position, p.B position → Prop)
    (bound : input → ExecutionCost) (value : input) {state : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init value) state) (htrace : trace.Conforms allows)
    {position : p.A} {next : p.B position → R.machine.State}
    (view_eq : R.machine.view state = Sum.inr ⟨position, next⟩)
    [IsEmpty (p.B position)] : ¬R.RunsWithinUnder allows bound := by
  intro hruns
  obtain ⟨direction, _⟩ := hruns.response_exists value trace htrace view_eq
  exact isEmptyElim direction

/-! ## Executable evidence is explicit -/

#check QuantitativeStepClass.Realizer
#check QuantitativeRealization.initCode
#check QuantitativeRealization.headCode
#check QuantitativeRealization.updateCode
#check QuantitativeRealization.ofFn
#check isQuantitativelyRealizableBy_ofFn

/-- Even an immediately returning pure function enters the quantitative layer through explicit
backend code for that function. -/
theorem pure_function_of_explicit_realizer
    {f : input → output} [Q.HasSum] [Q.HasOption]
    (code : Q.Realizer bd.input bd.out f) :
    IsQuantitativelyRealizableBy Q bd fun value ↦ FreeM.pure (f value) :=
  isQuantitativelyRealizableBy_ofFn code

/-! ## Fair coins and exact structural accounting -/

section FairCoin

variable {coinInput coinOutput : Type} {CoinClass : StepClass}
  [CoinClass.HasProd] [CoinClass.HasSum] [CoinClass.HasOption]
  (CoinQ : QuantitativeStepClass CoinClass)
  (coinBoundary : Boundary CoinClass coinSpec.toPFunctor coinInput coinOutput)

/-- The canonical fair-coin contract admits both Boolean replies. -/
theorem fair_coin_allows_both_answers :
    (fairCoinResourceModel CoinQ coinBoundary.interface).allows PUnit.unit false ∧
      (fairCoinResourceModel CoinQ coinBoundary.interface).allows PUnit.unit true := by
  simp

/-- The `true` trace remains charged under the fair-coin answer contract even if an independent
semantics assigns all mass to `false`. This gives a concrete zero-probability instantiation of the
generic pathwise theorem above. -/
theorem fair_coin_true_is_charged_under_zero_mass_semantics
    (R : QuantitativeRealization CoinQ coinBoundary)
    (bound : coinInput → ExecutionCost) (value : coinInput)
    {next : Bool → R.machine.State}
    (view_eq : R.machine.view (R.machine.init value) = Sum.inr ⟨PUnit.unit, next⟩)
    (hruns : R.RunsWithinUnder
      (fairCoinResourceModel CoinQ coinBoundary.interface).allows bound) :
    ∃ trace : ExecutionTrace R (R.machine.init value) (next true),
      trace.length = 1 ∧ R.executionCost value trace ≤ bound value ∧
        (PMF.pure false : PMF Bool) true = 0 :=
  allowed_zero_probability_reply_is_charged
    (fairCoinResourceModel CoinQ coinBoundary.interface) R bound value view_eq true (by simp)
      (PMF.pure false) (by simp) hruns

end FairCoin

/-- The query component of execution cost is definitionally the trace length, and a restricted
run turns that exact identity into the advertised resource consequence for every conforming
trace. -/
theorem exact_query_resource_consequence
    (R : QuantitativeRealization Q bd) (allows : ∀ position, p.B position → Prop)
    (bound : input → ExecutionCost) (hruns : R.RunsWithinUnder allows bound)
    (value : input) {finish : R.machine.State}
    (trace : ExecutionTrace R (R.machine.init value) finish) (htrace : trace.Conforms allows) :
    (R.executionCost value trace).queries = trace.length ∧
      trace.length ≤ (bound value).queries :=
  ⟨R.queries_executionCost value trace, hruns.traceLength_le value trace htrace⟩

end OracleComp.Complexity.SoundnessTest
