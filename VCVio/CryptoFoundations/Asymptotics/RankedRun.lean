/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public import PolyFun.Realizability.Quantitative.BoundedClosure

/-!
# Ranked resource certificates for finite oracle computations

This module derives `QuantitativeRealization.RunsWithinUnder` from local, operational resource
inequalities. A certificate assigns each hidden state both a resource potential and a natural rank.
The potential pays for stopping at that state or for one enabled query followed by the next
potential. The rank strictly decreases along every allowed answer. A separate progress field
ensures that a querying state cannot satisfy the rank condition vacuously by admitting no answer.

The construction never assigns work to code. Every local cost is read directly from the
`QuantitativeStepClass` realizers already stored by the realization. Consequently it is useful for
small finite-state programs and bounded loops without weakening the backend-relative trust
boundary of `IsOraclePPTBy`.
-/

@[expose] public section

universe u v w x

namespace OracleComp.Complexity

open PFunctor
open PFunctor.DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output}

namespace RankedRun

/-! ## Local resource costs -/

/-- Cost of observing a state as the final state of an execution prefix. -/
def terminalCost (R : QuantitativeRealization Q bd) (state : R.machine.State) :
    ExecutionCost :=
  ExecutionCost.ofWork (Q.cost R.headCode state) +
    ExecutionCost.observe (Q.size R.state state) (Q.size bd.head (R.machine.head state))

/-- Cost contributed by one enabled query-answer transition. -/
def queryStepCost (R : QuantitativeRealization Q bd) (state : R.machine.State)
    (position : p.A) (direction : p.B position) : ExecutionCost :=
  ExecutionCost.ofWork (Q.cost R.headCode state) +
    ExecutionCost.ofWork (Q.cost R.updateCode (state, ⟨position, direction⟩)) +
    ExecutionCost.observe (Q.size R.state state) (Q.size bd.head (R.machine.head state)) +
    ExecutionCost.query (Q.size bd.pos position) (Q.size bd.idx ⟨position, direction⟩)

@[simp]
theorem executionTrace_cost_query {R : QuantitativeRealization Q bd}
    {state : R.machine.State} {position : p.A} {next : p.B position → R.machine.State}
    {finish : R.machine.State}
    (view_eq : R.machine.view state = Sum.inr ⟨position, next⟩)
    (direction : p.B position)
    (tail : R.ExecutionTrace (next direction) finish) :
    (QuantitativeRealization.ExecutionTrace.query (R := R) view_eq direction tail).cost =
      queryStepCost R state position direction + tail.cost :=
  rfl

/-- Split total prefix cost into initialization, transition cost, and the final observation. -/
theorem executionCost_eq_init_add_trace_add_terminal
    (R : QuantitativeRealization Q bd) (value : input) {finish : R.machine.State}
    (trace : R.ExecutionTrace (R.machine.init value) finish) :
    R.executionCost value trace =
      ExecutionCost.ofWork (Q.cost R.initCode value) +
        (trace.cost + terminalCost R finish) := by
  simp [QuantitativeRealization.executionCost, terminalCost, add_assoc]

/-! ## Ranked potential certificates -/

/-- Local evidence that every allowed execution prefix fits a bound and every allowed branch
terminates.

`potential` bounds the remaining resource use from a state. `toRankedRunCertificate.rank` bounds
its remaining number of queries. The query obligations mention the realization's actual
`headCode` and `updateCode` costs through `queryStepCost`; a caller cannot replace them with an
asserted meter. -/
structure ResourcePotentialCertificate (R : QuantitativeRealization Q bd)
    (allows : ∀ position, p.B position → Prop) (bound : input → ExecutionCost) where
  /-- Backend-independent termination and non-vacuous progress evidence from PolyFun. -/
  toRankedRunCertificate :
    PFunctor.DynSystem.DynComputation.RankedRunCertificate R allows
  /-- Resource potential available at each hidden state. -/
  potential : R.machine.State → ExecutionCost
  /-- Stopping a finite prefix at any state fits that state's potential. -/
  terminal_le : ∀ state, terminalCost R state ≤ potential state
  /-- One allowed transition and the successor potential fit the source potential. -/
  query_le : ∀ {state : R.machine.State} {position : p.A}
    {next : p.B position → R.machine.State},
    R.machine.view state = Sum.inr ⟨position, next⟩ →
      ∀ direction, allows position direction →
        queryStepCost R state position direction + potential (next direction) ≤
          potential state
  /-- Initialization work and the initial potential fit the advertised input bound. -/
  init_le : ∀ value,
    ExecutionCost.ofWork (Q.cost R.initCode value) + potential (R.machine.init value) ≤
      bound value
  /-- The advertised query component dominates the initial rank. -/
  rank_init_le : ∀ value,
    toRankedRunCertificate.rank (R.machine.init value) ≤ (bound value).queries

namespace ResourcePotentialCertificate

variable {R : QuantitativeRealization Q bd}
  {allows : ∀ position, p.B position → Prop} {bound : input → ExecutionCost}

/-- A conforming trace's transition cost and final observation fit its starting potential. -/
theorem traceCost_add_terminal_le (certificate : ResourcePotentialCertificate R allows bound)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish)
    (htrace : trace.Conforms allows) :
    trace.cost + terminalCost R finish ≤ certificate.potential start := by
  induction trace with
  | nil state =>
      simpa only [QuantitativeRealization.ExecutionTrace.cost, zero_add] using
        certificate.terminal_le state
  | @query state position next finish view_eq direction tail ih =>
      calc
        (QuantitativeRealization.ExecutionTrace.query (R := R) view_eq direction tail).cost +
            terminalCost R finish =
            queryStepCost R state position direction +
              (tail.cost + terminalCost R finish) := by
          simp only [QuantitativeRealization.ExecutionTrace.cost, queryStepCost, add_assoc]
        _ ≤ queryStepCost R state position direction + certificate.potential (next direction) :=
          ExecutionCost.add_le_add le_rfl (ih htrace.2)
        _ ≤ certificate.potential state := certificate.query_le view_eq direction htrace.1

/-- The decreasing natural rank gives branchwise termination from every hidden state. -/
theorem resolvesInUnder (certificate : ResourcePotentialCertificate R allows bound)
    (state : R.machine.State) :
    R.machine.ResolvesInUnder allows (certificate.toRankedRunCertificate.rank state) state :=
  certificate.toRankedRunCertificate.resolvesInUnder state

/-- A ranked local certificate supplies VCVio's complete non-vacuous pathwise run bound. -/
theorem runsWithinUnder (certificate : ResourcePotentialCertificate R allows bound) :
    R.RunsWithinUnder allows bound := by
  apply certificate.toRankedRunCertificate.runsWithinUnder bound
  · intro value finish trace htrace
    rw [executionCost_eq_init_add_trace_add_terminal R value trace]
    exact (ExecutionCost.add_le_add le_rfl
      (certificate.traceCost_add_terminal_le trace htrace)).trans (certificate.init_le value)
  · exact certificate.rank_init_le

end ResourcePotentialCertificate

end RankedRun

/-! ## Strict-PPT packaging -/

/-- A strict-PPT witness presented through ranked local resource potentials. -/
structure RankedPPTCertificate {label : Type x}
    (Q : QuantitativeStepClass.{u, v, w} C) (bd : Boundary C p input output)
    (contract : OracleContract Q bd.interface label) (program : input → FreeM p output) where
  /-- The single quantitative realization of the whole program family. -/
  realization : QuantitativeRealization Q bd
  /-- Semantic agreement with the original free interaction syntax. -/
  implements : realization.machine.Implements program
  /-- Returned payload size is polynomially recoverable from the charged tagged readout. -/
  outputRecovery : Q.PolyOutputSizeRecovery bd
  /-- One second-order polynomial shared by every compatible resource model. -/
  polynomial : ResourcePolynomial (OracleModulus label)
  /-- Model-relative local ranked evidence for that same polynomial. -/
  resourcePotential : ∀ model : contract.Model,
    RankedRun.ResourcePotentialCertificate realization model.resourceModel.allows fun value ↦
      polynomial.eval model.modulus (Q.size bd.input value)

namespace RankedPPTCertificate

variable {label : Type x} {contract : OracleContract Q bd.interface label}
  {program : input → FreeM p output}

/-- Forget ranked local evidence to VCVio's standard strict-PPT witness. -/
def strictPPTWitness (certificate : RankedPPTCertificate Q bd contract program) :
    StrictPPTWitness Q bd contract program where
  realization := certificate.realization
  implements := certificate.implements
  outputRecovery := certificate.outputRecovery
  polynomial := certificate.polynomial
  runsWithin model := (certificate.resourcePotential model).runsWithinUnder

/-- Ranked local evidence establishes backend-relative strict oracle PPT. -/
theorem isOraclePPTBy (certificate : RankedPPTCertificate Q bd contract program) :
    IsOraclePPTBy Q bd contract program :=
  ⟨certificate.strictPPTWitness⟩

end RankedPPTCertificate

end OracleComp.Complexity
