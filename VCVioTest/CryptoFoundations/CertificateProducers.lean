/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.CryptoFoundations.Asymptotics.OracleClosure
public import VCVio.CryptoFoundations.Asymptotics.RankedRun
public import PolyFunTest.Realizability.QuantitativeBoundedClosure

/-!
# Concrete strict-PPT certificate producers

These tests instantiate the full `BindCertificate` and `RankedPPTCertificate` records.  The
backend is PolyFun's explicitly synthetic zero-cost structural fixture, so these are API
composition tests—not cryptographic complexity claims.
-/

@[expose] public section

namespace OracleComp.Complexity.CertificateProducerTest

open PFunctor
open PFunctor.DynSystem.DynComputation
open PFunctor.QuantitativeBoundedClosureTest

/-- The unique resource model for the fixture's unanswerable interface. -/
def emptyResourceModel :
    OracleResourceModel zeroBackend unitBoundary.interface (fun _ ↦ ()) where
  allows := fun _ answer ↦ nomatch answer
  responseSize := fun _ _ ↦ 0
  responseSize_monotone := fun _ _ _ _ ↦ le_rfl
  responseSize_le := fun _ answer ↦ nomatch answer

/-- A nonempty contract pinned to the unique empty-interface resource model. -/
def emptyContract : OracleContract zeroBackend unitBoundary.interface Unit where
  labelOf _ := ()
  admissible model := model = emptyResourceModel
  model_nonempty := ⟨emptyResourceModel, rfl⟩

/-- Returned unit payloads have exactly zero encoded size in the fixture backend. -/
def returnOutputRecovery : zeroBackend.PolyOutputSizeRecovery unitBoundary where
  polynomial := .const 0
  output_le _ := le_rfl

/-- The shared all-zero resource polynomial for the returning fixture. -/
def returnPolynomial : ResourcePolynomial (OracleModulus Unit) :=
  ResourcePolynomial.const 0

/-- A complete strict-PPT witness, not merely a record-shape check. -/
def returnStrictPPTWitness : StrictPPTWitness zeroBackend unitBoundary emptyContract
    (fun input ↦ FreeM.pure input) where
  realization := returnRealization
  implements := by
    change (ofFn (p := emptyResponse) id).Implements _
    intro input
    rw [denote_ofFn]
    simp
  outputRecovery := returnOutputRecovery
  polynomial := returnPolynomial
  runsWithin model := by
    rcases model with ⟨model, hmodel⟩
    change model = emptyResourceModel at hmodel
    subst model
    change returnRealization.RunsWithinUnder emptyResourceModel.allows (fun _ ↦ 0)
    have hallows : emptyResourceModel.allows = fun _ _ ↦ True := by
      funext _ answer
      exact nomatch answer
    rw [hallows]
    let ranked : RankedRunCertificate returnRealization (fun _ _ ↦ True) := {
      rank := fun _ ↦ 0
      returns_of_rank_zero := fun state _ ↦ ⟨state, rfl⟩
      decreases := fun _ direction ↦ nomatch direction
      progress := fun hview ↦ by
        rw [show returnRealization.machine.view _ = Sum.inl PUnit.unit by rfl] at hview
        exact nomatch hview }
    apply ranked.runsWithinUnder (fun _ ↦ 0)
    · intro input finish trace _
      have hview : returnRealization.machine.view
          (returnRealization.machine.init input) = Sum.inl input := by
        rfl
      obtain ⟨_, hcost⟩ := trace.finish_eq_and_cost_eq_zero_of_view_return hview
      change ExecutionCost.ofWork 0 + trace.cost + ExecutionCost.ofWork 0 +
        ExecutionCost.observe 0 0 ≤ 0
      rw [hcost]
      rfl
    · intro input
      rfl

/-- Concrete zero-overhead sequential-composition evidence for two returning witnesses. -/
def returnBindCertificate : BindCertificate returnStrictPPTWitness returnStrictPPTWitness where
  overheadPolynomial := ResourcePolynomial.const 0
  costCertificate model := {
    overhead := fun _ ↦ 0
    cost_le := by
      intro input finish trace htrace
      have hview : (returnRealization.seqComp returnRealization).machine.view
          ((returnRealization.seqComp returnRealization).machine.init input) =
          Sum.inl input := by
        rfl
      change (returnRealization.seqComp returnRealization).ExecutionTrace
        (Sum.inl (returnRealization.machine.init input)) finish at trace
      change (returnRealization.seqComp returnRealization).executionCost input trace ≤
        (trace.seqCompSource returnRealization returnRealization).cost input + 0
      obtain ⟨_, hcost⟩ := trace.finish_eq_and_cost_eq_zero_of_view_return hview
      change ExecutionCost.ofWork 0 + trace.cost + ExecutionCost.ofWork 0 +
          ExecutionCost.observe 0 0 ≤
        (trace.seqCompSource returnRealization returnRealization).cost input + 0
      rw [hcost]
      have hzero : ExecutionCost.ofWork 0 + 0 + ExecutionCost.ofWork 0 +
          ExecutionCost.observe 0 0 = 0 := rfl
      rw [hzero, add_zero]
      exact ExecutionCost.zero_le _ }
  overhead_le _ _ := le_rfl

/-- The concrete bind certificate produces the advertised strict-PPT theorem. -/
theorem returnBind_isOraclePPTBy :
    IsOraclePPTBy zeroBackend unitBoundary emptyContract
      (fun input ↦ FreeM.bind (FreeM.pure input) (fun value ↦ FreeM.pure value)) :=
  returnBindCertificate.isOraclePPTBy

/-- Local ranked resource evidence for the same immediate-return realization. -/
def returnResourcePotential : RankedRun.ResourcePotentialCertificate returnRealization
    emptyResourceModel.allows (fun _ ↦ 0) where
  toRankedRunCertificate := {
    rank := fun _ ↦ 0
    returns_of_rank_zero := fun state _ ↦ ⟨state, rfl⟩
    decreases := fun _ direction ↦ nomatch direction
    progress := fun hview ↦ by
      rw [show returnRealization.machine.view _ = Sum.inl PUnit.unit by rfl] at hview
      exact nomatch hview }
  potential := fun _ ↦ 0
  terminal_le _ := le_rfl
  query_le := fun _ direction _ ↦ nomatch direction
  init_le _ := le_rfl
  rank_init_le _ := le_rfl

/-- A concrete producer for the full ranked strict-PPT certificate. -/
def returnRankedPPTCertificate : RankedPPTCertificate zeroBackend unitBoundary emptyContract
    (fun input ↦ FreeM.pure input) where
  realization := returnRealization
  implements := returnStrictPPTWitness.implements
  outputRecovery := returnOutputRecovery
  polynomial := returnPolynomial
  resourcePotential model := by
    rcases model with ⟨model, hmodel⟩
    change model = emptyResourceModel at hmodel
    subst model
    change RankedRun.ResourcePotentialCertificate returnRealization
      emptyResourceModel.allows (fun _ ↦ 0)
    exact returnResourcePotential

/-- Ranked local evidence reaches the public strict-PPT proposition end to end. -/
theorem returnRanked_isOraclePPTBy :
    IsOraclePPTBy zeroBackend unitBoundary emptyContract (fun input ↦ FreeM.pure input) :=
  returnRankedPPTCertificate.isOraclePPTBy

/-! ## One genuinely uniform security family -/

/-- An empty oracle interface at every security parameter. -/
def familySpec (_n : ℕ) : OracleSpec PUnit := fun _ ↦ PEmpty

/-- The input and output types really vary with the parameter. -/
abbrev familyValue (n : ℕ) := Fin (n + 1)

/-- The family returns its input.  Packing retains the parameter in the returned sigma value. -/
def familyProgram (n : ℕ) (input : familyValue n) :
    OracleComp (familySpec n) (familyValue n) :=
  pure input

/-- One boundary for the whole packed family, rather than one boundary per parameter. -/
abbrev familyBoundary : Boundary StepClass.unconstrained
    (OracleComp.SecurityFamily.Spec familySpec).toPFunctor
    (OracleComp.SecurityFamily.Input familyValue)
    (OracleComp.SecurityFamily.Output familyValue) :=
  Boundary.unconstrained _ _ _

/-- One machine implements every member of the nonconstant family. -/
def familyRealization : QuantitativeRealization zeroBackend familyBoundary where
  machine := ofFn id
  state := PUnit.unit
  initCode := PUnit.unit
  headCode := PUnit.unit
  updateCode := PUnit.unit

/-- The unique model for the packed family's unanswerable aggregate interface. -/
def familyResourceModel :
    OracleResourceModel zeroBackend familyBoundary.interface (fun _ ↦ ()) where
  allows := fun _ answer ↦ nomatch answer
  responseSize := fun _ _ ↦ 0
  responseSize_monotone := fun _ _ _ _ ↦ le_rfl
  responseSize_le := fun _ answer ↦ nomatch answer

/-- A nonempty contract shared by all parameters of the packed family. -/
def familyContract : OracleContract zeroBackend familyBoundary.interface Unit where
  labelOf _ := ()
  admissible model := model = familyResourceModel
  model_nonempty := ⟨familyResourceModel, rfl⟩

/-- One output-size recovery certificate for the dependent packed output. -/
def familyOutputRecovery : zeroBackend.PolyOutputSizeRecovery familyBoundary where
  polynomial := .const 0
  output_le _ := le_rfl

/-- A single realization and a single polynomial certify every security parameter at once. -/
def familyStrictPPTWitness : StrictPPTWitness zeroBackend familyBoundary familyContract
    (fun input ↦ ((OracleComp.SecurityFamily.packProgram familyProgram) input).toFreeM) where
  realization := familyRealization
  implements := by
    change (ofFn id).Implements (fun input ↦ FreeM.pure input)
    intro input
    rw [denote_ofFn]
    simp
  outputRecovery := familyOutputRecovery
  polynomial := ResourcePolynomial.const 0
  runsWithin model := by
    rcases model with ⟨model, hmodel⟩
    change model = familyResourceModel at hmodel
    subst model
    change familyRealization.RunsWithinUnder familyResourceModel.allows (fun _ ↦ 0)
    have hallows : familyResourceModel.allows = fun _ _ ↦ True := by
      funext _ answer
      exact nomatch answer
    rw [hallows]
    let ranked : RankedRunCertificate familyRealization (fun _ _ ↦ True) := {
      rank := fun _ ↦ 0
      returns_of_rank_zero := fun state _ ↦ ⟨state, rfl⟩
      decreases := fun _ direction ↦ nomatch direction
      progress := fun hview ↦ by
        rw [show familyRealization.machine.view _ = Sum.inl _ by rfl] at hview
        exact nomatch hview }
    apply ranked.runsWithinUnder (fun _ ↦ 0)
    · intro input finish trace _
      have hview : familyRealization.machine.view
          (familyRealization.machine.init input) = Sum.inl input := by
        rfl
      obtain ⟨_, hcost⟩ := trace.finish_eq_and_cost_eq_zero_of_view_return hview
      change ExecutionCost.ofWork 0 + trace.cost + ExecutionCost.ofWork 0 +
        ExecutionCost.observe 0 0 ≤ 0
      rw [hcost]
      rfl
    · intro input
      rfl

/-- End-to-end public theorem: this is uniform strict PPT, not pointwise witness selection. -/
theorem family_isOraclePPTBy :
    OracleComp.Complexity.SecurityFamily.IsOraclePPTBy zeroBackend familyBoundary
      familyContract familyProgram :=
  ⟨familyStrictPPTWitness⟩

end OracleComp.Complexity.CertificateProducerTest
