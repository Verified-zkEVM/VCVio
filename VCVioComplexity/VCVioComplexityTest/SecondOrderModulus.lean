/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioComplexity.Backend.OracleCanary

/-!
# Second-order modulus acceptance canary

The existing one-coin machine has a fixed two-bit tagged response encoding, so it does not need a
variable response-size modulus for a tight bound. This canary instead admits two distinct honest
slack envelopes for that same response and checks one conservative second-order polynomial against
both. The concrete realization and every machine certificate are reused unchanged.
-/

@[expose] public section

namespace VCVioComplexityTest.SecondOrderModulus

open PFunctor
open OracleComp.Complexity
open VCVioComplexity.Backend.TuringMachine

local instance : stepClass.HasProd := hasProd
local instance : stepClass.HasSum := hasSum
local instance : stepClass.HasOption := hasOption

/-- The tight admissible response envelope for the one-coin interface. -/
def tightResponseModel : OracleResourceModel quantitativeStepClass coinBoundary.interface
    (fun _ ↦ PUnit.unit) where
  allows := fun _ _ ↦ True
  responseSize := fun _ _ ↦ 2
  responseSize_monotone := fun _ _ _ _ ↦ le_rfl
  responseSize_le position answer _ := by
    cases position
    cases answer <;> exact le_rfl

/-- A distinct admissible response envelope with one bit of explicit slack. -/
def slackResponseModel : OracleResourceModel quantitativeStepClass coinBoundary.interface
    (fun _ ↦ PUnit.unit) where
  allows := fun _ _ ↦ True
  responseSize := fun _ _ ↦ 3
  responseSize_monotone := fun _ _ _ _ ↦ le_rfl
  responseSize_le position answer _ := by
    cases position
    cases answer <;> decide

/-- The tight and slack envelopes are extensionally different resource models. -/
theorem tightResponseModel_ne_slackResponseModel : tightResponseModel ≠ slackResponseModel := by
  intro models_eq
  have sizes_eq := congrArg (fun model ↦ model.responseSize PUnit.unit 0) models_eq
  change 2 = 3 at sizes_eq
  omega

/-- A contract admitting exactly the two concrete response-size models above. -/
def twoResponseModelContract :
    OracleContract quantitativeStepClass coinBoundary.interface Unit where
  labelOf _ := PUnit.unit
  admissible model := model = tightResponseModel ∨ model = slackResponseModel
  model_nonempty := ⟨tightResponseModel, Or.inl rfl⟩

/-- The tight response model packaged with its contract evidence. -/
def tightContractModel : twoResponseModelContract.Model :=
  ⟨tightResponseModel, Or.inl rfl⟩

/-- The slack response model packaged with its contract evidence. -/
def slackContractModel : twoResponseModelContract.Model :=
  ⟨slackResponseModel, Or.inr rfl⟩

/-- A conservative resource bound which explicitly reads the response-size modulus.

The modulus term is added to every component. It is intentionally loose: this test checks that one
uniform witness is accepted under multiple environments, not that the fixed-answer machine needs
second-order growth. -/
def responseSensitivePolynomial : ResourcePolynomial (OracleModulus Unit) :=
  let response : _root_.Complexity.SecondOrderPolynomial (OracleModulus Unit) :=
    .oracle (.responseSize PUnit.unit) .input
  { work := .add (.const oneCoinCost.work) response
    queries := .add (.const oneCoinCost.queries) response
    traffic := .add (.const oneCoinCost.traffic) response
    peakStateSize := .add (.const oneCoinCost.peakStateSize) response
    peakHeadSize := .add (.const oneCoinCost.peakHeadSize) response }

/-- The second-order work bound observes the tight response modulus. -/
example :
    (responseSensitivePolynomial.eval tightContractModel.modulus 0).work = 12 :=
  rfl

/-- The same syntax evaluates differently under the admissible slack modulus. -/
example :
    (responseSensitivePolynomial.eval slackContractModel.modulus 0).work = 13 :=
  rfl

private theorem oneCoin_runsWithin_tight :
    oneCoinRealization.RunsWithinUnder tightResponseModel.allows (fun _ ↦ oneCoinCost) := by
  simpa [tightResponseModel, fairCoinResourceModel] using oneCoinRealization_runsWithin.{0}

private theorem oneCoin_runsWithin_slack :
    oneCoinRealization.RunsWithinUnder slackResponseModel.allows (fun _ ↦ oneCoinCost) := by
  simpa [slackResponseModel, fairCoinResourceModel] using oneCoinRealization_runsWithin.{0}

/-- The unchanged one-coin realization is bounded uniformly over both admissible moduli. -/
def oneCoinTwoModelWitness : StrictPPTWitness quantitativeStepClass coinBoundary
    twoResponseModelContract oneCoinProgram where
  realization := oneCoinRealization
  implements := oneCoinMachine_implements
  outputRecovery := coinOutputRecovery
  polynomial := responseSensitivePolynomial
  runsWithin model := by
    change oneCoinRealization.RunsWithinUnder model.1.allows fun value ↦
      responseSensitivePolynomial.eval model.1.modulus
        (quantitativeStepClass.size coinBoundary.input value)
    rcases model.2 with tight_eq | slack_eq
    · rw [tight_eq]
      exact oneCoin_runsWithin_tight.mono fun input ↦ by
        cases input
        rw [ExecutionCost.le_iff]
        change 10 ≤ 12 ∧ 1 ≤ 3 ∧ 2 ≤ 4 ∧ 2 ≤ 4 ∧ 2 ≤ 4
        decide
    · rw [slack_eq]
      exact oneCoin_runsWithin_slack.mono fun input ↦ by
        cases input
        rw [ExecutionCost.le_iff]
        change 10 ≤ 13 ∧ 1 ≤ 4 ∧ 2 ≤ 5 ∧ 2 ≤ 5 ∧ 2 ≤ 5
        decide

/-- Backend-relative strict PPT under a contract with two response-size environments. -/
theorem oneCoin_isOraclePPTBy_twoResponseModels :
    IsOraclePPTBy quantitativeStepClass coinBoundary twoResponseModelContract oneCoinProgram :=
  ⟨oneCoinTwoModelWitness⟩

end VCVioComplexityTest.SecondOrderModulus
