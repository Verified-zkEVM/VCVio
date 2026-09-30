/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.Support
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.EvalDist.Defs.Measure.FinRatPMF
public import VCVio.OracleComp.EvalDist.MeasureSpec
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Executable `FinRatPMF` Semantics for `OracleComp`

The computable oracle evaluator uses `FinRatPMF.Raw`. Its output measure agrees with uniform
oracle semantics, and its positive-weight outputs are exactly the oracle program's structurally
reachable outputs.
-/

@[expose] public section

open OracleSpec OracleComp

universe u v

namespace FinRatPMF

variable {ι : Type u} {spec : OracleSpec ι}

/-- Computable query implementation using the executable `FinRatPMF.Raw` monad. -/
def finRatImpl [∀ t, Inhabited (spec.Range t)] [∀ t : spec.Domain, FinEnum (spec.Range t)] :
    QueryImpl spec Raw :=
  fun t => Raw.uniform (α := spec.Range t)

namespace finRatImpl

variable [∀ t, Inhabited (spec.Range t)] [∀ t : spec.Domain, FinEnum (spec.Range t)]

section Measure

/-- Executable query sampling has the uniform response measure. -/
@[simp]
lemma evalDist_apply (t : spec.Domain) [MeasurableSpace (spec.Range t)]
    [MeasurableSingletonClass (spec.Range t)] :
    𝒟[finRatImpl (spec := spec) t] = ProbabilityTheory.uniformOn Set.univ :=
  Raw.evalDist_uniform

variable [IsUniformMeasureSpec spec]

/-- The executable evaluator preserves the uniform oracle measure. -/
@[simp]
lemma evalDist_simulateQ {α : Type v} [MeasurableSpace α] (oa : OracleComp spec α) :
    𝒟[simulateQ (finRatImpl (spec := spec)) oa] = 𝒟[oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
      let : MeasurableSpace (spec.Range t) := ⊤
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
      simp_rw [ih]
      rw [evalDist_apply, OracleComp.evalDist_liftM_query_uniform]

end Measure

@[simp] lemma support_simulateQ {α : Type v} [DecidableEq α] (oa : OracleComp spec α) :
    (simulateQ (finRatImpl (spec := spec)) oa).support = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
      have hsupport : (finRatImpl (spec := spec) t).support = Finset.univ :=
        Raw.support_uniform
      simp [Raw.support_bind, hsupport, ih]

lemma finSupport_simulateQ {α : Type v} [DecidableEq α]
    (oa : OracleComp spec α) :
    (simulateQ (finRatImpl (spec := spec)) oa).support = finSupport oa := by
  apply Finset.coe_injective
  rw [coe_finSupport, support_simulateQ]

end finRatImpl

namespace finRatImpl

/-- Final event checks have the same probability under executable and oracle evaluation. -/
lemma prEvent_simulateQ {ι : Type u} {spec : OracleSpec.{u, 0} ι}
    [IsUniformMeasureSpec spec] [∀ t, Inhabited (spec.Range t)]
    [∀ t : spec.Domain, FinEnum (spec.Range t)]
    {α : Type} (oa : OracleComp spec α) (p : α → Prop) :
    Pr{let x ← simulateQ (finRatImpl (spec := spec)) oa}[p x] = Pr{let x ← oa}[p x] := by
  rw [prEvent_eq_evalDist_map, prEvent_eq_evalDist_map, ← simulateQ_map]
  exact congrArg (fun μ : MeasureTheory.Measure Prop => μ {True})
    (evalDist_simulateQ (spec := spec) (p <$> oa))

end finRatImpl

namespace Demo

local instance : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b => if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
      invFun := fun i => i.1 = 1
      left_inv := by
        intro b
        cases b <;> rfl
      right_inv := by
        intro i
        fin_cases i <;> rfl }
  decEq := inferInstance

instance : (t : coinSpec.Domain) → FinEnum (coinSpec.Range t) := by
  intro t
  change FinEnum Bool
  infer_instance

def xorTwoCoins : FinRatPMF.Raw Bool := do
  let b1 ← FinRatPMF.Raw.coin
  let b2 ← FinRatPMF.Raw.coin
  pure (b1 != b2)

def threeCoinCount : FinRatPMF.Raw Nat := do
  let b1 ← FinRatPMF.Raw.coin
  let b2 ← FinRatPMF.Raw.coin
  let b3 ← FinRatPMF.Raw.coin
  pure (cond b1 1 0 + cond b2 1 0 + cond b3 1 0)

def twoCoinQueries : OracleComp coinSpec Nat := do
  let b1 ← OracleComp.coin
  let b2 ← OracleComp.coin
  pure (cond b1 1 0 + cond b2 1 0)

/-
#eval FinRatPMF.Raw.coin
#eval xorTwoCoins
#eval xorTwoCoins.normalize
#eval threeCoinCount.normalize
#eval! simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries
#eval! (simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries).normalize
#eval! (simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries).normalize.prob 1)
-/

end Demo
end FinRatPMF
