/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.ClassicalCalls
public import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable

/-!
# Classical randomized algorithms in the sequential QROM

Private uniform samples become local coins on the trivial register, and each function query
becomes one ordinary quantum basis call. A single sampled function answers every adaptive query.
The resulting output law is the classical lazy random-oracle law, including its private coins.
Only function queries count against the quantum query budget. Source and result types lie in
`Type`, following the classical simulation API.
-/

public section

open MeasureTheory OracleSpec OracleComp
open scoped ENNReal Kronecker

namespace Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- Uniform private coins together with ordinary quantum basis calls to the function oracle. -/
@[expose]
noncomputable def classicalRandomizedImpl :
    QueryImpl (unifSpec + (X →ₒ Y))
      (QComp (qromSpec X Y) (QReg.of Unit) (QReg.of Unit)) :=
  fun t ↦ match t with
    | .inl n => QComp.coinImpl (qromSpec X Y) (QReg.of Unit) n
    | .inr t => classicalQuery (Y := Y) t

end Quantum

namespace OracleComp

open Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- Run a classical randomized algorithm using local private coins and one ordinary quantum
basis call per function query, on the trivial register. -/
@[expose]
noncomputable def toQuantumRandomized (oa : OracleComp (unifSpec + (X →ₒ Y)) α) :
    QComp (qromSpec X Y) (QReg.of Unit) (QReg.of Unit) α :=
  oa.toQuantumAt classicalRandomizedImpl

@[simp]
theorem toQuantumRandomized_pure (a : α) :
    (pure a : OracleComp (unifSpec + (X →ₒ Y)) α).toQuantumRandomized =
      QuantumComp₂.pure a := rfl

@[simp]
theorem toQuantumRandomized_query_bind (t : ℕ ⊕ X)
    (k : (unifSpec + (X →ₒ Y)).Range t → OracleComp (unifSpec + (X →ₒ Y)) α) :
    (liftM ((unifSpec + (X →ₒ Y)).query t) >>= k).toQuantumRandomized =
      (classicalRandomizedImpl t).bind fun y ↦ (k y).toQuantumRandomized :=
  toQuantumAt_query_bind classicalRandomizedImpl t k

/-- Classical randomized algorithms give lossless quantum programs. -/
theorem lossless_toQuantumRandomized (oa : OracleComp (unifSpec + (X →ₒ Y)) α) :
    oa.toQuantumRandomized.Lossless .instruments := by
  apply lossless_toQuantumAt
  intro t
  rcases t with n | t
  · exact QComp.lossless_coinImpl (spec := qromSpec X Y) (B := QReg.of Unit) n
  · exact lossless_classicalQuery (Y := Y) t

/-- A bound counting only classical function queries transfers without charging private coins. -/
theorem IsQueryBoundP.isQueryBound_toQuantumRandomized
    {oa : OracleComp (unifSpec + (X →ₒ Y)) α} {n : ℕ}
    (h : IsQueryBoundP oa (fun t ↦ t.isRight = true) n) :
    oa.toQuantumRandomized.IsQueryBound (fun _ ↦ n) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact QuantumComp₂.isQueryBound_pure a _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [toQuantumRandomized_query_bind]
    rcases t with m | t
    · change ((QComp.coinImpl _ _ m).bind _).IsQueryBound _
      rw [QComp.coinImpl, QComp.isQueryBound_act_bind_iff]
      exact fun y ↦ ih y (h.2 y)
    · change ((classicalQuery (Y := Y) t).bind _).IsQueryBound _
      have hn : 0 < n := h.1.resolve_left (by simp)
      refine (QuantumComp₂.isQueryBound_bind (isQueryBound_classicalQuery (Y := Y) t)
        (fun y ↦ ih y (h.2 y))).mono fun _ ↦ ?_
      simp only [Pi.add_apply, Sum.isRight_inr, ↓reduceIte]
      omega

end OracleComp

namespace Quantum

variable {X Y α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y]

/-- The complete fixed-function run is the local-coin embedding of the classical fixed-table
execution. All adaptive classical continuations remain intact. -/
theorem run_toQuantumRandomized (H : X → Y)
    (oa : OracleComp (unifSpec + (X →ₒ Y)) α) :
    (additiveOracleRuntime H).run₂ .instruments oa.toQuantumRandomized =
      (additiveOracleRuntime H).run₂ .instruments
        ((simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) oa).toQuantumAt
          (QComp.coinImpl (qromSpec X Y) (QReg.of Unit))) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [toQuantumRandomized_query_bind, simulateQ_bind, simulateQ_spec_query]
    rcases t with n | t
    · change (additiveOracleRuntime H).run₂ .instruments
        ((QComp.coinImpl (qromSpec X Y) (QReg.of Unit) n).bind
          fun y ↦ (k y).toQuantumRandomized) =
        (additiveOracleRuntime H).run₂ .instruments
          ((liftM (unifSpec.query n) >>= fun y ↦
            simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) (k y)).toQuantumAt
            (QComp.coinImpl (qromSpec X Y) (QReg.of Unit)))
      rw [toQuantumAt_query_bind, QuantumRuntime.run₂_bind, QuantumRuntime.run₂_bind]
      congr 1
      funext y
      exact ih y
    · change (additiveOracleRuntime H).run₂ .instruments
        ((classicalQuery t).bind fun y ↦ (k y).toQuantumRandomized) =
        (additiveOracleRuntime H).run₂ .instruments
          ((pure (H t) >>= fun y ↦
            simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) (k y)).toQuantumAt
            (QComp.coinImpl (qromSpec X Y) (QReg.of Unit)))
      rw [pure_bind, QuantumRuntime.run₂_bind, run_classicalQuery, SubInstrument.pure_bind]
      exact ih _

/-- At a fixed function, the quantum embedding has the classical fixed-table output measure. -/
theorem evalDist_additiveOracleRuntime_toQuantumRandomized [MeasurableSpace α] (H : X → Y)
    (oa : OracleComp (unifSpec + (X →ₒ Y)) α) :
    (additiveOracleRuntime H).evalDist₂ .instruments oa.toQuantumRandomized (SubState.basis ()) =
      𝒟[simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) oa] := by
  rw [QuantumRuntime.evalDist₂, run_toQuantumRandomized,
    outcomeMeasure_run₂_toQuantumAt_coinImpl]
  have htrace : ((SubState.basis ()).prod (additiveOracleRuntime H).init).matrix.trace.re = 1 := by
    rw [SubState.trace_re_prod, SubState.trace_basis]
    change (1 : ℂ).re * (SubState.basis ()).matrix.trace.re = 1
    rw [SubState.trace_basis]
    norm_num
  rw [htrace, ENNReal.ofReal_one, one_smul]

section Sampled

variable [SampleableType (X → Y)]

/-- The sequential QROM embedding samples one function for the whole classical randomized
execution, keeping private uniform samples local. -/
theorem qromEvalDist₂_toQuantumRandomized [MeasurableSpace α]
    (oa : OracleComp (unifSpec + (X →ₒ Y)) α) :
    qromEvalDist₂ .instruments oa.toQuantumRandomized (SubState.basis ()) =
      𝒟[$ᵗ (X → Y) >>= fun H ↦ simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn H)) oa] := by
  let : MeasurableSpace (X → Y) := ⊤
  rw [qromEvalDist₂, sampledEvalDist₂_eq_bind_uniformSample, evalDist_bind_of_discrete]
  congr 1
  funext H
  exact evalDist_additiveOracleRuntime_toQuantumRandomized H oa

/-- The sequential QROM law of a classical randomized algorithm equals its lazily cached
classical random-oracle law. No resource bound is required. -/
theorem qromEvalDist₂_toQuantumRandomized_eq_randomOracle [SampleableType Y]
    [MeasurableSpace α] (oa : OracleComp (unifSpec + (X →ₒ Y)) α) :
    qromEvalDist₂ .instruments oa.toQuantumRandomized (SubState.basis ()) =
      𝒟[(simulateQ (X →ₒ Y).romImpl oa).run' ∅] := by
  rw [qromEvalDist₂_toQuantumRandomized,
    OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable]
  simp only [OracleComp.completeTable_empty]

end Sampled

end Quantum
