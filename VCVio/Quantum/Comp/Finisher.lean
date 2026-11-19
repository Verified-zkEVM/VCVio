/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.TotalQueryBound
public import VCVio.Quantum.Foundations.PrivateUnit

/-!
# Oracle-free finishing operations

An oracle-free continuation leaves every prefix query weight unchanged. A fixed instrument on
program memory and a trivial private register can also be packaged as such a local continuation,
without discarding any nontrivial runtime memory.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Quantum.QuantumRuntime

universe u v u₁ v₁ w w₁

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)
  {L : LocalSig.{u, v}} (I : L.Interp) {X : QReg → Type w} {Y : QReg → Type w₁}
  {A : QReg}

/-! ## Query weights and observations of continuations -/

/-- An oracle-free suffix does not affect the input weight of any earlier oracle call.
The suffix may depend on external data; the equality holds for arbitrary input matrices. -/
theorem queryWeight_bind_of_isTotalQueryBound_zero
    (weight : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (finish : ∀ B, X B → QuantumComp L spec Y B)
    (hf : ∀ B b, (finish B b).IsTotalQueryBound 0)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I weight (x.bind finish) ρ j = R.queryWeight I weight x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure B b =>
    rw [QuantumComp.pure_bind, queryWeight_pure]
    exact R.queryWeight_eq_zero_of_isTotalQueryBound I (hf B b) (Nat.zero_le _) ρ
  | primBind B o next ih =>
    rw [QuantumComp.primBind_bind, queryWeight_primBind, queryWeight_primBind]
    exact tsum_congr fun b ↦ ih b _ j
  | queryBind B i E e next ih =>
    rw [QuantumComp.queryBind_bind]
    cases j with
    | zero => rw [queryWeight_queryBind_zero, queryWeight_queryBind_zero]
    | succ j =>
      rw [queryWeight_queryBind_succ, queryWeight_queryBind_succ]
      exact tsum_congr fun r ↦ ih r _ j

/-- An oracle-free suffix also preserves the sum of all query weights. -/
theorem totalWeight_bind_of_isTotalQueryBound_zero
    (weight : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (finish : ∀ B, X B → QuantumComp L spec Y B)
    (hf : ∀ B b, (finish B b).IsTotalQueryBound 0)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I weight (x.bind finish) ρ = R.totalWeight I weight x ρ := by
  simp only [totalWeight, queryWeight_bind_of_isTotalQueryBound_zero R I weight x finish hf]

variable {β : Type*} [MeasurableSpace β]

/-- A measurable observation of the leaf is the pushforward of the run's outcome law. -/
theorem evalDistMap_eq_map_evalDist [MeasurableSpace (Σ B, X B)]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ B, X B) → β)
    (hf : Measurable f) :
    R.evalDistMap I x ρ f = (R.evalDist I x ρ).map f := by
  rw [evalDist, DSubInstrument.outcomeMeasure, Measure.map_sum hf.aemeasurable]
  refine congrArg Measure.sum (funext fun leaf ↦ ?_)
  rw [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]
  rfl

/-- Observe a continuation from each actual joint post-state of its prefix. No oracle-private
state is initialized again between the two computations. -/
theorem evalDistMap_bind (x : QuantumComp L spec X A)
    (k : ∀ B, X B → QuantumComp L spec Y B) (ρ : SubState A) (f : (Σ B, Y B) → β) :
    R.evalDistMap I (x.bind k) ρ f =
      letI : MeasurableSpace (Σ B, Y B) := ⊤
      Measure.sum fun pre : Σ B, X B ↦
        ((R.run I (k pre.1 pre.2)).outcomeMeasure (R.jointPost I x ρ pre)).map f := by
  let : MeasurableSpace (Σ B, X B) := ⊤
  let : MeasurableSpace (Σ B, Y B) := ⊤
  rw [evalDistMap_eq_map_evalDist R I _ _ _ Measurable.of_discrete,
    evalDist, run_bind, DSubInstrument.outcomeMeasure_bind,
    Measure.map_sum Measurable.of_discrete.aemeasurable]
  rfl

/-- Boolean and propositional observations of the same predicate give the same event weight. -/
theorem evalDistMap_decide_apply_true (x : QuantumComp L spec X A) (ρ : SubState A)
    (p : (Σ B, X B) → Prop) [DecidablePred p] :
    R.evalDistMap I x ρ (fun leaf ↦ decide (p leaf)) {true} =
      R.evalDistMap I x ρ p {True} := by
  rw [R.evalDistMap_apply I x ρ _ (MeasurableSet.singleton true),
    R.evalDistMap_apply I x ρ _ (MeasurableSet.singleton True)]
  apply tsum_congr
  intro leaf
  by_cases h : p leaf <;> simp [h]

end Quantum.QuantumRuntime

namespace Quantum.QuantumComp

universe u v w

variable {spec : QuantumOracleSpec.{u, v}} {W : QReg → Type w} {A : QReg}

/-! ## Local finishing instruments -/

/-- Package an instrument with trivial private memory as one oracle-free local operation. -/
@[expose]
noncomputable def localFinisher
    (p : DSubInstrument (A × Unit) (Σ B, W B) (fun leaf ↦ leaf.1 × Unit)) :
    QuantumComp LocalSig.instruments spec W A :=
  QuantumComp.primBind ⟨Σ B, W B, Sigma.fst, p.dropUnit⟩ fun leaf ↦
    QuantumComp.pure leaf.2

/-- A localized instrument makes no oracle calls. -/
@[simp]
theorem isTotalQueryBound_localFinisher
    (p : DSubInstrument (A × Unit) (Σ B, W B) (fun leaf ↦ leaf.1 × Unit)) (n : ℕ) :
    (localFinisher (spec := spec) p).IsTotalQueryBound n := by
  simp [localFinisher, LocalSig.InstrumentOp.Outcome]

variable {Out : Type}

/-- Run a unit-private-memory instrument locally, discard its final program register and
retain its classical output. Its primitive outcome type is `Out`, independently of the
input instrument's register-dependent leaf universe. -/
@[expose]
noncomputable def localObservation
    (p : DSubInstrument (A × Unit) (Σ _B : QReg, Out) (fun leaf ↦ leaf.1 × Unit)) :
    QuantumComp LocalSig.instruments spec (fun _ ↦ Out) A :=
  QuantumComp.primBind
    ⟨Out, fun _ ↦ QReg.of Unit, p.dropUnit.observe (fun leaf ↦ leaf.2)⟩ fun out ↦
      QuantumComp.pure out

/-- Physically observing an instrument introduces no oracle calls. -/
@[simp]
theorem isTotalQueryBound_localObservation
    (p : DSubInstrument (A × Unit) (Σ _B : QReg, Out) (fun leaf ↦ leaf.1 × Unit)) (n : ℕ) :
    (localObservation (spec := spec) p).IsTotalQueryBound n := by
  simp [localObservation, LocalSig.InstrumentOp.Outcome]

end Quantum.QuantumComp

namespace Quantum.QuantumRuntime

universe u v w

variable {spec : QuantumOracleSpec.{u, v}} {W : QReg → Type w} {A : QReg}

/-! ## Execution of local finishers -/

/-- Running a local finisher frames its program-memory operation by the actual private register.
For a unit private register, `DSubInstrument.frame_dropUnit` recovers the given instrument. -/
theorem run_localFinisher (R : QuantumRuntime spec)
    (p : DSubInstrument (A × Unit) (Σ B, W B) (fun leaf ↦ leaf.1 × Unit)) :
    R.run .instruments (QuantumComp.localFinisher (spec := spec) p) =
      p.dropUnit.frame R.D := by
  simp only [QuantumComp.localFinisher, run_primBind, LocalSig.Interp.instruments_apply,
    run_pure]
  exact DSubInstrument.bind_ret _

variable {Out : Type}

/-- A local observation returns the observed value on the trivial final register, with the
runtime's own private register framed around the local operation. -/
theorem run_localObservation (R : QuantumRuntime spec)
    (p : DSubInstrument (A × Unit) (Σ _B : QReg, Out) (fun leaf ↦ leaf.1 × Unit)) :
    R.run .instruments (QuantumComp.localObservation (spec := spec) p) =
      DSubInstrument.map
        (C := fun leaf : Σ _B : QReg, Out ↦ leaf.1 × R.D)
        (fun out ↦ ⟨QReg.of Unit, out⟩)
        ((p.dropUnit.observe (fun leaf ↦ leaf.2)).frame R.D) := by
  simp only [QuantumComp.localObservation, run_primBind, LocalSig.Interp.instruments_apply,
    run_pure]
  exact (DSubInstrument.map_eq_bind_ret _ _).symm

/-- Observing the classical result of a local observation gives its primitive observation law.
The final register is trivial and is forgotten by the outer observation. -/
theorem map_outcomeMeasure_run_localObservation (R : QuantumRuntime spec)
    (p : DSubInstrument (A × Unit) (Σ _B : QReg, Out) (fun leaf ↦ leaf.1 × Unit))
    (σ : SubState (A × R.D)) :
    letI : MeasurableSpace Out := ⊤
    letI : MeasurableSpace (Σ _B : QReg, Out) := ⊤
    ((R.run .instruments (QuantumComp.localObservation (spec := spec) p)).outcomeMeasure σ).map
        (fun leaf ↦ leaf.2) =
      ((p.dropUnit.observe (fun leaf ↦ leaf.2)).frame R.D).outcomeMeasure σ := by
  let : MeasurableSpace Out := ⊤
  let : MeasurableSpace (Σ _B : QReg, Out) := ⊤
  rw [run_localObservation,
    DSubInstrument.outcomeMeasure_map_eq_map _ Measurable.of_discrete,
    Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  exact Measure.map_id

end Quantum.QuantumRuntime
