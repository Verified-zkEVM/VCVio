/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.NumberedHybrid

/-!
# Numbered-call schedule regressions

Call tags count oracle calls rather than local operations. A current answer can change a
complete run while leaving its own pre-query weight unchanged; earlier loss affects later
weights. Runtime-private memory remains part of the complete run.
-/

public section

open Quantum Matrix
open scoped ENNReal Kronecker

namespace VCVioTest.QuantumNumberedQueries

/-- A trivial quantum port with one classical answer. -/
@[expose, reducible]
def spec : QuantumOracleSpec where
  Port := Unit
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result _ := Unit

/-- Two oracle calls separated by a local identity operation. -/
noncomputable def twoCalls :
    QuantumComp LocalSig.instruments spec (fun _ ↦ Unit) (QReg.of Unit) :=
  QuantumComp.queryBind () (QReg.of Unit) (Equiv.prodPUnit Unit).symm fun _ ↦
    QuantumComp.primBind
      ⟨Unit, fun _ ↦ QReg.of (Unit × Unit), SubInstrument.pure ()⟩ fun _ ↦
      QuantumComp.queryBind () (QReg.of Unit) (Equiv.refl _) fun _ ↦ QuantumComp.pure ()

/-- The numbered call positions are seven and eight; the local identity spends no tag. -/
example : twoCalls.numberQueries 7 =
    (QuantumComp.queryBind (7, ()) (QReg.of Unit) (Equiv.prodPUnit Unit).symm fun _ ↦
      QuantumComp.primBind
        ⟨Unit, fun _ ↦ QReg.of (Unit × Unit), SubInstrument.pure ()⟩ fun _ ↦
        QuantumComp.queryBind (8, ()) (QReg.of Unit) (Equiv.refl _)
          fun _ ↦ QuantumComp.pure () :
        QuantumComp LocalSig.instruments spec.numbered (fun _ ↦ Unit) (QReg.of Unit)) := by
  simp [twoCalls, QuantumComp.numberQueries_queryBind, QuantumComp.numberQueries_primBind]

/-- Non-unit port charges, including the exact threshold, survive numbering. -/
example (t n : ℕ) :
    (twoCalls.numberQueries t).IsQueryChargeBound (fun _ ↦ 3) n ↔ 6 ≤ n := by
  rw [QuantumComp.isQueryChargeBound_numberQueries_iff twoCalls t (fun _ ↦ 3) n]
  simp [twoCalls, LocalSig.InstrumentOp.Outcome]
  omega

/-- The original runtime retains a nontrivial private bit even for trivial caller registers. -/
@[expose, reducible]
noncomputable def runtime : QuantumRuntime spec where
  D := QReg.of Bool
  init := SubState.basis false
  step _ := SubInstrument.pure ()

/-- A schedule loses all mass precisely when answering the selected call tag. -/
@[expose, reducible]
noncomputable def stopAt (n : ℕ) (t : ℕ) (_ : spec.Port) :
    SubInstrument (Unit × runtime.D) (Unit × runtime.D) Unit :=
  if t = n then DSubInstrument.fail else SubInstrument.pure ()

/-- A current answer does not enter its own pre-query weight, even with a shifted counter. -/
example (ρ : Matrix ((QReg.of Unit) × runtime.D) ((QReg.of Unit) × runtime.D) ℂ) :
    (runtime.numbered (stopAt 8)).queryWeight .instruments
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (twoCalls.numberQueries 7) ρ 1 =
    (runtime.numbered (fun _ ↦ runtime.step)).queryWeight .instruments
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (twoCalls.numberQueries 7) ρ 1 := by
  apply QuantumRuntime.queryWeight_numberQueries_eq_of_prefix
  intro m hlo hhi
  have hm : m = 7 := by omega
  subst m
  rfl

/-- A weight supported only at tag seven vanishes at the second actual call. -/
example (ρ : Matrix ((QReg.of Unit) × runtime.D) ((QReg.of Unit) × runtime.D) ℂ) :
    (runtime.numbered (stopAt 8)).queryWeight .instruments
      (fun p σ ↦ if p.1 = 7 then ENNReal.ofReal σ.trace.re else 0)
      (twoCalls.numberQueries 7) ρ 1 = 0 := by
  apply QuantumRuntime.queryWeight_numberQueries_eq_zero
  intro p σ hp
  have hp' : p.1 ≠ 7 := by omega
  simp [hp']

/-- Constant scheduling preserves the full instrument, including the runtime's private bit. -/
example :
    (runtime.numbered (fun _ ↦ runtime.step)).run .instruments (twoCalls.numberQueries 7) =
      runtime.run .instruments twoCalls :=
  runtime.run_numberQueries_const .instruments twoCalls 7

/-- Changes after the bounded call interval preserve the whole run, including private memory. -/
example :
    (runtime.numbered (stopAt 9)).run .instruments (twoCalls.numberQueries 7) =
      (runtime.numbered (fun _ ↦ runtime.step)).run .instruments (twoCalls.numberQueries 7) := by
  apply runtime.run_numberQueries_eq_of_prefix .instruments (stopAt 9)
    (fun _ ↦ runtime.step) (n := 2)
  · simp [twoCalls, LocalSig.InstrumentOp.Outcome]
  · intro m hlo hhi
    have hm : m ≠ 9 := by omega
    funext i
    simp [stopAt, hm]

/-- Answering normally preserves the trace of the caller and private register jointly. -/
private theorem trace_queryStep_stopAt {A : QReg} (n t : ℕ) (ht : t ≠ n)
    (e : A ≃ Unit × Unit)
    (ρ : Matrix (A × runtime.D) (A × runtime.D) ℂ) :
    (((runtime.numbered (stopAt n)).queryStep (t, ()) (QReg.of Unit) e).branch () ρ).trace =
      ρ.trace := by
  rw [QuantumRuntime.queryStep_branch_apply, SubInstrument.trace_relabel_branch_apply]
  simp only [QuantumRuntime.numbered, stopAt, ht, ↓reduceIte,
    SubInstrument.frame_pure, SubInstrument.branch_pure_self, LinearMap.id_apply]
  exact SubInstrument.trace_relabel_branch_apply _ _

/-- Failing at the first call leaves no input mass for the second call. -/
example (ρ : Matrix ((QReg.of Unit) × runtime.D) ((QReg.of Unit) × runtime.D) ℂ) :
    (runtime.numbered (stopAt 7)).queryWeight .instruments
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (twoCalls.numberQueries 7) ρ 1 = 0 := by
  rw [twoCalls, QuantumComp.numberQueries_queryBind,
    QuantumRuntime.queryWeight_queryBind_succ]
  simp only [tsum_fintype, Fintype.sum_unique]
  have hz : ((runtime.numbered (stopAt 7)).queryStep (7, ()) (QReg.of Unit)
      (Equiv.prodPUnit Unit).symm).branch () ρ = 0 := by
    rw [QuantumRuntime.queryStep_branch_apply]
    simp [QuantumRuntime.numbered, stopAt, DSubInstrument.branch_fail]
  rw [hz]
  apply QuantumRuntime.queryWeight_zero
  intro i
  simp

/-- Failing when answering the second call does not remove its pre-answer input mass. -/
example (ρ : Matrix ((QReg.of Unit) × runtime.D) ((QReg.of Unit) × runtime.D) ℂ) :
    (runtime.numbered (stopAt 8)).queryWeight .instruments
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (twoCalls.numberQueries 7) ρ 1 =
        ENNReal.ofReal ρ.trace.re := by
  rw [twoCalls, QuantumComp.numberQueries_queryBind,
    QuantumRuntime.queryWeight_queryBind_succ]
  simp only [tsum_fintype, Fintype.sum_unique, QuantumComp.numberQueries_primBind,
    QuantumRuntime.queryWeight_primBind, QuantumComp.numberQueries_queryBind]
  simp only [LocalSig.Interp.instruments_apply, SubInstrument.frame_pure,
    SubInstrument.branch_pure_self, LinearMap.id_apply,
    QuantumRuntime.queryWeight_queryBind_zero, QuantumRuntime.trace_callInput]
  rw [trace_queryStep_stopAt 8 7 (by decide)]

/-- A program written directly on numbered ports can choose tag nine for its first call. -/
noncomputable def manuallyTagged :
    QuantumComp LocalSig.instruments spec.numbered (fun _ ↦ Unit) (QReg.of Unit) :=
  QuantumComp.queryBind (9, ()) (QReg.of Unit) (Equiv.prodPUnit Unit).symm
    fun _ ↦ QuantumComp.pure ()

/-- Actual-position tag invariants require the translation; arbitrary tagged programs need not
use tag zero at their first call. -/
example (ρ : Matrix ((QReg.of Unit) × runtime.D) ((QReg.of Unit) × runtime.D) ℂ) :
    (runtime.numbered (stopAt 8)).queryWeight .instruments
      (fun p σ ↦ if p.1 = 9 then ENNReal.ofReal σ.trace.re else 0) manuallyTagged ρ 0 =
        ENNReal.ofReal ρ.trace.re := by
  simp [manuallyTagged, QuantumRuntime.trace_callInput]

/-- The full run, unlike the pre-query weight, includes both answering maps. -/
private theorem run_twoCalls_branch (n : ℕ)
    (ρ : Matrix ((QReg.of Unit) × runtime.D) ((QReg.of Unit) × runtime.D) ℂ) :
    ((runtime.numbered (stopAt n)).run .instruments (twoCalls.numberQueries 7)).branch
      ⟨QReg.of (Unit × Unit), ()⟩ ρ =
    ((runtime.numbered (stopAt n)).queryStep (A := QReg.of (Unit × Unit))
      (8, ()) (QReg.of Unit) (Equiv.refl _)).branch ()
      (((runtime.numbered (stopAt n)).queryStep (7, ()) (QReg.of Unit)
        (Equiv.prodPUnit Unit).symm).branch () ρ) := by
  rw [twoCalls, QuantumComp.numberQueries_queryBind, QuantumRuntime.run_queryBind,
    DSubInstrument.branch_bind_unit]
  simp only [QuantumComp.numberQueries_primBind, QuantumRuntime.run_primBind,
    QuantumComp.numberQueries_queryBind, QuantumComp.numberQueries_pure,
    QuantumRuntime.run_queryBind, QuantumRuntime.run_pure,
    LocalSig.Interp.instruments_apply, SubInstrument.frame_pure, DSubInstrument.ret_bind,
    DSubInstrument.branch_bind_unit, DSubInstrument.branch_ret_self, LinearMap.id_comp,
    LinearMap.comp_apply]

/-- Failing at the second answer destroys all final mass while its pre-query weight survives. -/
example (ρ : Matrix ((QReg.of Unit) × runtime.D) ((QReg.of Unit) × runtime.D) ℂ) :
    ((runtime.numbered (stopAt 8)).run .instruments (twoCalls.numberQueries 7)).branch
      ⟨QReg.of (Unit × Unit), ()⟩ ρ = 0 := by
  rw [run_twoCalls_branch, QuantumRuntime.queryStep_branch_apply]
  simp [QuantumRuntime.numbered, stopAt, DSubInstrument.branch_fail]

/-- A schedule failing only at the unused tag nine retains the complete initial trace. -/
example (ρ : Matrix ((QReg.of Unit) × runtime.D) ((QReg.of Unit) × runtime.D) ℂ) :
    (((runtime.numbered (stopAt 9)).run .instruments (twoCalls.numberQueries 7)).branch
      ⟨QReg.of (Unit × Unit), ()⟩ ρ).trace = ρ.trace := by
  rw [run_twoCalls_branch, trace_queryStep_stopAt 9 8 (by decide),
    trace_queryStep_stopAt 9 7 (by decide)]

end VCVioTest.QuantumNumberedQueries
