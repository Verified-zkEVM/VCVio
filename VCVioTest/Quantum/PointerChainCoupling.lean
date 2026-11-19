/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Scheme
public import VCVio.Quantum.Foundations.SubState
public import VCVioTest.Quantum.PointerChainProgramming
import Mathlib.Tactic.FinCases

/-!
# Retained preprocessing in the exact pointer-chain coupling

A fixed preprocessing query retains its raw answer and returns it without online calls.
For one fixed challenge, programming that cell changes recovery from zero to one. This is a
conditional fixture, not an assertion about success averaged over random challenges.
-/

public section

open Quantum PointerChainPuzzle PointerChainPuzzle.LeanSeal OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace VCVioTest.PointerChainCoupling

/-- A start address fixed before the adversary receives any puzzle. -/
@[expose, reducible]
def address : ByteArray.Bounded 83 :=
  hashInputWindow (b := 1) (n := 1) (by decide) (.start (ctx 1 1 0 0) 0 0)

/-- One raw preprocessing query, including all 32 response bytes. -/
@[expose, reducible]
def readStart : OracleComp (unifSpec + (windowSpec 83).batch) (Bytes 32) :=
  queryPoint address

/-- Retain the classical response in the preprocessing state, with no online oracle call. -/
@[expose, reducible]
noncomputable def adversary (ρ : SubState Unit) : WindowAdversary 1 1 83 where
  initialReg := QReg.of Unit
  initialState := ρ
  State := QuantumComp₂.Leaf (QReg.of Unit) (Bytes 32)
  preprocess := readStart.toQuantumBatch
  online M state _ := by
    rcases state with ⟨h, word⟩
    subst M
    exact QuantumComp.pure word

private theorem run_preprocess (ρ : SubState Unit) (H : ByteArray.Bounded 83 → Bytes 32) :
    (parallelOracleRuntime H).run .instruments (adversary ρ).preprocess =
      DSubInstrument.ret (fun leaf : Σ M, (adversary ρ).State M ↦
        leaf.1 × (parallelOracleRuntime H).D) ⟨QReg.of Unit, rfl, H address⟩ := by
  apply DSubInstrument.ext
  funext leaf
  rcases leaf with ⟨M, h, word⟩
  cases h
  change ((parallelOracleRuntime H).run₂ .instruments readStart.toQuantumBatch).branch word = _
  rw [run_toQuantumBatch]
  simp only [readStart, simulateQ_queryPoint, Id.run, OracleComp.toQuantumAt_pure,
    QuantumRuntime.run₂_pure, QueryImpl.ofFn_apply]
  by_cases h : word = H address
  · subst word
    rw [SubInstrument.branch_pure_self, DSubInstrument.branch_ret_self]
  · rw [SubInstrument.branch_pure_of_ne h]
    exact (DSubInstrument.branch_ret_of_ne
      (fun leaf : Σ M, (adversary ρ).State M ↦ leaf.1 × (parallelOracleRuntime H).D)
      (i := ⟨QReg.of Unit, rfl, H address⟩) (j := ⟨QReg.of Unit, rfl, word⟩)
      (by intro he; exact h (congrArg (fun leaf ↦ leaf.2.2) he))).symm

private theorem run_recovery (ρ : SubState Unit) (H : ByteArray.Bounded 83 → Bytes 32)
    (P : LeanSeal.Puzzle 1 1) :
    (parallelOracleRuntime H).run .instruments (windowRecoveryProgram (adversary ρ) P) =
      DSubInstrument.ret (fun leaf : Σ _B : QReg, Bytes 32 ↦
        leaf.1 × (parallelOracleRuntime H).D) ⟨QReg.of Unit, H address⟩ := by
  rw [windowRecoveryProgram, QuantumRuntime.run_bind, run_preprocess,
    DSubInstrument.ret_bind]
  simp [adversary, QuantumRuntime.run_pure]

/-- The fixed-oracle event reads the retained answer and preserves missing input mass. -/
theorem recovery_retained_answer (ρ : SubState Unit) (H : ByteArray.Bounded 83 → Bytes 32)
    (P : LeanSeal.Puzzle 1 1) (key : Bytes 32) :
    windowRecoveryAt (adversary ρ) H P key = if H address = key then ρ.mass else 0 := by
  rw [windowRecoveryAt,
    QuantumRuntime.evalDistMap_apply _ _ _ _ _ (MeasurableSet.singleton True),
    tsum_eq_single ⟨QReg.of Unit, H address⟩]
  · simp only [QuantumRuntime.matrix_jointPost]
    change ENNReal.ofReal (((parallelOracleRuntime H).run .instruments
      (windowRecoveryProgram (adversary ρ) P)).branch ⟨QReg.of Unit, H address⟩
      (ρ.prod (SubState.basis ())).matrix).trace.re * _ = _
    rw [run_recovery, DSubInstrument.branch_ret_self]
    change ENNReal.ofReal (ρ.prod (SubState.basis ())).matrix.trace.re *
      ({True} : Set Prop).indicator 1 (H address = key) = _
    rw [SubState.trace_re_prod, SubState.trace_basis]
    by_cases h : H address = key <;> simp [h, SubState.mass]
  · intro leaf hleaf
    simp only [QuantumRuntime.matrix_jointPost]
    change ENNReal.ofReal (((parallelOracleRuntime H).run .instruments
      (windowRecoveryProgram (adversary ρ) P)).branch leaf
      (ρ.prod (SubState.basis ())).matrix).trace.re * _ = 0
    rw [run_recovery, DSubInstrument.branch_ret_of_ne _ hleaf]
    change ENNReal.ofReal (0 : Matrix (leaf.1 × Unit) (leaf.1 × Unit) ℂ).trace.re * _ = 0
    simp

private theorem inputs_injective (W : PathValue 1 0 → Bytes 32) :
    Function.Injective (fun v ↦ rawPathInput (by decide : 1 ≤ 32)
      (by decide : hashInputBound 1 ≤ 83) (n := 1) 0 0 Fin.elim0 v W) := by
  intro v w h
  have ht := hashInput_injective (b := 1) (n := 1) (by decide)
    (congrArg ByteArray.Bounded.toByteArray h)
  clear h
  fin_cases v <;> fin_cases w <;> simp_all [PathValue.equivSum, pathInput]

/-- The actual preprocessing phase uses the programmed oracle, not the unpatched base table.
Equal node responses are harmless here because the four encoded inputs remain distinct. -/
example :
    let W := fun _ : PathValue 1 0 ↦ PointerChainProgramming.taggedWord
    let H := programPath (by decide : 1 ≤ 32) (by decide : hashInputBound 1 ≤ 83)
      0 0 Fin.elim0 (fun _ ↦ 0) W
    let P := labelPuzzle 0 0 Fin.elim0 (pathLabels (by decide : 1 ≤ 32) W)
    windowRecoveryAt (adversary (SubState.basis ())) H P (W .key) = 1 ∧
      windowRecoveryAt (adversary (SubState.basis ())) (fun _ ↦ 0) P (W .key) = 0 := by
  dsimp only
  have hread := programPath_apply_of_injective (by decide : 1 ≤ 32)
    (by decide : hashInputBound 1 ≤ 83) 0 0 Fin.elim0 (fun _ ↦ 0)
    (fun _ : PathValue 1 0 ↦ PointerChainProgramming.taggedWord)
    (inputs_injective _) PathValue.firstStart
  change programPath (n := 1) (m := 0) (by decide : 1 ≤ 32)
    (by decide : hashInputBound 1 ≤ 83)
    0 0 Fin.elim0 (fun _ ↦ 0) (fun _ ↦ PointerChainProgramming.taggedWord) address =
      PointerChainProgramming.taggedWord at hread
  have hn : (0 : Bytes 32) ≠ PointerChainProgramming.taggedWord := by
    intro h
    have he := congrArg (fun w : Bytes 32 ↦ w.toVector[31]) h
    norm_num [PointerChainProgramming.taggedWord] at he
  constructor
  · rw [recovery_retained_answer, hread, ite_eq_left rfl]
    simp [SubState.mass]
  · rw [recovery_retained_answer, ite_eq_right hn]

end VCVioTest.PointerChainCoupling
