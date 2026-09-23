/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioComplexity.Backend.Copy
public import VCVioComplexityTest.Backend.PureCanary
public import PolyFun.PFunctor.Free.HandlerMachine

/-!
# Variable-input handler execution with exact tape costs

An inhabited word interface is implemented by one uniform echo handler. Executing its caller
requires two administrative transitions even though the handler has no inner queries. The
returned optional word is realized by exact tape machines which copy every input bit and write
both the optional-value tag and the final readout tag. Total work is `2 * n + 7` for input length
`n`; state and readout sizes grow as `n + 1` and `n + 2`.

This checks semantic handler execution against a concrete realization on arbitrary-length
inputs. The exact realization specializes this echo program; it is not a general compiler from
the syntax-level dispatcher to this machine backend.
-/

public section

namespace VCVioComplexity.Backend.TuringMachine.HandlerCanary

open PFunctor PFunctor.DynSystem PFunctor.FreeM.HandlerMachine
open PFunctor.DynSystem.DynComputation OracleComp.Complexity _root_.Complexity

local instance : stepClass.HasProd := hasProd
local instance : stepClass.HasSum := hasSum
local instance : stepClass.HasOption := hasOption

/-- An inhabited interface with arbitrary-length queries and replies. -/
@[expose] def wordInterface : PFunctor.{0, 0} := ⟨Word, fun _ => Word⟩

/-- One uniform handler echoes every query position. -/
@[expose] def echo (word : wordInterface.A) : FreeM noQuery (wordInterface.B word) :=
  .pure word

/-- Execute one caller query with both dispatch transitions charged. -/
@[expose] def program (word : Word) : FreeM noQuery (Option Word) :=
  (fun out => result out.phase) <$>
    runPrefix echo 2 (.caller (FreeM.lift (P := wordInterface) word))

/-- The caller receives exactly the word it supplied to the handler. -/
theorem program_eq (word : Word) : program word = FreeM.pure (some word) := by
  rfl

/-- Stopping after entry leaves the handler return pending, even for an empty input. -/
theorem one_transition_pending (word : Word) :
    (fun out => result out.phase) <$>
      runPrefix echo 1 (.caller (FreeM.lift (P := wordInterface) word)) =
        FreeM.pure none := by
  rfl

/-- Word input and optional-word output use the trusted structural encodings. -/
@[expose] def boundary : Boundary stepClass noQuery Word (Option Word) where
  input := .word
  out := .option .word
  pos := noQueryPosition
  idx := noQueryIndex

/-- The unreachable update still has exact code on every raw binary input. -/
noncomputable def updateCode : Code (boundary.stateIdx boundary.out)
    (.option boundary.out) (DynComputation.ofFn (p := noQuery) (some : Word → Option Word)).update?
    where
  workTapes := 0
  machine := Primitive.haltMachine
  wordFunction := fun _ => []
  run := Primitive.haltRun
  encode_eq input := input.2.1.elim

/-- All charged operations copy the full input and include their representation tags. -/
noncomputable def certificate : PureCertificate quantitativeStepClass boundary
    (some : Word → Option Word) where
  result := someCopyPolyRealizer .word
  head := inlCopyPolyRealizer (.option .word) noQueryPosition
  outputRecovery :=
    { polynomial := .input
      output_le value := by
        change encodedSize (.option .word) value ≤
          encodedSize (.sum (.option .word) noQueryPosition) (.inl value)
        simp [encodedSize] }
  update := updateCode

/-- A complete backend-relative witness for the actual completed handler execution. -/
noncomputable def witness : StrictPPTWitness quantitativeStepClass boundary
    noQueryContract program := by
  have hprogram : program = fun input => FreeM.pure (some input) := funext program_eq
  rw [hprogram]
  exact certificate.programWitness noQueryContract

/-- The inhabited, variable-input handler canary is strictly polynomial in encoded input size. -/
theorem isOraclePPTBy : IsOraclePPTBy quantitativeStepClass boundary noQueryContract program :=
  ⟨witness⟩

/-- The derived resource polynomial charges both complete copying passes. -/
theorem polynomial_eval (length : OracleModulus PEmpty → ℕ → ℕ) (n : ℕ) :
    (PureResourceCertificate.polynomial certificate).eval length n =
      { work := 2 * n + 7, queries := 0, traffic := 0,
        peakStateSize := n + 1, peakHeadSize := n + 2 } := by
  rw [PureResourceCertificate.eval_polynomial]
  apply ExecutionCost.ext <;>
    simp [certificate, someCopyPolyRealizer, inlCopyPolyRealizer]
  omega

end VCVioComplexity.Backend.TuringMachine.HandlerCanary
