/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import HashSigTest.SLHDSA.Refactor.HypertreeIntegration

/-! # Executable effectful hypertree entry-policy checks -/

/-- Execute shared hypertree-loop checks or one selected assertion-failure control. -/
public def main (args : List String) : IO Unit :=
  match args with
  | [] => SLHDSA.Refactor.HypertreeIntegration.runTests
  | ["--control", name] => SLHDSA.Refactor.HypertreeIntegration.runControl name
  | _ => throw (IO.userError "usage: slhdsa_hypertree_program_tests [--control NAME]")
