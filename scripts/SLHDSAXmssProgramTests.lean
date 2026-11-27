/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import HashSigTest.SLHDSA.Refactor.XmssProgram

/-! # Executable checks for paper XMSS traversal, recovery and authentication -/

/-- Execute actual paper XMSS checks or a selected assertion-failure control. -/
public def main (args : List String) : IO Unit :=
  match args with
  | [] => SLHDSA.SHAKE128s.XmssProgramTest.runTests
  | ["--control", name] => SLHDSA.SHAKE128s.XmssProgramTest.runControl name
  | _ => throw (IO.userError "usage: slhdsa_xmss_program_tests [--control NAME]")
