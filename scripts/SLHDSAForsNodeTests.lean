/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
import HashSigTest.SLHDSA.Refactor.ForsNode

/-! # Executable checks for paper FORS traversal, recovery and authentication -/

/-- Execute actual paper FORS checks or an explicitly selected assertion-failure control. -/
public def main (args : List String) : IO Unit :=
  match args with
  | [] => SLHDSA.SHAKE128s.ForsNodeTest.runTests
  | ["--control", name] => SLHDSA.SHAKE128s.ForsNodeTest.runControl name
  | _ => throw (IO.userError "usage: slhdsa_fors_node_tests [--control NAME]")
