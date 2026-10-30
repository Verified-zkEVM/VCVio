/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig

/-!
# Compiler controls through the combined hash-signature library

Direct finite-index elimination checks zero, successor and last indices after importing the
combined library. A 32-entry family built by `sequenceFin` exercises the nested eliminators
while recording callback order and checking every value and their sum.
-/

public section

namespace SLHDSA.SHAKE128s.CompilerTest

/-- Fail the executable when a compiler control returns an unexpected result. -/
def ensure (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"SHAKE-128s compiler check failed: {label}")

/-- Distinct zero and successor branches of the ordinary finite-index eliminator. -/
def dispatch (index : Fin 32) : Nat :=
  Fin.cases (n := 31) (motive := fun _ => Nat) 101 (fun previous => 200 + previous.val) index

/-- Exercise zero, a successor and the largest index through the imported compiler rule. -/
def checkCases : IO Unit := do
  let cases : List (Fin 32 × Nat) := [
    (⟨0, by decide⟩, 101), (⟨1, by decide⟩, 200), (⟨31, by decide⟩, 230)]
  for (index, expected) in cases do
    ensure s!"Fin.cases index {index.val}" (dispatch index == expected)

/-- Record each family entry and give it a position-dependent odd value. -/
def callback (index : Fin 32) : StateM (List Nat) Nat := do
  modify (· ++ [index.val])
  return 2 * index.val + 1

/-- The literal expected chronological callback order. -/
def expectedIndices : List Nat := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

/-- The literal expected values, independent of the family-construction code. -/
def expectedValues : List Nat := [
  1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31,
  33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63]

/-- Construct and consume all 32 entries of the nested head/tail family. -/
def checkSequence : IO Unit := do
  let (family, trace) := (SLHDSA.SHAKE128s.sequenceFin 32 callback).run []
  let values := List.ofFn family
  ensure "32 callbacks in chronological order" (trace == expectedIndices)
  ensure "all 32 values" (values == expectedValues)
  for index in List.finRange 32 do
    ensure s!"family entry {index.val}" (family index == expectedValues.getD index.val 0)
  ensure "literal sum of all entries" (values.sum == 1024)

/-- Execute the direct elimination and nested-family controls. -/
def check : IO Unit := do
  checkCases
  checkSequence
  IO.println "SLH-DSA SHAKE-128s compiler controls: PASS (32 entries; sum 1024)"

end SLHDSA.SHAKE128s.CompilerTest

/-- Run the compiler controls through the combined library import. -/
def main : IO Unit := SLHDSA.SHAKE128s.CompilerTest.check
