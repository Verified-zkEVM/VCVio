/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioTest.InnerProduct.Comparison
public import Examples.InnerProduct.Interaction
public import Mathlib.Algebra.Field.ZMod

/-!
# Executable checks for folding, replay, and retained work

Small prime fields exercise nonzero challenges and concrete folding equations.
Concrete checks execute the definitions; representation comparisons use proved equations.
-/

public section

namespace InnerProduct.Checks

abbrev F := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def challenge : Fˣ := Units.mk0 (2 : F) (by decide)

def nontrivialStatement : Statement F F 1 where
  g i := if i.1 then (if (i.2 : Fin 2).val = 0 then 3 else 4)
    else (if (i.2 : Fin 2).val = 0 then 1 else 2)
  h i := if i.1 then (if (i.2 : Fin 2).val = 0 then 4 else 5)
    else (if (i.2 : Fin 2).val = 0 then 2 else 3)
  A := 2
  B := 0
  z := 4

def nontrivialMessage : FoldMessage F F := ⟨4, 4, 0, 4, 1, 0⟩

def foldedWitness : Witness F 0 where
  a i := if (i : Fin 2).val = 0 then 0 else 6
  b i := if (i : Fin 2).val = 0 then 3 else 1



def zeroWitness (r : Nat) : Witness F r := ⟨fun _ => 0, fun _ => 0⟩

def zeroMessage : FoldMessage F F := ⟨0, 0, 0, 0, 0, 0⟩

def zeroStatement (r : Nat) : Statement F F r := ⟨fun _ => 1, fun _ => 1, 0, 0, 0⟩

def zeroProver : (r : Nat) → Prover F F r
  | 0 => zeroWitness 0
  | r + 1 => (zeroMessage, fun _ => zeroProver r)


def countedChallenge : StateT Nat Id Fˣ := fun used => (challenge, used + 1)

def rejectStatement : Statement F F 2 := { zeroStatement 2 with z := 1 }

def checkedAttempt : StateT Nat Id Bool :=
  simulateQ (fun _ => countedChallenge) (source (zeroProver 2) (accepts rejectStatement))

/-- A finite consumer whose work ledger is outside its rejected attempts. -/
def attempts : Nat → StateT Nat Id (Option Nat)
  | 0 => pure none
  | remaining + 1 => do
      let ok ← checkedAttempt
      if ok then return some remaining else attempts remaining


example : simulateQ (fun _ => countedChallenge) (source (zeroProver 3) (fun _ => ())) =
    PlainReplay.run (fun _ => countedChallenge) (Plain.source (zeroProver 3) (fun _ => ())) :=
  Comparison.run_eq _ _ _

example (p : Prover F F 2) (first : Fin 3 → Fˣ) (second : Fin 3 → Fin 3 → Fˣ)
    (i j : Fin 3) :
    PFunctor.FreeM.output (source p id) (replay33Leaf p first second i j).path =
      PlainReplay.output (Plain.source p id) (Plain.replay33Leaf p first second i j).path :=
  Comparison.replay33_output_eq _ _ _ _ _

/-- Run the concrete folding and retained-work regression checks. -/
def run : IO Unit := do
  unless ((fold nontrivialStatement nontrivialMessage challenge).A == 5) do
    throw (IO.userError "inner-product replay check 1 failed")
  unless ((fold nontrivialStatement nontrivialMessage challenge).B == 2) do
    throw (IO.userError "inner-product replay check 2 failed")
  unless ((fold nontrivialStatement nontrivialMessage challenge).z == 6) do
    throw (IO.userError "inner-product replay check 3 failed")
  unless (accepts (fold nontrivialStatement nontrivialMessage challenge)
    (.terminal foldedWitness) == true) do
    throw (IO.userError "inner-product replay check 4 failed")
  unless (accepts (zeroStatement 0) (respond (zeroProver 0) ()) == true) do
    throw (IO.userError "inner-product replay check 5 failed")
  unless (accepts (zeroStatement 1) (respond (zeroProver 1) (challenge, ())) == true) do
    throw (IO.userError "inner-product replay check 6 failed")
  unless (accepts (zeroStatement 2)
    (respond (zeroProver 2) (challenge, challenge, ())) == true) do
    throw (IO.userError "inner-product replay check 7 failed")
  unless (accepts (zeroStatement 3)
    (respond (zeroProver 3) (challenge, challenge, challenge, ())) == true) do
    throw (IO.userError "inner-product replay check 8 failed")
  unless ((Id.run (checkedAttempt.run 10)) == (false, 12)) do
    throw (IO.userError "inner-product replay check 9 failed")
  unless ((Id.run ((attempts 0).run 10)) == (none, 10)) do
    throw (IO.userError "inner-product replay check 10 failed")
  unless ((Id.run ((attempts 1).run 10)) == (none, 12)) do
    throw (IO.userError "inner-product replay check 11 failed")
  unless ((Id.run ((attempts 3).run 10)) == (none, 16)) do
    throw (IO.userError "inner-product replay check 12 failed")
  IO.println "Inner-product folding and replay checks passed"

end InnerProduct.Checks
