/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.BoundEval

/-!
# Exact security-bound table

The CSV reports exact numerator/denominator pairs from the proved rational evaluators.
The displayed bit coefficients are floating-point presentation only; the rational columns
are suitable for independent exact comparison and certification.
-/

public section

open SLHDSA SLHDSA.Security

namespace SLHDSA.BoundEvalTest

/-- Logarithm of a positive natural, using its leading bits to avoid floating-point overflow. -/
def logNat (n : Nat) : Float :=
  let shift := n.log2 - 52
  (n >>> shift).toFloat.log / (2 : Float).log + shift.toFloat

/-- Bit coefficient of an exact positive rational. -/
def bits (q : ℚ≥0) : Float := logNat q.den - logNat q.num

def main : IO Unit := do
  let q : Nat := 2 ^ 64
  IO.println "parameters,model,qh,qs,numerator,denominator,bits"
  for (name, set) in [
      ("128s", FipsParameterSet.SLHDSA_SHAKE_128s), ("128f", .SLHDSA_SHAKE_128f),
      ("192s", .SLHDSA_SHAKE_192s), ("192f", .SLHDSA_SHAKE_192f),
      ("256s", .SLHDSA_SHAKE_256s), ("256f", .SLHDSA_SHAKE_256f)] do
    let p := set.validatedParams.params
    let values := [
      ("three-oracle", securityBoundEval p (256 ^ p.n) 2 1 q q),
      ("single-SHAKE-deterministic", averagedByteBoundEval p q q),
      ("single-SHAKE-hedged", averagedByteBoundHedgedEval p q q)]
    for (model, bound) in values do
      let coefficient := bound / q
      IO.println s!"{name},{model},{q},{q},{coefficient.num},{coefficient.den},{bits coefficient}"

end SLHDSA.BoundEvalTest

def main : IO Unit := SLHDSA.BoundEvalTest.main
