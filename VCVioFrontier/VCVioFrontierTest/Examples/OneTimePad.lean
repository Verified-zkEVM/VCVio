/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import VCVioFrontier.Examples.OneTimePad.Machine

/-!
# One program with supplied or fair key bits

`encryptWord` asks for one Boolean response per message bit. Install a tape to compute one
ciphertext, then install fair coins to interpret the same requests probabilistically.
-/

open VCVioFrontier VCVioFrontier.OneTimePad

example : (simulateQ tapeBits (encryptWord [false, true, false])).run
    [true, false, false, true] = some ([true, true, false], [true]) := rfl

-- The tape contains one key bit per message bit, followed by an arbitrary suffix.
example {n : ℕ} (key msg : BitVec n) (suffix : List Bool) :
    (simulateQ tapeBits (encryptWord (word msg))).run (word key ++ suffix) =
      some (word (key ^^^ msg), suffix) :=
  encryptWord_tapeBits key msg suffix

-- The machine’s output has the law of that same tree with fair answers at every request.
example (msg : List Bool) : encryptMachine.output msg =
    Cslib.ProbComp.eval (simulateQ fairBits (encryptWord msg)) :=
  WordMachine.agrees encryptMachine msg

example {n : ℕ} (m₀ m₁ : BitVec n) :
    encryptMachine.output (word m₀) = encryptMachine.output (word m₁) :=
  encryptMachine_rows m₀ m₁

example : (simulateQ tapeBits (encryptWord [false, true])).run [true] = none := rfl

example : word (1 : BitVec 3) = [true, false, false] := by decide

example : roundTripMachine.output [] = PMF.pure [] := by
  simpa [word] using roundTripMachine_correct (0 : BitVec 0)

example : encryptMachine.output [false] = encryptMachine.output [true] := by
  exact encryptMachine_rows (0 : BitVec 1) (1 : BitVec 1)

example : xorMachine.output ([true, false, false], [false, true, false]) =
    PMF.pure [true, true, false] :=
  xorMachine_exact (1 : BitVec 3) (2 : BitVec 3)

example : xorMachine.output ([true, false, false], [true, true, false]) =
    PMF.pure [false, true, false] :=
  xorMachine_decrypt (1 : BitVec 3) (2 : BitVec 3)
