/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle.Hiding
public import VCVio.Schemes.PointerChainPuzzle.LeanSealEnvelope
public import VCVioTest.PointerChainPuzzle.LeanSeal
import Lean.Data.Json.Parser

/-!
# leanSeal envelope known answers

Compile-time checks that the byte-level envelope is the `dem` argument of the hiding game for the
byte-level puzzle, and known-answer tests over leanSeal's test vectors, vendored unchanged in
`VCVioTest/PointerChainPuzzle/LeanSealVectors/`. For every valid case, sealing the case's message
under its puzzle bytes, key and nonce with `sealBytes sha256` gives the case's envelope byte for
byte, and opening that envelope gives the message back; opening it under another case's puzzle
bytes is rejected. Every invalid entry of kind `envelope` is rejected when opened under the puzzle
bytes and key of the case it names. Run `lake exe algorithm_tests`.
-/

public section

open OracleSpec PointerChainPuzzle.LeanSeal VCVioTest.LeanSeal

namespace VCVioTest.LeanSealEnvelope

/-! ## The envelope in the hiding game -/

example (b n m : ℕ) [NeZero n] (adv : TimeLockPuzzle.HidingAdversary byteSpec (Puzzle b n)
    Envelope.Plaintext ByteArray) (bit : Bool) :
    OracleComp (unifSpec + byteSpec) Bool :=
  (byteScheme b n m).hidingExperiment (byteEnvelope b n m) (fun msg => msg.1.size) adv bit

noncomputable example (b n m : ℕ) [NeZero n]
    (adv : TimeLockPuzzle.HidingAdversary byteSpec (Puzzle b n) Envelope.Plaintext ByteArray) :
    ENNReal :=
  (byteScheme b n m).hidingAdvantage (byteEnvelope b n m) (fun msg => msg.1.size) adv

example (b n m : ℕ) (cache : byteSpec.QueryCache) :
    (byteEnvelope b n m).PerfectlyCorrect (ProbCompRuntime.rom byteSpec cache) :=
  byteEnvelope_perfectlyCorrect_rom m cache

/-! ## Known answers -/

/-- The message written in hexadecimal by `hex`, if it is within the length bound. -/
def plaintextOfHex (hex : String) : Except String Envelope.Plaintext :=
  let a := parseHex hex
  if h : a.size ≤ Envelope.maxLength ∧ hex.length = 2 * a.size then .ok ⟨a, h.1⟩
  else .error s!"not a message: {hex}"

/-- The puzzle bytes and key of a valid case. -/
def puzzleAndKey (case : Lean.Json) : Except String (ByteArray × Bytes 32) := do
  return (parseHex (← strField case "puzzle"), ← bytesOfHex 32 (← strField case "key"))

/-- Check the envelope of one valid case: sealing its message under its puzzle bytes, key and
nonce gives its envelope, opening the envelope gives the message, and opening it under the
puzzle bytes `otherPuzzle` of another case is rejected. -/
def checkCase (index : ℕ) (case : Lean.Json) (otherPuzzle : ByteArray) : Except String Unit := do
  let label := s!"case {index}"
  let (pz, key) ← puzzleAndKey case
  let nonce ← bytesOfHex 16 (← strField case "nonce")
  let msg ← plaintextOfHex (← strField case "message")
  let env := parseHex (← strField case "envelope")
  check s!"{label}: envelope" (sealBytes sha256 pz key nonce msg == env)
  check s!"{label}: opened message" <| match openBytes sha256 pz key env with
    | some msg' => msg'.1 == msg.1
    | none => false
  check s!"{label}: opened under another puzzle" (openBytes sha256 otherPuzzle key env).isNone

/-- Check that an invalid entry of kind `envelope` is rejected under the puzzle bytes and key of
the case it names. Returns whether the entry is of kind `envelope`; entries of other kinds are
skipped. -/
def checkInvalid (cases : Array Lean.Json) (entry : Lean.Json) : Except String Bool := do
  if (← strField entry "kind") != "envelope" then return false
  let why ← strField entry "why"
  let index ← natField entry "case"
  let some case := cases[index]? | throw s!"invalid envelope names case {index}: {why}"
  let (pz, key) ← puzzleAndKey case
  let env := parseHex (← strField entry "hex")
  check s!"invalid envelope accepted: {why}" (openBytes sha256 pz key env).isNone
  return true

/-- Check the envelope of every valid case and every invalid envelope; return their numbers. -/
def checkVectors (root : Lean.Json) : Except String (ℕ × ℕ) := do
  check "vectors for leanseal v1" ((← strField root "spec") == "leanseal v1")
  let cases ← (← root.getObjVal? "cases").getArr?
  check "at least two cases" (2 ≤ cases.size)
  for h : index in [0:cases.size] do
    let (otherPuzzle, _) ← puzzleAndKey cases[(index + 1) % cases.size]!
    checkCase index cases[index] otherPuzzle
  let mut invalid := 0
  for entry in ← (← root.getObjVal? "invalid").getArr? do
    if ← checkInvalid cases entry then invalid := invalid + 1
  check s!"19 invalid envelopes, found {invalid}" (invalid = 19)
  return (cases.size, invalid)

/-- Run the leanSeal envelope known-answer tests over the vendored vectors. -/
def run : IO Unit := do
  let source ← IO.FS.readFile "VCVioTest/PointerChainPuzzle/LeanSealVectors/vectors.json"
  unless matchesHex (sha256 source.toUTF8)
      "9eeb2366433d15af094a773951fa28c9925e7fe9841c29709930c5d5a24e357b" do
    throw (IO.userError "leanSeal vectors differ from the pinned copy")
  let root ← match Lean.Json.parse source with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"leanSeal vectors JSON rejected: {error}")
  match checkVectors root with
  | .ok (cases, invalid) =>
      IO.println
        s!"leanSeal envelope known-answer tests: PASS ({cases} cases, {invalid} invalid envelopes)"
  | .error error => throw (IO.userError s!"leanSeal envelope check failed: {error}")

end VCVioTest.LeanSealEnvelope
