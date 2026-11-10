/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSeal
import Lean.Data.Json.Parser

/-!
# leanSeal known answers

Compile-time checks of the leanSeal byte encoding on a tiny instance, and known-answer tests over
leanSeal's test vectors, vendored unchanged in `VCVioTest/PointerChainPuzzle/LeanSealVectors/`.
For every valid case, the byte-level programs over `sha256` reproduce the chain starts, the chain
ends, the accumulators, the key, the commitment and the puzzle bytes, and the chain state and
accumulator at the checkpoint position; decoding the puzzle gives its parameters back, the checked
solver returns the key, and with one commitment byte changed it returns `none`. Every invalid
entry of kind `puzzle` is rejected by the decoder. Run `lake exe algorithm_tests`.
-/

public section

open PointerChainPuzzle.LeanSeal

namespace VCVioTest.LeanSeal

/-! ## A tiny instance -/

/-- A toy byte-answer function: every output byte is the input length. -/
def toyHash (x : ByteArray) : Bytes 32 := ⟨Vector.replicate 32 x.size.toUInt8⟩

example : Valid 24 16 (2 ^ 29) := by decide

example : ¬ Valid 33 1 1 := by decide

example : ¬ Valid 1 4097 (2 ^ 48) := by decide

/-- The context of the largest vendored case, `b = 7`, `n = 8`, `m = 1000`, with a zero salt. -/
example : ctxList 7 8 1000 0 =
    [1, 7, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0x03, 0xe8] ++ List.replicate 16 0 := by
  decide

example (puzzle : Puzzle 1 2) : decode (encode 3 puzzle) = some ⟨1, 2, 3, by decide, puzzle⟩ :=
  decode_encode _ puzzle

example (salt : Bytes 16) (xs : Fin 2 → Bytes 1) :
    solveBytes toyHash (generate toyHash 3 salt xs).1 = some (generate toyHash 3 salt xs).2 :=
  solveBytes_generate toyHash 3 (by decide) salt xs

example (puzzle : Puzzle 1 2)
    (hc : commit toyHash (ctx 1 2 3 puzzle.salt) (derive toyHash 3 puzzle) ≠ puzzle.commitment) :
    solve toyHash 3 puzzle = none := by
  simp [solve, hc]

example (puzzle : Puzzle 1 2) :
    simulateQ (impl toyHash 1 2) (_root_.PointerChainPuzzle.solve 3 (ctx 1 2 3) id puzzle) =
      pure (solveBytes toyHash (encode 3 puzzle)) :=
  simulateQ_solve_eq_solveBytes toyHash 3 (by decide) puzzle

/-! ## Known answers -/

/-- The value of a lowercase hexadecimal digit. -/
def hexDigit (c : Char) : UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then (c.toNat - 'a'.toNat + 10).toUInt8
  else 0

/-- The bytes written in lowercase hexadecimal by `hex`. -/
def parseHex (hex : String) : ByteArray := Id.run do
  let chars := hex.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:chars.size / 2] do
    out := out.push (hexDigit chars[2 * i]! <<< 4 ||| hexDigit chars[2 * i + 1]!)
  return out

/-- Fail with `label` unless `condition` holds. -/
def check (label : String) (condition : Bool) : Except String Unit :=
  unless condition do throw label

/-- Whether `x` has the bytes written in hexadecimal by `hex`. -/
def matchesHex {k : ℕ} (x : Bytes k) (hex : String) : Bool :=
  x.toByteArray == parseHex hex

/-- The `k` bytes written in hexadecimal by `hex`, if it writes exactly `k` bytes. -/
def bytesOfHex (k : ℕ) (hex : String) : Except String (Bytes k) :=
  let a := parseHex hex
  if h : a.data.size = k ∧ hex.length = 2 * k then .ok ⟨⟨a.data, h.1⟩⟩
  else .error s!"not {k} bytes: {hex}"

/-- The natural number field `key` of `j`. -/
def natField (j : Lean.Json) (key : String) : Except String ℕ := do
  (← j.getObjVal? key).getNat?

/-- The string field `key` of `j`. -/
def strField (j : Lean.Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

/-- The string array field `key` of `j`. -/
def strsField (j : Lean.Json) (key : String) : Except String (Array String) := do
  (← (← j.getObjVal? key).getArr?).mapM (·.getStr?)

/-- Check one valid case with parameters `b`, `n`, `m` against the byte-level programs over
`sha256`. -/
def checkCaseWith (label : String) (b n m : ℕ) [NeZero n] (case : Lean.Json) :
    Except String Unit := do
  let salt ← bytesOfHex 16 (← strField case "salt")
  let links ← (← strsField case "x").mapM (bytesOfHex b)
  check s!"{label}: {n} links" (links.size = n)
  let xs : Fin n → Bytes b := fun i => links.getD i default
  let c := ctx b n m salt
  let ys := Vector.ofFn fun i : Fin n => chainAt sha256 c salt i (xs i) m
  let starts ← strsField case "start"
  let ends ← strsField case "y"
  let accsHex ← strsField case "acc"
  check s!"{label}: {n} starts, ends and accumulators"
    (starts.size = n ∧ ends.size = n ∧ accsHex.size = n)
  for i in List.finRange n do
    check s!"{label}: start {i}" (matchesHex (start sha256 c i (xs i)) starts[i]!)
    check s!"{label}: end {i}" (matchesHex ys[i] ends[i]!)
    check s!"{label}: accumulator {i}"
      (matchesHex (accs sha256 c (fun j => ys[j]) (i + 1)) accsHex[i]!)
  let keyHex ← strField case "key"
  let puzzleHex ← strField case "puzzle"
  let generated := genWith sha256 m salt xs
  check s!"{label}: key" (matchesHex generated.2 keyHex)
  check s!"{label}: commitment" (matchesHex generated.1.commitment (← strField case "commit"))
  let puzzleBytes := encode m generated.1
  check s!"{label}: puzzle bytes" (puzzleBytes == parseHex puzzleHex)
  check s!"{label}: decoded parameters" <| match decode puzzleBytes with
    | some d => d.b = b ∧ d.n = n ∧ d.m = m
    | none => false
  check s!"{label}: solved key" <| match solveBytes sha256 (parseHex puzzleHex) with
    | some k => matchesHex k keyHex
    | none => false
  let tampered := puzzleBytes.set! 36 (puzzleBytes.get! 36 ^^^ 1)
  check s!"{label}: changed commitment decodes" (decode tampered).isSome
  check s!"{label}: changed commitment fails the check" (solveBytes sha256 tampered).isNone
  let checkpoint ← case.getObjVal? "checkpoint"
  let i ← natField checkpoint "i"
  let j ← natField checkpoint "j"
  if hi : 1 ≤ i ∧ i ≤ n then
    let chain : Fin n := ⟨i - 1, by omega⟩
    check s!"{label}: checkpoint state"
      (matchesHex (chainAt sha256 c salt chain (xs chain) j) (← strField checkpoint "state"))
    check s!"{label}: checkpoint accumulator"
      (matchesHex (accs sha256 c (fun j => ys[j]) (i - 1)) (← strField checkpoint "acc"))
  else throw s!"{label}: checkpoint chain {i} out of range"

/-- Check one valid case against the byte-level programs over `sha256`. -/
def checkCase (index : ℕ) (case : Lean.Json) : Except String Unit := do
  let label := s!"case {index}"
  let n ← natField case "n"
  if hn : n = 0 then throw s!"{label}: n = 0"
  else
    haveI : NeZero n := ⟨hn⟩
    checkCaseWith label (← natField case "b") n (← natField case "m") case

/-- Check that an invalid entry of kind `puzzle` is rejected by the decoder. Returns whether the
entry is of kind `puzzle`; entries of other kinds are skipped. -/
def checkInvalid (entry : Lean.Json) : Except String Bool := do
  if (← strField entry "kind") != "puzzle" then return false
  let bytes := parseHex (← strField entry "hex")
  check s!"invalid puzzle accepted: {← strField entry "why"}" (decode bytes).isNone
  return true

/-- Check every valid case and every invalid puzzle; return their numbers. -/
def checkVectors (root : Lean.Json) : Except String (ℕ × ℕ) := do
  check "vectors for leanseal v1" ((← strField root "spec") == "leanseal v1")
  let cases ← (← root.getObjVal? "cases").getArr?
  for h : index in [0:cases.size] do
    checkCase index cases[index]
  let mut invalid := 0
  for entry in ← (← root.getObjVal? "invalid").getArr? do
    if ← checkInvalid entry then invalid := invalid + 1
  check s!"16 invalid puzzles, found {invalid}" (invalid = 16)
  return (cases.size, invalid)

/-- Run the leanSeal known-answer tests over the vendored vectors. -/
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
      IO.println s!"leanSeal known-answer tests: PASS ({cases} cases, {invalid} invalid puzzles)"
  | .error error => throw (IO.userError s!"leanSeal check failed: {error}")

end VCVioTest.LeanSeal
