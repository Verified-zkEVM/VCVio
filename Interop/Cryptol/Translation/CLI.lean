/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Examples
public import Interop.Cryptol.Translation.Export
public import Interop.Cryptol.Model.WordOps
public import Interop.Cryptol.Model.Inspect
public import Interop.Cryptol.Translation.FiniteSource
import Interop.Cryptol.Translation.NumericCLI
import Lean.Data.Json

/-!
# Cryptol model fixture CLI

`emit NAME` prints a Cryptol module. `run NAME` executes the Lean machine.
`report` emits the complete differential-test corpus as JSON. Cutoff, error,
and value are different JSON states; no cutoff is reported as divergence.
`word OP WIDTH AMOUNT INPUT FUEL` observes a word's outer constructor and bits.
`arx WIDTH DEPTH FUEL` measures repeated add/XOR/rotate descriptions. Fuel is
per observation; counts include repeated evaluation without sharing.
-/

public section

open Interop.Cryptol Interop.Cryptol.Examples
open Lean (toJson)

namespace Interop.Cryptol.CLI

/-- Stable machine-readable error categories. -/
def errorJson : EvalError → Lean.Json
  | .user message => .mkObj [("kind", .str "user"), ("message", .str message)]
  | .invalidIndex index => .mkObj [("kind", .str "invalidIndex"), ("index", toJson index)]
  | .divideByZero => .mkObj [("kind", .str "divideByZero")]

/-- Keep finite execution outcomes distinct in CLI output. -/
def outcomeJson : Option (Except EvalError Int) → Lean.Json
  | none => .mkObj [("status", .str "cutoff")]
  | some (.ok i) => .mkObj [("status", .str "value"), ("value", toJson i)]
  | some (.error e) => .mkObj [("status", .str "error"), ("error", errorJson e)]

/-- Report the finite source description and independently supplied expectation. -/
def report (fixture : Fixture) : Lean.Json := .mkObj [
  ("name", .str fixture.name),
  ("source", .str (Export.moduleText fixture.source)),
  ("fuel", toJson fixture.fuel),
  ("expected", outcomeJson fixture.expected),
  ("actual", outcomeJson (runInteger fixture.fuel fixture.term))]

/-- An outer constructor is distinct from the outcomes of its suspended bits. -/
def outerJson {a : ClosedTy} : Outcome a ⊕ MachineState a → Lean.Json
  | .inr _ => .mkObj [("status", .str "cutoff")]
  | .inl (.error e) => .mkObj [("status", .str "error"), ("error", errorJson e)]
  | .inl (.ok _) => .mkObj [("status", .str "value")]

/-- Observe each bit independently, retaining partial errors and finite cutoffs. -/
def wordReport {n : Nat} (budget : Nat) (source : Resolved.Term [] (wordTy n)) :
    Lean.Json := Id.run do
  let e := Resolved.lower source
  let (outerSteps, outer) := MachineState.runCounted budget (.eval e .done)
  let mut steps := outerSteps
  let mut bits : Array Lean.Json := #[]
  for i in [:n] do
    let (count, result) := MachineState.runCounted budget
      (.eval (.index e (.integer i)) .done)
    steps := steps + count
    bits := bits.push (match result with
      | .inl (.ok (.bit b)) => .mkObj [("status", .str "value"), ("value", toJson b)]
      | other => outerJson other)
  return .mkObj [("outer", outerJson outer), ("bits", .arr bits), ("steps", toJson steps),
    ("nodes", toJson e.nodeCount), ("sourceNodes", toJson (Resolved.nodeCount source)),
    ("source", .str (Export.expression source))]

/-- Native literals stay compact at the source boundary. -/
def compactWord (n value : Nat) : Resolved.Term [] (wordTy n) :=
  .word (BitVec.ofNat n value)

/-- Inputs for demand-sensitive primitive comparisons. Numeric inputs use
compact literal descriptions to bound external elaboration of the matrix. -/
def wordInput (n : Nat) (input : String) : Except String (Resolved.Term [] (wordTy n)) :=
  match input with
  | "error" => .ok (.error (.user "word input"))
  | "diverge" => .ok (.fix (.var .zero))
  | "partial" => .ok (.generate (Length.finite n)
      (.ite (.intEq (.var .zero) (.integer 0)) (.bit true) (.error (.user "partial bit"))))
  | value => match value.toNat? with
      | some value => .ok (compactWord n value)
      | none => .error "Expected a natural number, error, diverge, or partial"

/-- Preserve a native operator head for both lowering and compact export. -/
def wordOperation {n : Nat} (op : String) (amount : Int)
    (e : Resolved.Term [] (wordTy n)) :
    Except String (Resolved.Term [] (wordTy n)) :=
  match op with
  | "identity" => .ok e
  | "left" => .ok (.shift .left e (.integer amount))
  | "right" => .ok (.shift .right e (.integer amount))
  | "rotl" => .ok (.shift .rotateLeft e (.integer amount))
  | "rotr" => .ok (.shift .rotateRight e (.integer amount))
  | "not" => .ok (.app (.primitive (.wordNot n)) e)
  | "xor" => .ok (.wordLogic .xor e (.word (BitVec.ofInt n amount)))
  | "and" => .ok (.wordLogic .and e (.word (BitVec.ofInt n amount)))
  | "or" => .ok (.wordLogic .or e (.word (BitVec.ofInt n amount)))
  | "add" => .ok (.wordArithmetic .add e (.word (BitVec.ofInt n amount)))
  | "sub" => .ok (.wordArithmetic .sub e (.word (BitVec.ofInt n amount)))
  | "mul" => .ok (.wordArithmetic .mul e (.word (BitVec.ofInt n amount)))
  | "neg" => .ok (.wordNeg e)
  | _ => .error "Unknown word operation"

/-- Each stage binds its input once and retains references in the source description. -/
def arx {Γ : List ClosedTy} {n : Nat} : Nat → Resolved.Term Γ (wordTy n) →
    Resolved.Term Γ (wordTy n)
  | 0, x => x
  | depth + 1, x => .letE x (arx depth
      (.wordLogic .xor (.shift .rotateRight
        (.wordArithmetic .add (.var .zero) (.var .zero)) (.integer 7)) (.var .zero)))

/-- A shared total description can execute natively and export the same source structure. -/
def finiteArx {Γ : List Finite.Ty} {n : Nat} : Nat → Finite.Term Γ (.word n) →
    Finite.Term Γ (.word n)
  | 0, x => x
  | depth + 1, x => .letE x (finiteArx depth
      (.wordOp .xor (.rotateRight 7 (.arithmetic .add (.var .zero) (.var .zero))) (.var .zero)))

/-- Measure native execution separately from source construction and core observations. -/
def nativeArxReport (n depth : Nat) : IO Lean.Json := do
  let term : Finite.Term [] (.word n) := finiteArx depth (.word (BitVec.ofNat n 305419896))
  let start ← IO.monoNanosNow
  let value := (term.denote Finite.Env.empty).toNat
  let elapsed ← IO.monoNanosNow
  let source := term.source
  return .mkObj [("native", toJson value), ("nativeNanos", toJson (elapsed - start)),
    ("sourceNodes", toJson (Resolved.nodeCount source)),
    ("source", .str (Export.expression source))]

end Interop.Cryptol.CLI

/-- Run a named fixture or emit the corpus for external comparison. -/
def Interop.Cryptol.CLI.run (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match args with
  | ["numeric"] =>
      out.putStrLn CLI.numericReport.compress
      return 0
  | ["arx-native", width, depth] =>
      match width.toNat?, depth.toNat? with
      | some n, some depth => out.putStrLn (← CLI.nativeArxReport n depth).compress; return 0
      | _, _ => err.putStrLn "Expected natural width and depth"; return 1
  | ["word", op, width, amount, input, fuel] =>
      match width.toNat?, amount.toInt?, fuel.toNat? with
      | some n, some k, some budget =>
          match CLI.wordInput n input >>= CLI.wordOperation op k with
          | .ok term => out.putStrLn (CLI.wordReport budget term).compress; return 0
          | .error message => err.putStrLn message; return 1
      | _, _, _ => err.putStrLn "Expected natural width, amount and budget"; return 1
  | ["arx", width, depth, fuel] =>
      match width.toNat?, depth.toNat?, fuel.toNat? with
      | some n, some depth, some budget =>
          out.putStrLn (CLI.wordReport budget
            (CLI.arx depth (.word (BitVec.ofNat n 305419896)))).compress
          return 0
      | _, _, _ => err.putStrLn "Expected natural width, depth and budget"; return 1
  | ["report"] =>
      out.putStrLn (Lean.Json.arr (fixtures.map CLI.report).toArray).compress
      return 0
  | [command, name] =>
      match fixtures.find? (fun f => f.name == name) with
      | none =>
          err.putStrLn s!"Unknown fixture: {name}"
          return 1
      | some fixture =>
          match command with
          | "emit" => out.putStr (Export.moduleText fixture.source); return 0
          | "run" =>
              out.putStrLn (CLI.outcomeJson (runInteger fixture.fuel fixture.term)).compress
              return 0
          | _ => err.putStrLn "Usage: polyfun-cryptol {emit NAME | run NAME | report | \
              word OP WIDTH AMOUNT INPUT FUEL | arx WIDTH DEPTH FUEL}"; return 1
  | _ =>
      err.putStrLn "Usage: polyfun-cryptol {emit NAME | run NAME | report | \
        word OP WIDTH AMOUNT INPUT FUEL | arx WIDTH DEPTH FUEL}"
      return 1
