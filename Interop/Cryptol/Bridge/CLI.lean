/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Bridge.Specifications
import Interop.Cryptol.Bridge.ByteCompression
import Interop.Cryptol.Bridge.SourceFoundation
import Interop.Cryptol.Translation.Export
import Interop.Cryptol.Model.Inspect
import Interop.Cryptol.Bridge.HashCLI
public import Lean.Data.Json

/-!
# Foundation bridge executable checks

The CLI emits finite descriptions and compares native functions with bounded
core execution. Compression accepts arbitrary eight-word states and a valid
64-byte window at any offset, including unaligned offsets.
-/

open Interop.Cryptol Interop.Cryptol.Bridge Lean

namespace Interop.Cryptol.Bridge.CLI

/-- Execute a word observation while retaining a finite cutoff as a distinct result. -/
public def sampleReport (input : Nat) : Json := Id.run do
  let x := input.toUInt32
  let term := Expr.wordToInteger (.app Foundation.sigma256Zero.lower (.word x.toBitVec))
  let (steps, result) := MachineState.runCounted 1000000 (.eval term .done)
  let machine : Json := match result with
    | .inr _ => .mkObj [("status", .str "cutoff")]
    | .inl (.error _) => .mkObj [("status", .str "error")]
    | .inl (.ok (.integer i)) => .mkObj [("status", .str "value"), ("value", toJson i)]
  return .mkObj [("input", toJson x.toNat), ("source", toJson (foundationSigma x).toNat),
    ("vcvio", toJson (VCVio.Algorithms.Sha2.bsig0 x).toNat), ("machine", machine),
    ("steps", toJson steps), ("nodes", toJson term.nodeCount)]

/-- Emit descriptions or run reproducible bridge comparisons. -/
public def run (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match args with
  | ["hash", algorithm, bytes, length] => HashCLI.run algorithm bytes length
  | ["emit-compression-source"] =>
      out.putStr (Export.moduleText Foundation.compressionSource); return 0
  | ["emit-compression"] =>
      out.putStr (Export.moduleText compressionTerm.source); return 0
  | ["compression-sizes"] =>
      out.putStrLn (toJson ((#[0, 16, 32, 64] : Array Nat).map fun n => Json.mkObj
        [("length", toJson n), ("scheduleNodes", toJson (Resolved.nodeCount
          (Finite.Term.prefixTable scheduleStepTerm n).source)),
          ("roundNodes", toJson (Resolved.nodeCount (compressionRoundsTerm n).source))])).compress
      return 0
  | ["compress", offset, stateText, bytesText] =>
      let parsed : Except String (Nat × Array Nat × Array Nat) := do
        let base ← match offset.toNat? with
          | some n => pure n
          | none => throw "Expected a nonnegative offset"
        let state ← (Json.parse stateText).bind (fromJson? (α := Array Nat))
        let bytes ← (Json.parse bytesText).bind (fromJson? (α := Array Nat))
        if state.size != 8 || state.any (· ≥ 2^32) then
          throw "Expected eight unsigned 32-bit state words"
        if base + 64 > bytes.size || bytes.any (· ≥ 256) then
          throw "Expected a valid 64-byte window and byte values below 256"
        pure (base, state, bytes)
      match parsed with
      | .error message => err.putStrLn message; return 1
      | .ok (base, state, bytes) =>
          let st := state.map Nat.toUInt32
          let m := ByteArray.mk (bytes.map Nat.toUInt8)
          let input := (stateBits (arrayState st), loadedBlock m base)
          let start ← IO.monoMsNow
          let run := compressionTerm.denote Finite.Env.empty input
          let compiled := Array.ofFn fun i => (run i).toNat
          let elapsed ← IO.monoMsNow
          let result := VCVio.Algorithms.Sha2.compress st m base
          out.putStrLn (Json.mkObj [("compiled", toJson compiled),
            ("vcvio", toJson (result.map UInt32.toNat)),
            ("compiledMilliseconds", toJson (elapsed - start)),
            ("sourceNodes", toJson (Resolved.nodeCount Foundation.compressionSource)),
            ("compiledNodes", toJson (Resolved.nodeCount compressionTerm.source))]).compress
          return 0
  | ["emit-round"] => out.putStr (Export.moduleText Foundation.round256.source); return 0
  | "round" :: inputs =>
      match inputs.mapM String.toNat? with
      | some [a, b, c, d, e, f, g, h, kt, wt] =>
          let s : VCVio.Algorithms.Sha2.RoundState :=
            ⟨a.toUInt32, b.toUInt32, c.toUInt32, d.toUInt32, e.toUInt32,
              f.toUInt32, g.toUInt32, h.toUInt32⟩
          let input := (stateBits s, kt.toUInt32.toBitVec, wt.toUInt32.toBitVec)
          let source := Foundation.round256.denote Finite.Env.empty input
          let target := nativeRound input
          out.putStrLn (Json.mkObj [("source", toJson (Array.ofFn fun i => (source i).toNat)),
            ("vcvio", toJson (Array.ofFn fun i => (target i).toNat)),
            ("nodes", toJson (Resolved.nodeCount Foundation.round256.source))]).compress
          return 0
      | _ => err.putStrLn "Expected eight registers, kt and wt"; return 1
  | ["sample-all", x, y, z] =>
      match x.toNat?, y.toNat?, z.toNat? with
      | some x, some y, some z =>
          let x := x.toUInt32
          let y := y.toUInt32
          let z := z.toUInt32
          let source := #[Foundation.sigma256Zero.denote Finite.Env.empty x.toBitVec,
            Foundation.sigma256One.denote Finite.Env.empty x.toBitVec,
            Foundation.smallSigma256Zero.denote Finite.Env.empty x.toBitVec,
            Foundation.smallSigma256One.denote Finite.Env.empty x.toBitVec,
            Foundation.choose256.denote Finite.Env.empty (x.toBitVec, y.toBitVec, z.toBitVec),
            Foundation.majority256.denote Finite.Env.empty (x.toBitVec, y.toBitVec, z.toBitVec)]
          out.putStrLn (Json.mkObj [("source", toJson (source.map BitVec.toNat)),
            ("vcvio", toJson (#[VCVio.Algorithms.Sha2.bsig0 x, VCVio.Algorithms.Sha2.bsig1 x,
              VCVio.Algorithms.Sha2.ssig0 x, VCVio.Algorithms.Sha2.ssig1 x,
              VCVio.Algorithms.Sha2.ch x y z, VCVio.Algorithms.Sha2.maj x y z].map UInt32.toNat))
            ]).compress
          return 0
      | _, _, _ => err.putStrLn "Expected three natural word inputs"; return 1
  | ["emit-sigma"] => out.putStr (Export.moduleText Foundation.sigma256Zero.source); return 0
  | ["emit-property"] => out.putStr (Export.moduleText linearity.source); return 0
  | ["sample", input] =>
      match input.toNat? with
      | some x => out.putStrLn (sampleReport x).compress; return 0
      | none => err.putStrLn "Expected a natural input"; return 1
  | ["compress"] =>
      let block := ByteArray.mk (Array.replicate 64 0)
      let result := VCVio.Algorithms.Sha2.compress VCVio.Algorithms.Sha2.iv block 0
      out.putStrLn (toJson (result.map UInt32.toNat)).compress
      return 0
  | _ =>
      err.putStrLn "Usage: cryptol-interop foundation {emit-compression[-source] | \
        compress BASE STATE_JSON BYTES_JSON | …}"
      return 1

end Interop.Cryptol.Bridge.CLI
