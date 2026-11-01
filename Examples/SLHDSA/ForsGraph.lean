/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ForsGraphSampling

/-!
# Programming and sampling canonical FORS schedules

Deterministic programming preserves the full cache without widths or freshness assumptions.
Sampling requires address widths and freshness for the actual cache; the approved empty-cache
clients discharge them through production laws. Full m-byte answers remain in the cache while
cells use their n-byte prefixes. These equalities make no additional prefix-uniformity claim.
-/

public section

open OracleComp OracleSpec RandomOracleTraversal
open SLHDSA SLHDSA.Graph SLHDSA.Security

namespace SLHDSA.Examples.ForsGraph

local notation "vp128" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "vp192" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams

/-- Canonical 128s dependencies supply read-before-write; every unscheduled cell is retained. -/
theorem program128s (pk : Bytes (vp128).params.n) (key : ForsKey (vp128).params)
    (md : List Byte) (initial : Node (vp128).params → Bytes (vp128).params.n)
    (outputs : StructuralNode (vp128).params → Bytes (vp128).params.m)
    (cache : QueryCache (List Byte →ₒ Bytes (vp128).params.m)) :
    let nodes := ForsSchedule.signing key md
    let target := GraphProgramming.tableTarget vp128 nodes initial outputs
    RandomOracleTraversal.program (GraphInput.input vp128 pk)
      (fun parent cells answer => updateCell parent cells (prefixBytes (vp128).params.n answer))
      outputs nodes initial cache =
      (target, Programming.cacheFrom
        (fun parent => GraphInput.input vp128 pk parent target) outputs nodes cache) :=
  GraphProgramming.signing_program vp128 pk key md initial outputs cache

/-- A 192f warm-cache client supplies precisely the widths and local freshness it needs. -/
theorem sample192f_from (widths : Widths (vp192).params)
    (pk : Bytes (vp192).params.n) (key : ForsKey (vp192).params) (md : List Byte)
    (initial : Node (vp192).params → Bytes (vp192).params.n)
    (cache : QueryCache (shakeSpec vp192))
    (fresh : FreshFor (GraphInput.input vp192 pk) (ForsSchedule.signing key md) cache) :
    let nodes := ForsSchedule.signing key md
    (simulateQ randomOracle
      (evaluate (GraphInput.input vp192 pk)
        (fun parent cells (answer : Bytes (vp192).params.m) =>
          updateCell parent cells (prefixBytes (vp192).params.n answer))
        nodes initial)).run cache =ᵈ
      ((fun outputs =>
        let target := GraphProgramming.tableTarget vp192 nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp192 pk parent target) outputs nodes cache)) <$>
        ForsGraphSampling.uniformAnswers vp192) :=
  ForsGraphSampling.signing_from vp192 widths pk key md initial cache fresh

/-- The approved 128s schedule discharges widths, duplicate freedom and empty-cache freshness. -/
theorem sample128s_empty (pk : Bytes (vp128).params.n) (key : ForsKey (vp128).params)
    (md : List Byte) (initial : Node (vp128).params → Bytes (vp128).params.n) :
    let nodes := ForsSchedule.signing key md
    (simulateQ randomOracle
      (evaluate (GraphInput.input vp128 pk)
        (fun parent cells (answer : Bytes (vp128).params.m) =>
          updateCell parent cells (prefixBytes (vp128).params.n answer)) nodes initial)).run ∅ =ᵈ
      ((fun outputs =>
        let target := GraphProgramming.tableTarget vp128 nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp128 pk parent target) outputs nodes ∅)) <$>
        ForsGraphSampling.uniformAnswers vp128) :=
  ForsGraphSampling.shake128s pk key md initial

/-- The approved 192f client retains its own full answer length and concrete schedule. -/
theorem sample192f_empty (pk : Bytes (vp192).params.n) (key : ForsKey (vp192).params)
    (md : List Byte) (initial : Node (vp192).params → Bytes (vp192).params.n) :
    let nodes := ForsSchedule.signing key md
    (simulateQ randomOracle
      (evaluate (GraphInput.input vp192 pk)
        (fun parent cells (answer : Bytes (vp192).params.m) =>
          updateCell parent cells (prefixBytes (vp192).params.n answer)) nodes initial)).run ∅ =ᵈ
      ((fun outputs =>
        let target := GraphProgramming.tableTarget vp192 nodes initial outputs
        (target, Programming.cacheFrom
          (fun parent => GraphInput.input vp192 pk parent target) outputs nodes ∅)) <$>
        ForsGraphSampling.uniformAnswers vp192) :=
  ForsGraphSampling.shake192f pk key md initial

end SLHDSA.Examples.ForsGraph
